{-# LANGUAGE GADTs, TemplateHaskell, FlexibleContexts #-}
import Call
import Call.Util.Text as Text
import Control.Lens
import Control.Monad.State.Strict
import qualified Data.IntMap as M
import Data.Ord
import Data.List
import System.Random.MWC hiding (create)

consMap :: a -> M.IntMap a -> (Int, M.IntMap a)
consMap x m
  | M.size m == 0 = (0, m & at 0 ?~ x)
  | otherwise = let (i,_) = M.findMax m in (i+1, m & at (i+1) ?~ x)

consMap' :: a -> M.IntMap a -> M.IntMap a
consMap' x m = snd $ consMap x m

data Creature = Plant | Herbivore | Carnivore | Human deriving (Eq, Show)
data Condition = Idle | Hungry | Dead deriving (Eq, Show)

data Alife = Alife {
  -- on canvas
  _pos :: Vec2,
  _arg :: Float,

  -- trait
  _strength :: Int,
  _agility :: Int,
  _creature :: Creature,

  -- state
  _counter :: Int,
  _destination :: Vec2,
  _condition :: Condition,
  _life :: Double
  } deriving (Eq, Show)

data World = World {
  _lives :: M.IntMap Alife,
  _canvas :: [Picture],
  _seed :: Seed
  }

makeLenses ''Alife
makeLenses ''World

-- type Simulator s = Inst (System s) (StateT World (System s)) (System s)
-- type AI s = Inst (System s) (StateT Alife (System s)) (System s)

isInside :: Vec2 -> Bool
isInside (V2 x y) = (0 < x && x < 640) && (0 < y && y < 480)

create :: Creature -> Alife
create Plant     = Alife (V2 320 240) 0  20 20 Plant      1 0 Idle   100
create Herbivore = Alife (V2 320 240) 0  50 50 Herbivore  1 0 Idle    50
create Carnivore = Alife (V2 320 240) 0  50 50 Carnivore  1 0 Idle   100
create Human     = Alife (V2 320 240) 0  25 25 Human      1 0 Idle   100

spawn :: Alife -> StateT World (System s) ()
spawn ai = lives %= consMap' ai

randomVec2 :: (Functor m, MonadIO m) => StateT World m Vec2
randomVec2 = do
  gen <- liftIO . restore =<< use seed
  v <- V2 <$> liftIO (uniformR (0,640) gen) <*> liftIO (uniformR (0,480) gen)
  seed <~ liftIO (save gen)
  return v

evolve :: Int -> StateT World (System s) ()
evolve j = do
  x <- getAI j
  evolve' j (x^.creature)
  zoom (lives . ix j) runAI

  where
  runAI = do
    V2 px py <- (-) <$> use destination <*> use pos
    arg .= atan2 py px
    
    arg' <- use arg
    agility' <- use agility
    when (agility' > 20 && norm (V2 px py) > 10) $ do
      pos += ((fromIntegral agility' / 20 * 0.75) *^ V2 (cos arg') (sin arg'))
    counter += 1
    whenM (use life <&> (< 0)) $ condition .= Dead
    life -= 0.1

  getAI i = use lives <&> (^?! ix i)

  evolve' i Plant = do
    x <- getAI i
    when (x ^. counter `mod` 150 == 0) $ do
      p <- randomVec2
      spawn (create Plant & pos .~ p & destination .~ p)

  evolve' i Herbivore = do
    x <- getAI i
    case x ^. condition of
      Idle -> do
        p <- randomVec2
        zoom (lives . ix i) $ do
          whenM ((use counter <&> (\t -> t `mod` 200 == 0)) <||> (use pos <&> not . isInside) <||> ((distance <$> use pos <*> use destination) <&> (< 10))) $ do
            destination .= p
          when (x ^. life < 60) $ do
            condition .= Hungry
            destination .= 0
      Hungry -> do
        when ((x ^. counter) `mod` 10 == 0) $ do
          ys <- use lives <&> sortBy (comparing (\y -> qd (y^.pos) (x^.pos))) . M.elems . M.filter (\a -> (a ^. life > 20) && (a ^. creature == Plant))
          when (ys /= []) $ lives . ix i . destination .= (head ys^.pos)

        ls <- use lives <&> M.assocs . M.filterWithKey (\k _ -> k /= i) . M.filter (\a -> a^.creature == Plant && distance (a^.pos) (x^.pos) < 10)
        forM_ ls $ \(iy,_) -> do
          lives . ix i . life += 5
          lives . ix iy . life -= (fromIntegral $ x^.strength)

        when (x ^. life > 80) $ do
          lives . ix i . life -= 50
          spawn (create Herbivore & pos .~ (x^.pos))
        zoom (lives . ix i) $ when (x ^. life > 80) $ condition .= Idle
        when (x ^. destination /= 0) $ canvas %= cons (color (V4 0.9 0.9 0 1) $ line [x^.destination, x^.pos])
      _ -> return ()

  evolve' _ _ = return ()

main :: IO ()
main = void $ runSystemDefault $ do
  setTitle "hakoniwa"
  setFPS 30
  renderText <- Text.simple defaultFont 15

  seed' <- liftIO $ save =<< createSystemRandom
  sim <- new $ variable $ World M.empty [] seed'

  replicateM_ 5 $ do
    sim .- do
      p <- randomVec2
      spawn (create Plant & pos .~ p & destination .~ p)
  sim .- spawn (create Herbivore)

--  sim .- lives %= consMap' (create Herbivore)
--  sim .- lives %= consMap' (create Carnivore)
--  sim .- lives %= consMap' (create Human)

  linkPicture $ \_ -> do
    sim .- canvas .= []

    sim .- do
      ls <- use lives
      forM_ (M.keys ls) $ \i -> do
        evolve i
        when (ls ^?! ix i ^. condition == Dead) $ lives %= (sans i)

      ps <- use lives <&> fmap pictureOf . M.elems
      canvas %= cons (color black $ translate (V2 10 20) $ renderText $ show $ length ps)
      canvas %= cons (mconcat ps)

    sim .- use canvas <&> mconcat
  stand

  where
    box :: Float -> Picture
    box r = polygon [V2 (-r) (-r), V2 (-r) r, V2 r r, V2 r (-r)]

    pictureOf :: Alife -> Picture
    pictureOf x = translate (x^.pos) $ rotateOn (x^.arg) $ case (x^.creature) of
      Plant -> color green $ box 4
      Herbivore -> color yellow $ box 10
      Carnivore -> color red $ box 10
      Human -> color blue $ box 7

