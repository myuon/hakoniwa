{-# LANGUAGE GADTs, TemplateHaskell, FlexibleContexts, MultiWayIf #-}
import Call
import Call.Util.Text as Text
import qualified Data.BoundingBox as Box
import Control.Lens
import Control.Monad.State.Strict
import Control.Monad.Trans.Maybe
import qualified Data.IntMap.Strict as M
import Data.Ord (comparing)
import Data.List (sortBy)
import System.Random.MWC hiding (create)

window :: V2 Float
window = V2 640 480

consMap :: a -> M.IntMap a -> (Int, M.IntMap a)
consMap x m
  | M.size m == 0 = (0, m & at 0 ?~ x)
  | otherwise = let (i,_) = M.findMax m in (i+1, m & at (i+1) ?~ x)

consMap' :: a -> M.IntMap a -> M.IntMap a
consMap' x m = snd $ consMap x m

approx :: (RealFrac a) => a -> a -> a
approx p a = let q = fromInteger $ floor $ p / a in a * q

instance (Variate a) => Variate (V2 a) where
  uniform = error "undefined method `uniform'"
  uniformR (V2 a b, V2 c d) m = do
    x <- uniformR (a,c) m
    y <- uniformR (b,d) m
    return $ V2 x y

data Creature = Plant | Herbivore | Carnivore | Human deriving (Eq, Show)
data Condition = Idle | Hunting | Dead deriving (Eq, Show)

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
  _life :: Float
  } deriving (Eq, Show)

data World = World {
  _lives :: M.IntMap Alife,
  _canvas :: [Picture],
  _seed :: Seed,
  _cursor :: Maybe Int
  }

makeLenses ''Alife
makeLenses ''World

getInside :: Vec2 -> Vec2
getInside (V2 x y)
  | x < 0 = getInside $ V2 5 y
  | x > (window^._x) = getInside $ V2 (window^._x - 5) y
  | y < 0 = getInside $ V2 x 5
  | y > (window^._y) = getInside $ V2 x (window^._y - 5)
  | otherwise = V2 x y

create :: Creature -> Alife
create u = case u of
  Plant -> plain & creature .~ Plant & strength .~ 8 & agility .~ 20
  Herbivore -> plain & creature .~ Herbivore & strength .~ 50 & agility .~ 60
  Carnivore -> plain & creature .~ Carnivore & strength .~ 90 & agility .~ 60
  Human -> plain & creature .~ Human & strength .~ 25 & agility .~ 25
  where
    plain = Alife {
      _pos = V2 320 240, _arg = 0,
      _strength = 0, _agility = 0, _creature = undefined,
      _counter = 0, _destination = 0, _condition = Idle, _life = 100
      }

eatBy :: Creature -> [Creature]
eatBy Plant = []
eatBy Herbivore = [Plant]
eatBy Carnivore = [Herbivore, Human]
eatBy Human = [Plant, Herbivore]

spawn :: Alife -> StateT World (System s) ()
spawn ai = do
  ps <- use lives <&> M.elems
  case ai^.creature of
    Plant -> when ((< 1000) $ length $ filter (\a -> a^.creature == Plant) ps) $ lives %= consMap' ai
    Herbivore -> when ((< 200) $ length $ filter (\a -> a^.creature == Herbivore) ps) $ lives %= consMap' ai
    Carnivore -> when ((< 50) $ length $ filter (\a -> a^.creature == Carnivore) ps) $ lives %= consMap' ai

randomVec2 :: (Functor m, MonadIO m, Variate a) => (a,a) -> StateT World m a
randomVec2 r = do
  gen <- liftIO . restore =<< use seed
  v <- liftIO $ uniformR r gen
  seed <~ liftIO (save gen)
  return v

evolve :: Int -> StateT World (System s) ()
evolve j = do
  x <- getAI j
  eat j
  evolve' j (x^.creature)
  zoom (lives . ix j) runAI

  where
  runAI = do
    x <- get
    V2 px py <- (-) <$> use destination <*> use pos
    arg .= (atan2 py px) `approx` ((2 * pi) * 15 / 360)
    
    when (x^.agility > 20 && norm (V2 px py) > 10) $ do
      let f = \x -> x / 300 + 1
      let q = \x -> sqrt x / 150 + 1
      let hunting = if x^.condition == Hunting then 1.2 else 1.0
      pos += (fromIntegral (x^.agility) / 20 * f (100 - x^.life) / 2 / q (fromIntegral $ x^.counter)) *^ V2 (cos $ x^.arg) (sin $ x^.arg)
    when (x^.life < 0) $ condition .= Dead
    life -= fromIntegral (x^.strength) / 1000 + fromIntegral (x^.agility) / 1000
    counter += 1

  eat i = do
    x <- getAI i
    xs <- use lives <&> M.assocs . M.filterWithKey (\k a -> k /= j && a^.creature `elem` eatBy (x^.creature) && distance (a^.pos) (x^.pos) < 10 && a^.life > 0)
    forM_ (take 1 xs) $ \(iy,y) -> do
      lives . ix i . life += (fromIntegral $ y^.strength)^2 / 200
      lives . ix i . life %= min 100
      lives . ix iy . life -= (fromIntegral $ x^.strength)^3 / 100000
      canvas %= cons (color (V4 1 0.5 0 1) $ line [y^.pos, x^.pos])
    return $ xs == []

  searchIn i d es = do
    x <- getAI i
    ls <- use lives
    let targets = es
    return $
      sortBy (comparing (\y -> qd (y^.pos) (x^.pos))) $
      M.elems $
      M.filter (\a -> distance (a^.pos) (x^.pos) < d && a^.creature `elem` targets) $ ls

  randomWalk i = do
    x <- getAI i
    when ((x^.counter) `mod` 500 == 0 || distance (x^.pos) (x^.destination) < 10) $ do
      p <- randomVec2 (getInside $ x^.pos - 150, getInside $ x^.pos + 150)
      lives . ix i . destination .= p

  runAwayFrom i d es = do
    x <- getAI i
    es' <- searchIn i d es
    when (es' /= []) $ do
      lives . ix i . destination .= (getInside $ sum $ fmap (\e -> let d = x^.pos - e^.pos in (quadrance d) *^ d) es')

  getAI i = use lives <&> (^?! ix i)

  evolve' i Plant = do
    x <- getAI i
    plants <- use lives <&> M.filter (\a -> a ^. creature == Plant && distance (a^.pos) (x^.pos) < 100)
    when (x ^. counter `mod` 150 == 0 && M.size plants < 10) $ replicateM_ 3 $ do
      p <- randomVec2 (x^.pos - 30, x^.pos + 30)
      spawn (create Plant & pos .~ p & destination .~ p)

  evolve' i Herbivore = do
    x <- getAI i
    whenM (eat i) $ do
      if
       | x^.condition == Idle || x^.condition == Hunting -> do
         xs <- searchIn i 80 (eatBy $ x^.creature)
         ys <- searchIn i 20 (eatBy $ x^.creature)
         zs <- searchIn i 5 (eatBy $ x^.creature)
         unless (zs /= []) $ do
           if
             | ys /= [] -> lives . ix i . destination .= (head ys ^. pos)
             | x^.life < 50 && xs /= [] -> lives . ix i . destination .= (head xs ^. pos)
             | x^.life > 80
               && (200 < x^.counter)
               && x^.counter `mod` 300 == 0 -> spawn (create (x^.creature) & pos .~ (x^.pos))
             | otherwise -> do
                 randomWalk i

         runAwayFrom i 40 [Carnivore]
       
       | x^.condition == Dead -> replicateM_ (floor $ fromIntegral (x^.strength) / 10) $ do
         p <- randomVec2 (x^.pos - 40, x^.pos + 40)
         spawn (create Plant & pos .~ p & destination .~ p)

  evolve' i Carnivore = do
    x <- getAI i
    whenM (eat i) $ do
      if
       | x^.condition == Idle || x^.condition == Hunting -> do
          xs <- searchIn i 30 (eatBy $ x^.creature)
          ys <- searchIn i 20 (eatBy $ x^.creature)
          zs <- searchIn i 5 (eatBy $ x^.creature)
          unless (zs /= []) $ do
            if
              | ys /= [] -> lives . ix i . destination .= (head ys ^. pos)
              | x^.life < 70 && xs /= [] -> do
                  lives . ix i . condition .= Hunting
                  lives . ix i . destination .= (head xs ^. pos)
              | x^.life > 80
                && (200 < x^.counter)
                && x^.counter `mod` 300 == 0 -> do
                  lives . ix i . condition .= Idle
                  spawn (create (x^.creature) & pos .~ (x^.pos))
              | otherwise -> do
                  lives . ix i . condition .= Idle
                  randomWalk i
       | x^.condition == Dead -> replicateM_ (floor $ fromIntegral (x^.strength) / 10) $ do
         p <- randomVec2 (x^.pos - 40, x^.pos + 40)
         spawn (create Plant & pos .~ p & destination .~ p)

  evolve' _ _ = return ()

main :: IO ()
main = void $ runSystemDefault $ do
  setTitle "hakoniwa"
  setFPS 30
  setBoundingBox $ Box.Box 0 window
  renderText <- Text.simple defaultFont 15

  seed' <- liftIO $ save =<< createSystemRandom
  sim <- new $ variable $ World M.empty [] seed' Nothing

  replicateM_ 100 $ do
    sim .- do
      p <- randomVec2 (V2 0 0, window)
      spawn (create Plant & pos .~ p & destination .~ p)
  replicateM_ 40 $ do
    sim .- do
      p <- randomVec2 (V2 0 0, window)
      spawn (create Herbivore & pos .~ p & destination .~ p)
  replicateM_ 5 $ do
    sim .- do
      p <- randomVec2 (V2 0 0, window)
      spawn (create Carnivore & pos .~ p & destination .~ p)

  linkPicture $ \_ -> do
    sim .- canvas .= []

    sim .- do
      ls <- use lives
      forM_ (M.keys ls) $ \i -> do
        evolve i
        when (ls ^?! ix i ^. condition == Dead) $ lives %= (sans i)

      ps <- use lives <&> M.elems
      canvas %= cons (color green $ translate (V2 10 20) $ renderText $ show $ length $ filter (\a -> a^.creature == Plant) ps)
      canvas %= cons (color yellow $ translate (V2 10 40) $ renderText $ show $ length $ filter (\a -> a^.creature == Herbivore) ps)
      canvas %= cons (color red $ translate (V2 10 60) $ renderText $ show $ length $ filter (\a -> a^.creature == Carnivore) $ ps)
      canvas %= cons (mconcat $ fmap pictureOf ps)

    sim .- do
      m <- use cursor
      ls <- use lives
      cursor .= (m >>= \i -> ifThenElse (M.member i ls) m Nothing)

    m <- sim .- use cursor
    case m of
      Just i -> do
        sim .- do
          x <- use lives <&> (^?! ix i)
          let c = V4 0.8 0.2 0.5 1
          canvas %= cons (color c $ translate (x^.pos) $ circleOutline 15)
          canvas %= cons (color c $ translate (x^.pos + V2 20 (-15)) $ renderText $ "LIFE: " ++ show (floor $ x^.life))
          canvas %= cons (color c $ translate (x^.pos + V2 20 5) $ renderText $ "STR: " ++ show (x^.strength))

      Nothing -> return ()

    sim .- use canvas <&> mconcat

  linkMouse $ \e -> when (mouseClicked e) $ do
    v <- mousePosition
    sim .- do
      ys <- sortBy (comparing (\(_,a) -> qd (a^.pos) v)) . M.assocs . M.filter (\a -> distance (a^.pos) v < 50) <$> use lives
      when (ys /= []) $ do
        cursor .= Just (fst $ head ys)

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

    mouseClicked (Button _) = True
    mouseClicked _ = False

