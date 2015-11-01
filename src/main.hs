{-# LANGUAGE RankNTypes, FlexibleInstances, FlexibleContexts, MultiWayIf #-}
{-# LANGUAGE LiberalTypeSynonyms, ImpredicativeTypes #-}
import Haste
import Haste.DOM
import Haste.Events
import Haste.Foreign hiding (get)
import Haste.Graphics.Canvas
import Haste.Graphics.AnimationFrame
import Control.Applicative
import Control.Arrow
import Control.Monad
import Control.Monad.State
import qualified Data.IntMap as IM
-- import qualified JSArray as IM
import qualified Data.Map as M
import Data.List
import Data.Ord
import Data.IORef
import Lens.Family2
import Lens.Family2.Unchecked
import Lens.Family2.State.Lazy

data V2 a = V2 !a !a deriving (Eq, Ord, Show)
type Vec2 = V2 Double

fromV2 :: V2 a -> (a,a)
fromV2 (V2 x y) = (x,y)

toV2 :: (a,a) -> V2 a
toV2 (x,y) = V2 x y

_x :: Lens' (V2 a) a
_x = lens (\(V2 x _) -> x) (\(V2 _ y) x -> V2 x y)

_y :: Lens' (V2 a) a
_y = lens (\(V2 _ y) -> y) (\(V2 x _) y -> V2 x y)

instance Functor V2 where
  fmap f (V2 x y) = V2 (f x) (f y)

instance Applicative V2 where
  pure a = V2 a a
  V2 a b <*> V2 d e = V2 (a d) (b e)

instance Monad V2 where
  return a = V2 a a
  V2 a b >>= f = V2 a' b' where
    V2 a' _ = f a
    V2 _ b' = f b

instance Num a => Num (V2 a) where
  (+) = liftA2 (+)
  (-) = liftA2 (-)
  (*) = liftA2 (*)
  negate = fmap negate
  abs = fmap abs
  signum = fmap signum
  fromInteger = pure . fromInteger

instance (Random a) => Random (V2 a) where
  randomR (x,y) = first toV2 . randomR (fromV2 x, fromV2 y)

norm :: Vec2 -> Double
norm (V2 x y) = sqrt $ x^2 + y^2

normalize :: Vec2 -> Vec2
normalize v = fmap (/ norm v) v

scaleV2 :: Double -> Vec2 -> Vec2
scaleV2 d = fmap (* d) . normalize

intersection :: V2 Vec2 -> V2 Vec2 -> V2 Vec2
intersection (V2 lt1 rb1) (V2 lt2 rb2) = V2 (liftA2 max lt1 lt2) (liftA2 min rb1 rb2)

windowSize :: Vec2
windowSize = V2 640 480

approx :: (RealFrac a) => a -> a -> a
approx p a = let q = fromInteger $ floor $ p / a in a * q

distance :: Vec2 -> Vec2 -> Double
distance v v' = norm $ v - v'

ix :: (ToAny b, FromAny b) => Int -> Lens' (IM.IntMap b) b
ix n = lens (IM.! n) (\l x -> IM.insert n x l)

consMap :: (ToAny a, FromAny a) => a -> IM.IntMap a -> (Int, IM.IntMap a)
consMap x m = (n, m & ix n .~ x) where
  ks = filter (\(i,j) -> i /= j) $ zip (IM.keys m) [0..]
  n | IM.size m == 0 = 0
    | ks == [] = last (IM.keys m) + 1
    | otherwise = snd $ head $ ks

consMap' :: (ToAny a, FromAny a) => a -> IM.IntMap a -> IM.IntMap a
consMap' x m = snd $ consMap x m

randomRIO :: (Random a, MonadIO m) => (a,a) -> m a
randomRIO ix = liftIO $ do
  sd <- newSeed
  return $ fst $ randomR ix sd

instance (Random a) => Random (a,a) where
  randomR ((a,b), (c,d)) gen =
    let (x,gen1) = randomR (a,c) gen
        (y,gen2) = randomR (b,d) gen1
    in ((x,y), gen2)

data Creature = Plant | Herbivore | Carnivore deriving (Eq, Ord, Enum, Show)
data Condition = Idle | Hunting | Dead deriving (Eq, Show)
data FieldType = Land | Forest deriving (Eq, Ord, Enum, Show)

eatBy :: Creature -> [Creature]
eatBy Plant = []
eatBy Herbivore = [Plant]
eatBy Carnivore = [Herbivore]

data Alife = Alife {
  -- on canvas
  _pos :: Vec2,
  _arg :: Double,

  -- trait
  _strength :: Int,
  _agility :: Int,
  _creature :: Creature,

  -- state
  _counter :: Int,
  _destination :: Vec2,
  _condition :: Condition,
  _life :: Double,
  _viewRate :: Double,
  _speedRate :: Double
  } deriving (Eq, Show)

instance ToAny Alife where
  toAny = toAny . toOpaque

instance FromAny Alife where
  fromAny = fmap fromOpaque . fromAny

pos :: Lens' Alife Vec2; pos = lens _pos (\a x -> a { _pos = x })
arg :: Lens' Alife Double; arg = lens _arg (\a x -> a { _arg = x })
strength :: Lens' Alife Int; strength = lens _strength (\a x -> a { _strength = x })
agility :: Lens' Alife Int; agility = lens _agility (\a x -> a { _agility = x })
creature :: Lens' Alife Creature; creature = lens _creature (\a x -> a { _creature = x })
counter :: Lens' Alife Int; counter = lens _counter (\a x -> a { _counter = x })
destination :: Lens' Alife Vec2; destination = lens _destination (\a x -> a { _destination = x })
condition :: Lens' Alife Condition; condition = lens _condition (\a x -> a { _condition = x })
life :: Lens' Alife Double; life = lens _life (\a x -> a { _life = x })
viewRate :: Lens' Alife Double; viewRate = lens _viewRate (\a x -> a { _viewRate = x })
speedRate :: Lens' Alife Double; speedRate = lens _speedRate (\a x -> a { _speedRate = x })

data World = World {
  _lives :: !(IM.IntMap Alife),
  _cursor :: Maybe Int,
  _spratio :: [(Int,Int,Int)],
  _globalCounter :: Int,
  _running :: Bool,
  _timeStamp :: HRTimeStamp
  }

lives :: Lens' World (IM.IntMap Alife); lives = lens _lives (\a x -> a { _lives = x })
cursor :: Lens' World (Maybe Int); cursor = lens _cursor (\a x -> a { _cursor = x })
spratio :: Lens' World [(Int, Int, Int)]; spratio = lens _spratio (\a x -> a { _spratio = x })
globalCounter :: Lens' World Int; globalCounter = lens _globalCounter (\a x -> a { _globalCounter = x })
running :: Lens' World Bool; running = lens _running (\a x -> a { _running = x })
timeStamp :: Lens' World HRTimeStamp; timeStamp = lens _timeStamp (\a x -> a { _timeStamp = x })

completeLoadBitmaps :: [Bitmap] -> IO () -> IO ()
completeLoadBitmaps bs cont = foldr (\b m -> void $ onEvent (elemOf b) Load $ const m) cont bs

getInside :: Vec2 -> Vec2
getInside (V2 x y)
  | x < 0 = getInside $ V2 5 y
  | x > (windowSize^._x) = getInside $ V2 (windowSize^._x - 5) y
  | y < 0 = getInside $ V2 x 5
  | y > (windowSize^._y) = getInside $ V2 x (windowSize^._y - 5)
  | otherwise = V2 x y

newLife :: Creature -> Alife
newLife u = case u of
  Plant -> plain & creature .~ Plant & strength .~ 8 & agility .~ 20
  Herbivore -> plain & creature .~ Herbivore & strength .~ 50 & agility .~ 60
  Carnivore -> plain & creature .~ Carnivore & strength .~ 90 & agility .~ 60
  where
    plain = Alife {
      _pos = fmap (/2) windowSize, _arg = 0,
      _strength = 0, _agility = 0, _creature = undefined,
      _counter = 0, _destination = 0, _condition = Idle, _life = 100,
      _viewRate = 1.0, _speedRate = 1.0
      }

spawn :: Alife -> StateT World IO ()
spawn ai = do
  ps <- IM.elems `fmap` use lives
  case ai^.creature of
    Plant -> when ((< 1000) $ length $ filter (\a -> a^.creature == Plant) ps) $ lives %= consMap' ai
    Herbivore -> when ((< 200) $ length $ filter (\a -> a^.creature == Herbivore) ps) $ lives %= consMap' ai
    Carnivore -> when ((< 50) $ length $ filter (\a -> a^.creature == Carnivore) ps) $ lives %= consMap' ai

destruct :: Int -> StateT World IO ()
destruct j = do
  x <- use $ lives . ix j
  destructor' j (x^.creature)

  where
    plantAround :: Vec2 -> Double -> StateT World IO ()
    plantAround x d = do
      let V2 c1 c2 = V2 (x - pure d) (x + pure d) `intersection` V2 0 windowSize
      p <- randomRIO (c1, c2)
      spawn (newLife Plant & pos .~ p & destination .~ p)

    destructor' i Plant = return ()
    destructor' i Herbivore = do
      x <- use $ lives . ix j
      let view = (x^.viewRate) * 80
      replicateM_ (floor $ fromIntegral (x^.strength) / 10) $ plantAround (x^.pos) view
    destructor' i Carnivore = do
      x <- use $ lives . ix j
      let view = (x^.viewRate) * 80
      replicateM_ (floor $ fromIntegral (x^.strength) / 10) $ plantAround (x^.pos) view

evolve :: Int -> StateT World IO ()
evolve j = do
  ai <- use (lives . ix j)
  zoom (lives . ix j) $ runAI

  eat j
  evolve' j (ai^.creature)

  where
    getAI :: Int -> StateT World IO Alife
    getAI i = use (lives . ix i)

    runAI :: StateT Alife IO ()
    runAI = do
      ai <- get
      V2 px py <- (-) <$> use destination <*> use pos
      arg .= (atan2 py px) `approx` ((2 * pi) * 15 / 360)

      spR <- use speedRate
      when (ai^.agility > 20 && norm (V2 px py) > 10) $ do
        let f = \x -> x / 300 + 1
        let q = \x -> sqrt x / 150 + 1
        let vel = fromIntegral (ai^.agility) / 20 * f (100 - ai^.life) / 2 / q (fromIntegral $ ai^.counter)
        pos += scaleV2 (vel * spR) (V2 (cos $ ai^.arg) (sin $ ai^.arg))
      when (ai^.life < 0) $ condition .= Dead
      life -= (fromIntegral (ai^.strength) / 1000 + fromIntegral (ai^.agility) / 1000) * spR
      counter += 1

    eat :: Int -> StateT World IO Bool
    eat i = do
      x <- getAI i
      xs <- filter (\(_,z) -> z^.life > 0) <$> searchIn i 10 (eatBy $ x^.creature)
      when (xs /= []) $ do
        let (iy,y) = head xs
        lives . ix i . life += (fromIntegral $ y^.strength)^2 / 200
        lives . ix i . life %= min 100
        lives . ix iy . life -= (fromIntegral $ x^.strength)^3 / 100000
        -- canvas %= cons (color (V4 1 0.5 0 1) $ line [y^.pos, x^.pos])

      return $ xs == []

    searchIn :: Int -> Double -> [Creature] -> StateT World IO [(Int, Alife)]
    searchIn i d targets = do
      x <- getAI i
      ls <- use lives
      return $
        sortBy (comparing (\(_,y) -> distance (y^.pos) (x^.pos))) $
        IM.assocs $
        IM.filter (\a -> distance (a^.pos) (x^.pos) < d && a^.creature `elem` targets) $ ls

    randomWalk :: Int -> StateT World IO ()
    randomWalk i = do
      x <- getAI i
      when ((x^.counter) `mod` 500 == 0 || distance (x^.pos) (x^.destination) < 10) $ do
        p <- randomRIO (getInside $ x^.pos - 150, getInside $ x^.pos + 150)
        lives . ix i . destination .= p

    runAwayFrom :: Int -> Double -> [Creature] -> StateT World IO ()
    runAwayFrom i d es = do
      x <- getAI i
      es' <- fmap snd <$> searchIn i d es
      when (es' /= []) $ do
        let tvec = sum $ fmap (\e -> let v = x^.pos - e^.pos in scaleV2 (d - norm v) v) es'
        lives . ix i . destination .= (getInside $ tvec)

    plantAround :: Vec2 -> Double -> StateT World IO ()
    plantAround x d = do
      let V2 c1 c2 = V2 (x - pure d) (x + pure d) `intersection` V2 0 windowSize
      p <- randomRIO (c1, c2)
      spawn (newLife Plant & pos .~ p & destination .~ p)

    evolve' i Plant = do
      x <- getAI i
      plants <- IM.filter (\a -> a ^. creature == Plant && distance (a^.pos) (x^.pos) < 100) <$> use lives
      when (x ^. counter `mod` 150 == 0 && IM.size plants < 10) $ replicateM_ 3 $ plantAround (x^.pos) 30

    evolve' i Herbivore = do
      x <- getAI i
      let view = (x^.viewRate) * 80
      eat i >>= \b -> when b $ do
        if
         | x^.condition == Idle || x^.condition == Hunting -> do
           xs <- fmap snd <$> searchIn i view (eatBy $ x^.creature)
           ys <- fmap snd <$> searchIn i 20 (eatBy $ x^.creature)
           zs <- fmap snd <$> searchIn i 5 (eatBy $ x^.creature)
           unless (zs /= []) $ do
             if
               | ys /= [] -> lives . ix i . destination .= (head ys ^. pos)
               | x^.life < 50 && xs /= [] -> lives . ix i . destination .= (head xs ^. pos)
               | x^.life > 80
                 && (200 < x^.counter)
                 && x^.counter `mod` 500 == 0 -> spawn (newLife (x^.creature) & pos .~ (x^.pos))
               | otherwise -> do
                   randomWalk i

           runAwayFrom i (view / 2) [Carnivore]

         | x^.condition == Dead -> return ()

    evolve' i Carnivore = do
      x <- getAI i
      let view = (x^.viewRate) * 40
--      canvas %= cons (translate (x^.pos) $ color (V4 0.4 0.3 1 0.5) $ circleOutline $ if x^.life < 70 then double2Float view else 20)

      eat i >>= \b -> when b $ do
        if
         | x^.condition == Idle || x^.condition == Hunting -> do
            xs <- fmap snd <$> searchIn i view (eatBy $ x^.creature)
            ys <- fmap snd <$> searchIn i 20 (eatBy $ x^.creature)
            zs <- fmap snd <$> searchIn i 5 (eatBy $ x^.creature)
            unless (zs /= []) $ do
              if
                | ys /= [] -> lives . ix i . destination .= (head ys ^. pos)
                | x^.life < 70 && xs /= [] -> do
                    lives . ix i . condition .= Hunting
                    lives . ix i . destination .= (head xs ^. pos)
                | x^.life > 80
                  && (200 < x^.counter)
                  && x^.counter `mod` 500 == 0 -> do
                    lives . ix i . condition .= Idle
                    spawn (newLife (x^.creature) & pos .~ (x^.pos))
                | otherwise -> do
                    lives . ix i . condition .= Idle
                    randomWalk i
         | x^.condition == Dead -> return ()

mainloop :: IORef World -> [Bitmap] -> Canvas -> IO ()
mainloop ref bmps cv = void $ do
  render cv . stroke $ circle (0,0) 0

  forM_ [1..400] $ \i -> do
    k <- randomRIO (0,600)
    renderOnTop cv $ do
      draw (bmps !! 2) (k,i)
      -- stroke $ circle (k,i) 10

  onceStateT ref $ do
    ls <- use lives
    forM_ (IM.keys ls) $ evolve

  -- onceStateT ref $ do
  --   globalCounter += 1
  --
  --   r <- use running
  --   when r $ do
  --     withElem "alife-num" $ \e -> do
  --       s <- IM.size <$> use lives
  --       setProp e "innerText" $ show s
  --     withElem "alife-all-num" $ \e -> do
  --       s <- last . IM.keys <$> use lives
  --       setProp e "innerText" $ show s
  --
  --     ls <- use lives
  --
  --     forM_ (IM.keys ls) $ evolve
  --     forM_ (IM.assocs ls) $ \(i,x) -> do
  --       when (x^.condition == Dead) $ do
  --         destruct i
  --         lives %= IM.delete i
  --
  --     render cv $ do
  --       forM_ (IM.assocs ls) $ \(i,x) -> do
  --         let ps = M.fromList $ zip [Plant, Herbivore, Carnivore] [0..]
  --         draw (bmps !! (ps M.! (x^.creature))) $ fromV2 $ x^.pos

  requestAnimationFrame $ \p -> do
    onceStateT ref $ do
      t <- use timeStamp
      r <- use running
      when r $ do
        withElem "fps" $ \e -> do
          setProp e "innerText" $ show $ floor $ 1000 / (p - t)

      timeStamp .= p

    mainloop ref bmps cv

main :: IO ()
main = do
  Just cv <- getCanvasById "hakoniwa-canvas"
  bmps <- mapM loadBitmap ["img/creature0.png", "img/creature1.png", "img/creature2.png"]

  completeLoadBitmaps bmps $ do
    ref <- newIORef $ World IM.empty Nothing [] 0 True 0

    replicateM_ 50 $ onceStateT ref $ do
      p <- liftIO $ randomRIO (pure 0, windowSize)
      spawn (newLife Plant & pos .~ p & destination .~ p)
    replicateM_ 20 $ onceStateT ref $ do
      p <- liftIO $ randomRIO (pure 0, windowSize)
      spawn (newLife Herbivore & pos .~ p & destination .~ p)
    replicateM_ 3 $ onceStateT ref $ do
      p <- liftIO $ randomRIO (pure 0, windowSize)
      spawn (newLife Carnivore & pos .~ p & destination .~ p)

    withElem "game-run" $ \e -> do
      onEvent e Click $ \_ -> do
        onceStateT ref $ running .= True

    withElem "game-stop" $ \e -> do
      onEvent e Click $ \_ -> do
        onceStateT ref $ running .= False

    mainloop ref bmps cv

onceStateT :: IORef s -> StateT s IO a -> IO a
onceStateT ref m = do
  x <- readIORef ref
  (a,x') <- runStateT m x
  writeIORef ref $! x'
  return a
