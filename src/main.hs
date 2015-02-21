{-# LANGUAGE GADTs, TemplateHaskell, FlexibleContexts, MultiWayIf #-}
{-# LANGUAGE FlexibleInstances #-}
import Call
import Call.Util.Text as Text
import Data.BoundingBox
import Control.Lens
import Control.Monad.State.Strict
import Data.Ord (comparing)
import Data.List (sortBy)
import Data.Array
import Data.Array.IO
import Data.Trees.KdTree as K
import qualified Data.IntMap.Strict as IM
import System.Random.MWC hiding (create)
import GHC.Float (float2Double, double2Float)

windowSize :: V2 Float
windowSize = V2 854 480

squareSize :: V2 Float
squareSize = V2 25 25

squareNumber :: V2 Int
squareNumber = fmap floor $ windowSize / squareSize

consMap :: a -> IM.IntMap a -> (Int, IM.IntMap a)
consMap x m
  | IM.size m == 0 = (0, m & at 0 ?~ x)
  | otherwise = let (i,_) = IM.findMax m in (i+1, m & at (i+1) ?~ x)

consMap' :: a -> IM.IntMap a -> IM.IntMap a
consMap' x m = snd $ consMap x m

approx :: (RealFrac a) => a -> a -> a
approx p a = let q = fromInteger $ floor $ p / a in a * q

data Creature = Plant | Herbivore | Carnivore deriving (Eq, Ord, Enum, Show)
data Condition = Idle | Hunting | Dead deriving (Eq, Show)
data FieldType = Land | Forest deriving (Eq, Ord, Enum, Show)

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
  _life :: Float,
  _viewRate :: Double,
  _speedRate :: Float
  } deriving (Eq, Show)

data World = World {
  _lives :: IM.IntMap Alife,
  _canvas :: [Picture],
  _seed :: Seed,
  _cursor :: Maybe Int,
  _spratio :: [(Int,Int,Int)],
  _globalCounter :: Int,
  _fieldMap :: Array (Int,Int) FieldType,
  _spTree :: K.KdTree (Int,Alife)
  }

makeLenses ''Alife
makeLenses ''World

instance (Variate a) => Variate (V2 a) where
  uniform = error "undefined method `uniform'"
  uniformR (V2 a b, V2 c d) m = do
    x <- uniformR (a,c) m
    y <- uniformR (b,d) m
    return $ V2 x y

instance K.Point Vec2 where
  dimension _ = 2
  coord 0 p = float2Double $ p^._x
  coord 1 p = float2Double $ p^._y

instance K.Point Alife where
  dimension x = dimension $ x^.pos
  coord i x = coord i $ x^.pos

instance K.Point b => K.Point (a,b) where
  dimension (_,y) = dimension y
  coord i (_,p) = coord i p

getInside :: Vec2 -> Vec2
getInside (V2 x y)
  | x < 0 = getInside $ V2 5 y
  | x > (windowSize^._x) = getInside $ V2 (windowSize^._x - 5) y
  | y < 0 = getInside $ V2 x 5
  | y > (windowSize^._y) = getInside $ V2 x (windowSize^._y - 5)
  | otherwise = V2 x y

create :: Creature -> Alife
create u = case u of
  Plant -> plain & creature .~ Plant & strength .~ 8 & agility .~ 20
  Herbivore -> plain & creature .~ Herbivore & strength .~ 50 & agility .~ 60
  Carnivore -> plain & creature .~ Carnivore & strength .~ 90 & agility .~ 60
  where
    plain = Alife {
      _pos = V2 320 240, _arg = 0,
      _strength = 0, _agility = 0, _creature = undefined,
      _counter = 0, _destination = 0, _condition = Idle, _life = 100,
      _viewRate = 1.0, _speedRate = 1.0
      }

eatBy :: Creature -> [Creature]
eatBy Plant = []
eatBy Herbivore = [Plant]
eatBy Carnivore = [Herbivore]

spawn :: Alife -> StateT World (System s) ()
spawn ai = do
  ps <- use lives <&> IM.elems
  case ai^.creature of
    Plant -> when ((< 1000) $ length $ filter (\a -> a^.creature == Plant) ps) $ lives %= consMap' ai
    Herbivore -> when ((< 200) $ length $ filter (\a -> a^.creature == Herbivore) ps) $ lives %= consMap' ai
    Carnivore -> when ((< 50) $ length $ filter (\a -> a^.creature == Carnivore) ps) $ lives %= consMap' ai

randomR :: (Functor m, MonadIO m, Variate a) => (a,a) -> StateT World m a
randomR r = do
  s <- use seed
  gen <- liftIO . restore =<< use seed
  v <- liftIO $ uniformR r gen
  seed <~ liftIO (save gen)
  return v

destructor :: Int -> StateT World (System s) ()
destructor j = do
  x <- getAI j
  destructor' j (x^.creature)

  where
  getAI i = use lives <&> (^?! ix i)

  plantAround :: Vec2 -> Float -> StateT World (System s) ()
  plantAround x d = do
    let Box c1 c2 = Box (x - pure d) (x + pure d) `intersect` Box 0 windowSize
    p <- randomR (c1, c2)
    spawn (create Plant & pos .~ p & destination .~ p)

  destructor' i Plant = return ()
  destructor' i Herbivore = do
    x <- getAI i
    let view = (x^.viewRate) * 80
    replicateM_ (floor $ fromIntegral (x^.strength) / 10) $ plantAround (x^.pos) (double2Float view)
  destructor' i Carnivore = do
    x <- getAI i
    let view = (x^.viewRate) * 80
    replicateM_ (floor $ fromIntegral (x^.strength) / 10) $ plantAround (x^.pos) (double2Float view)

evolve :: Int -> StateT World (System s) ()
evolve j = do
  x <- getAI j

  fm <- use fieldMap
  let V2 sx sy = fmap floor $ x^.pos / squareSize
  zoom (lives . ix j) $ fieldAction (fm ! (sx,sy))

  eat j
  evolve' j (x^.creature)
  zoom (lives . ix j) runAI

  where
  getAI i = use lives <&> (^?! ix i)

  runAI = do
    ai <- get
    V2 px py <- (-) <$> use destination <*> use pos
    arg .= (atan2 py px) `approx` ((2 * pi) * 15 / 360)
    
    spR <- use speedRate
    when (ai^.agility > 20 && norm (V2 px py) > 10) $ do
      let f = \x -> x / 300 + 1
      let q = \x -> sqrt x / 150 + 1
      let vel = fromIntegral (ai^.agility) / 20 * f (100 - ai^.life) / 2 / q (fromIntegral $ ai^.counter)
      pos += vel * spR *^ V2 (cos $ ai^.arg) (sin $ ai^.arg)
    when (ai^.life < 0) $ condition .= Dead
    life -= (fromIntegral (ai^.strength) / 1000 + fromIntegral (ai^.agility) / 1000) * spR
    counter += 1

  fieldAction :: FieldType -> StateT Alife (System s) ()
  fieldAction Land = do
    viewRate .= 1
    speedRate .= 1
  fieldAction Forest = do
    viewRate .= 0.5
    speedRate .= 0.5

  eat :: Int -> StateT World (System s) Bool
  eat i = do
    x <- getAI i
    xs <- searchIn i 10 (eatBy $ x^.creature) <&> filter (\(_,z) -> z^.life > 0)
    when (xs /= []) $ do
      let (iy,y) = head xs
      lives . ix i . life += (fromIntegral $ y^.strength)^2 / 200
      lives . ix i . life %= min 100
      lives . ix iy . life -= (fromIntegral $ x^.strength)^3 / 100000
      canvas %= cons (color (V4 1 0.5 0 1) $ line [y^.pos, x^.pos])

    return $ xs == []

  searchIn :: Int -> Double -> [Creature] -> StateT World (System s) [(Int, Alife)]
  searchIn i d targets = do
    x <- getAI i
    spT <- use spTree
    mapM (\(k,_) -> getAI k >>= \z -> return (k,z)) $ reverse $ filter (\(j,z) -> j /= i && z^.creature `elem` targets) $ nearNeighbors spT d (i,x)

  randomWalk :: Int -> StateT World (System s) ()
  randomWalk i = do
    x <- getAI i
    when ((x^.counter) `mod` 500 == 0 || distance (x^.pos) (x^.destination) < 10) $ do
      p <- randomR (getInside $ x^.pos - 150, getInside $ x^.pos + 150)
      lives . ix i . destination .= p

  runAwayFrom :: Int -> Double -> [Creature] -> StateT World (System s) ()
  runAwayFrom i d es = do
    x <- getAI i
    es' <- fmap snd <$> searchIn i d es
    when (es' /= []) $ do
      lives . ix i . destination .= (getInside $ sum $ fmap (\e -> let d' = x^.pos - e^.pos in (quadrance d') *^ d') es')

  plantAround :: Vec2 -> Float -> StateT World (System s) ()
  plantAround x d = do
    let Box c1 c2 = Box (x - pure d) (x + pure d) `intersect` Box 0 windowSize
    p <- randomR (c1, c2)
    spawn (create Plant & pos .~ p & destination .~ p)

  evolve' i Plant = do
    x <- getAI i
    plants <- use lives <&> IM.filter (\a -> a ^. creature == Plant && distance (a^.pos) (x^.pos) < 100)
    when (x ^. counter `mod` 150 == 0 && IM.size plants < 10) $ replicateM_ 3 $ plantAround (x^.pos) 30

  evolve' i Herbivore = do
    x <- getAI i
    let view = (x^.viewRate) * 80
    whenM (eat i) $ do
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
               && x^.counter `mod` 500 == 0 -> spawn (create (x^.creature) & pos .~ (x^.pos))
             | otherwise -> do
                 randomWalk i

         runAwayFrom i (view / 2) [Carnivore]
       
       | x^.condition == Dead -> return ()

  evolve' i Carnivore = do
    x <- getAI i
    let view = (x^.viewRate) * 40
    whenM (eat i) $ do
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
                  spawn (create (x^.creature) & pos .~ (x^.pos))
              | otherwise -> do
                  lives . ix i . condition .= Idle
                  randomWalk i
       | x^.condition == Dead -> return ()

newField :: StateT World (System s) (Array (Int,Int) FieldType)
newField = do
  arr <- liftIO $ (newListArray ((0,0),(w,h)) (repeat Land) :: IO (IOArray (Int,Int) FieldType))
  forM_ [0..w] $ \x ->
    forM_ [0..h] $ \y -> do
      b <- randomR (0,1)
      liftIO $ writeArray arr (x,y) $ toEnum b

  replicateM_ 10 $ go arr
  liftIO $ freeze arr
  where
    V2 w h = fmap floor $ windowSize / squareSize    
    go arr = do
      forM_ [1..w-1] $ \x ->
        forM_ [1..h-1] $ \y -> do
          neighbors <- mapM (liftIO . readArray arr) [(x-i,y-j)|i<-[-1,0,1], j<-[-1,0,1], (i,j) /= (0,0)]
          b <- randomR (0,7)
          liftIO $ writeArray arr (x,y) $ neighbors !! b

main :: IO ()
main = void $ runSystemDefault $ do
  setTitle "hakoniwa"
  setFPS 30
  setBoundingBox $ Box 0 windowSize
  renderText <- Text.simple defaultFont 15

  bmps <- mapM readBitmap ["img/creature0.png", "img/creature1.png", "img/creature2.png"]

  seed' <- liftIO $ save =<< createSystemRandom
  sim <- newSettle $ variable $ World {
    _lives = IM.empty, _canvas = [], _seed = seed',
    _cursor = Nothing, _spratio = [], _globalCounter = 0,
    _fieldMap = listArray ((0,0),(0,0)) $ [],
    _spTree = K.fromList []
    }
  sim .- (fieldMap <~ newField)

  replicateM_ 50 $ do
    sim .- do
      p <- randomR (0, windowSize)
      spawn (create Plant & pos .~ p & destination .~ p)
  replicateM_ 20 $ do
    sim .- do
      p <- randomR (0, windowSize)
      spawn (create Herbivore & pos .~ p & destination .~ p)
  replicateM_ 3 $ do
    sim .- do
      p <- randomR (0, windowSize)
      spawn (create Carnivore & pos .~ p & destination .~ p)

  linkPicture $ \_ -> do
    sim .- globalCounter += 1
    sim .- canvas .= []

    sim .- do
      ls <- use lives
      forM_ (IM.keys ls) evolve

      forM_ (IM.assocs ls) $ \(i,x) -> do
        when (x^.condition == Dead) $ do
          destructor i
          lives %= sans i

--      lives %= IM.filter (\a -> a^.condition /= Dead)
      spTree <~ (use lives <&> K.fromList . IM.assocs)

    sim .- do
      ls <- use lives
      m <- use cursor
      cursor .= (m >>= \i -> ifThenElse (IM.member i ls) m Nothing)

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

    sim .- do
      ps <- use lives <&> IM.elems
      let plants = length $ filter (\a -> a^.creature == Plant) ps
      let herbs = length $ filter (\a -> a^.creature == Herbivore) ps
      let carns = length $ filter (\a -> a^.creature == Carnivore) ps
--      whenM (use globalCounter <&> \t -> t `mod` 30 == 0) $ do
--        spratio %= cons (plants,herbs,carns)

{-
      let d = 2
      let ymax = 150
      let yscale = 0.15
      ds <- use spratio
      canvas %= cons (color (V4 0 1 0 1) $ line $ fmap (\(p,x) -> V2 x (ymax - fromIntegral (p^._1) * yscale - 0.1)) $ zip ds [d,d*2..])
      canvas %= cons (color (V4 1 1 0 1) $ line $ fmap (\(p,x) -> V2 x (ymax - fromIntegral (p^._2) * yscale - 0.1)) $ zip ds [d,d*2..])
      canvas %= cons (color (V4 1 0 0 1) $ line $ fmap (\(p,x) -> V2 x (ymax - fromIntegral (p^._3) * yscale - 0.1)) $ zip ds [d,d*2..])
-}

      canvas %= cons (color green $ translate (V2 10 20) $ renderText $ show plants)
      canvas %= cons (color yellow $ translate (V2 10 40) $ renderText $ show herbs)
      canvas %= cons (color red $ translate (V2 10 60) $ renderText $ show carns)

      canvas %= cons (mconcat $ fmap (pictureOf bmps) $ sortBy (comparing (^.creature)) $ ps)

      fm <- use fieldMap
      let V2 w h = squareNumber
      forM_ [0..w] $ \x -> do
        forM_ [0..h] $ \y -> do
          canvas %= cons (paintOf (x,y) $ fm ! (x,y))

    sim .- use canvas <&> mconcat

  linkMouse $ \e -> when (mouseClicked e) $ do
    v <- mousePosition
    sim .- do
      ys <- use lives <&> sortBy (comparing (\(_,a) -> qd (a^.pos) v)) . IM.assocs . IM.filter (\a -> distance (a^.pos) v < 50)
      when (ys /= []) $ do
        cursor .= Just (fst $ head ys)

  stand

  where
    box :: Float -> Picture
    box r = polygon [V2 (-r) (-r), V2 (-r) r, V2 r r, V2 r (-r)]

    pictureOf :: [Bitmap] -> Alife -> Picture
    pictureOf bmps x = translate (x^.pos) $ scale 0.8 $ case (x^.creature) of
      Plant -> bitmap (bmps !! 0)
      Herbivore -> bitmap (bmps !! 1)
      Carnivore -> bitmap (bmps !! 2)

    paintOf :: (Int,Int) -> FieldType -> Picture
    paintOf (x,y) ftype = translate v $ case ftype of
      Land -> color (V4 0.97 0.98 0.81 1) $ area
      Forest -> color (V4 0.36 0.74 0.33 0.6) $ area
      where
        v = V2 (fromIntegral x * (squareSize^._x)) (fromIntegral y * (squareSize^._y))
        area = polygon [V2 0 0, V2 (squareSize^._x) 0, squareSize, V2 0 (squareSize^._y)]

    mouseClicked (Button _) = True
    mouseClicked _ = False

