{-# LANGUAGE OverloadedStrings, RankNTypes, FlexibleContexts #-}
module JSArray where

import Prelude as P
import Haste
import Haste.Foreign
import System.IO.Unsafe (unsafePerformIO)

newtype Array a = Array JSAny
type IntMap = Array

empty :: ToAny a => Array a
empty = fromList []

fromList :: ToAny a => [(Int, a)] -> Array a
fromList xs = unsafePerformIO $ Array <$> go xs where
  go = ffi "(function(xs){ \
\ var a = new Array(); \
\ for(var i = 0; i < xs.length; i ++){ a[i] = xs[i][1]; } \
\ return a; })"

size :: FromAny a => Array a -> Int
size = length . keys

(!) :: FromAny a => Array a -> Int -> a
(!) (Array a) i = unsafePerformIO $ ffi "(function(a,i){ return a[i]; })" a i

update :: ToAny a => Int -> a -> Array a -> Array a
update i x (Array a) = unsafePerformIO $ Array <$> ffi "(function(i,x,a){ a[i] = x; return a; })" i x a

insert :: ToAny a => Int -> a -> Array a -> Array a
insert = update

keys :: Array a -> [Int]
keys (Array a) = unsafePerformIO $ go a where
  go :: JSAny -> IO [Int]
  go = ffi "(function(a){ \
\ var keys = new Array(); \
\ for(var i = 0; i < a.length; i++){ if(a[i] !== undefined) keys.push(i); } \
\ return keys; })"

elems :: (FromAny a) => Array a -> [a]
elems a = fmap (a !) $ keys a

assocs :: (FromAny a) => Array a -> [(Int, a)]
assocs a = zip (keys a) (elems a)

delete :: FromAny a => Int -> Array a -> Array a
delete n (Array a) = unsafePerformIO $ Array <$> ffi "(function(n,a){ a[n] = undefined; return a; })"

filter :: (ToAny a, FromAny a) => (a -> Bool) -> Array a -> Array a
filter f = fromList . P.filter (f . snd) . assocs
