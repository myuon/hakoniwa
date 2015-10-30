{-# LANGUAGE OverloadedStrings, RankNTypes #-}
module JSArray where

import Haste
import Haste.Foreign

newtype Array a = Array JSAny

fromList :: ToAny a => [a] -> Array a
fromList = Array . listToAny

toList :: FromAny a => Array a -> IO [a]
toList (Array a) = listFromAny a

(!) :: (FFI a, FromAny a) => Array a -> Int -> IO a
(!) (Array a) i = ffi "(function(a,i){ return a[i]; })" a i

update :: (ToAny a, FFI a) => Int -> a -> Array a -> IO (Array a)
update i x (Array a) = Array <$> ffi "(function(i,x,a){ a[i] = x; return a; })" i x a

insert :: (ToAny a, FFI a) => Int -> a -> Array a -> IO (Array a)
insert = update

keys :: Array a -> IO [Int]
keys (Array a) = ffi "(function(a){ \
\ ixs = Object.keys(new Int8Array(a.length - 1)).map(Number); \
\ keys = new Array(); \
\ for(var i in ixs){ if(a[i] === undefined) keys.push(i); } \
\ return keys; })" a

keysUnder :: Int -> Array a -> IO [Int]
keysUnder n (Array a) = ffi "(function(n,a){ \
\ ixs = Object.keys(new Int8Array(n - 1)).map(Number); \
\ keys = new Array(); \
\ for(var i in ixs){ if(a[i] === undefined) keys.push(i); } \
\ return keys; })" n a

elems :: (FFI a, FromAny a) => Array a -> IO [a]
elems a = mapM (a !) =<< keys a

elemsUnder :: (FFI a, FromAny a) => Int -> Array a -> IO [a]
elemsUnder n a = mapM (a !) =<< keysUnder n a
