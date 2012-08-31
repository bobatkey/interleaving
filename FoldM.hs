module FoldM where

import System.IO

foldrM n c []     = n
foldrM n c (x:xs) = foldrM n c xs >>= c x


data List' m a = Nil | Cons a (List m a)
newtype List m a = List (m (List' m a))

hGetContents2 :: Handle -> List IO Char
hGetContents2 h = List (do isEOF <- hIsEOF h
                           if isEOF then return Nil
                           else do c <- hGetChar h
                                   return (Cons c (hGetContents2 h)))