{-# LANGUAGE TypeApplications #-}
module Main where

import MyLib
import System.Mem
import GHC.Debug.Stub

main = withGhcDebug $ do
  encode "abc" ([1 :: Int .. 10])
  res <- decode @[Int] "abc"

  encode "abc" (FastString "a" : replicate 1000 (FastString "abc"))
  res <- decode @[FastString] "abc"

  print (take 3 res)

  encode "abc" ([Name (FastString "abc") 9, Name (FastString "abc") 9])
  res <- decode @[Name] "abc"

  print (take 3 res)

  encode "abc" (concat (replicate 1000 [IfTyConInfo 0 0, IfTyConInfo 0 1]))
  res <- decode @[IfTyConInfo] "abc"
  print res

  performMajorGC
  n <- getLine


  shared <- share (concat (map (IfTyConInfo 0 n)

  print (take 3 res)
