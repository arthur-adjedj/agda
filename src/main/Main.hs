-- | Wrapper for "Agda.Main".
--
-- Agda is installed as a library. This module is used to build the
-- executable.

{-# LANGUAGE BangPatterns #-}


module Main (main) where

import Agda.Main ( runAgda )
import Prelude ( IO, pure )
import Agda.TypeChecking.Cumulativity

main :: IO ()
main = do
    let !foo = test_cumul2
    runAgda []
    
