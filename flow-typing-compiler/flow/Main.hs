{-# LANGUAGE UnboxedTuples #-}

module Main where

import Examples qualified
import FlowPrelude (World (..))
import Prelude.Linear as L
import System.IO.Linear as IO

main :: L.IO ()
main = withLinearIO (IO (\w -> case Examples.main (World w) of ((), World w') -> (# w', Ur () #)))
