{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE UnboxedTuples #-}

module FlowPrelude where

import Control.Monad (Monad (..))
import Data.Bifunctor.Linear (first)
import GHC.Exts (RealWorld, State#)
import GHC.IO.IOMode (IOMode (ReadMode, WriteMode))
import Prelude.Linear
import System.IO qualified (
  Handle,
  IO,
  SeekMode (AbsoluteSeek),
  hClose,
  hGetChar,
  hIsEOF,
  hPutStr,
  hSeek,
  openFile,
 )
import System.IO.Linear (IO (..))
import System.IO.Linear qualified

data World = World (State# RealWorld)

newtype Handle = Handle (Ur System.IO.Handle)

unboxIO :: System.IO.Linear.IO a %1 -> World %1 -> (a, World)
unboxIO (IO f) (World w) = case f w of (# w', x #) -> (x, World w')

print :: (Movable a, Show a) => a %1 -> World %1 -> ((), World)
print s = case move s of Ur t -> unboxIO (System.IO.Linear.fromSystemIO (Prelude.Linear.print t))

putStrLn :: String %1 -> World %1 -> ((), World)
putStrLn s = case move s of Ur t -> unboxIO (System.IO.Linear.fromSystemIO (Prelude.Linear.putStrLn t))

openFile :: String %1 -> World %1 -> (Handle, World)
openFile s = case move s of
  Ur t ->
    first Handle
      . unboxIO (System.IO.Linear.fromSystemIOU (System.IO.openFile t ReadMode))

truncateFile :: String %1 -> World %1 -> (Handle, World)
truncateFile s = case move s of
  Ur t ->
    first Handle
      . unboxIO (System.IO.Linear.fromSystemIOU (System.IO.openFile t WriteMode))

closeFile :: Handle %1 -> World %1 -> ((), World)
closeFile (Handle (Ur h)) = unboxIO (System.IO.Linear.fromSystemIO (System.IO.hClose h))

-- | Get the contents of a file without closing it. Inefficient but useful for demos.
hGetContentsStrict :: System.IO.Handle -> System.IO.IO String
hGetContentsStrict h = do
  System.IO.hSeek h System.IO.AbsoluteSeek 0
  go h ""
 where
  go :: System.IO.Handle -> String -> System.IO.IO String
  go h' s =
    System.IO.hIsEOF h' >>= \case
      True -> return s
      False -> System.IO.hGetChar h' >>= \c -> go h' (c : s)

readFile :: (World, Handle) %1 -> (String, (World, Handle))
readFile (w, Handle (Ur h)) = case unboxIO (System.IO.Linear.fromSystemIO (hGetContentsStrict h)) w of
  (s, w') -> (s, (w', Handle (Ur h)))

writeFile :: String %1 -> (World, Handle) %1 -> ((), (World, Handle))
writeFile s (w, Handle (Ur h)) = case move s of
  Ur s' -> case unboxIO (System.IO.Linear.fromSystemIO (System.IO.hPutStr h s')) w of
    (s'', w') -> (s'', (w', Handle (Ur h)))

div :: Int %1 -> Int %1 -> Int
div x y = case (move x, move y) of (Ur x', Ur y') -> x' `Prelude.Linear.div` y'
