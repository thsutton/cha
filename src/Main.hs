module Main where

import           Interp
import           Term

#ifdef FLAG_coind
nat = Sum Unit (Var 0)
ten = Fold nat (last . take 3 $ (iterate InR (InL Unit)))

r = Rec nat (Case (Var 0) Z (Succ (Var 0))) ten
#endif

main :: IO ()
main = do
  putStrLn "hello world"
