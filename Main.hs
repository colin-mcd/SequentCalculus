module Main where
import Types
import Helpers
import Show
import CutElim


main :: IO ()
main =
  let c = Imp (Conj (Atom "A") (Atom "B")) (Disj (Atom "C") (Neg (Atom "D")))
      l = Leaf "E"
      x = cut (weakeningR c l) (weakeningL c l)
      xcf = cutElim x
  in
    ensureValid x $
    ensureValid xcf $
    putStrLn (show x) >>
    putStrLn (show xcf)

