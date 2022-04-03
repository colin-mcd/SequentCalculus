module Main where
import Types
import Helpers
import Show()
import CutElim

main :: IO ()
main =
  let --c = Conj (Atom "A") (Atom "B")
      c = Imp (Conj (Atom "A") (Atom "B")) (Disj (Atom "C") (Neg (Atom "D")))
      l = Leaf "E"
      x = cut (weakeningR c l) (weakeningL c l)
      x' = ensureValid x x
      xcf = ensureValid x' (cutElim x')
  in
    putStrLn (show x') >>
    putStrLn (show xcf)

