module Main where
import Types
import Helpers
import Show()
import CutElim

main :: IO ()
main =
  let --c = Conj (Atom "A") (Atom "B")
      c = Imp (Conj (Atom "A") (Atom "B")) (Disj (Atom "C") (Neg (Atom "D")))
      l = leaf (Disj (Atom "C") (Neg (Atom "D")))
--      r = leaf (Conj (Atom "A") (Atom "B"))
      l' = ensureValid l l
--      r' = ensureValid r r
      x = cut (weakeningR c l') (weakeningL c l')
      x' = ensureValid x x
      xcf = ensureValid x' (cutElim x')
  in
    putStrLn (show x') >>
    putStrLn (show xcf)

