module Main where
import Types
import Helpers
import Show()
import CutElim

main :: IO ()
main =
  let c = Imp (Conj (Neg (Disj (Atom "C") (Atom "A"))) (Imp (Imp (Atom "B") (Disj (Atom "C") (Atom "A"))) (Imp (Atom "C") (Disj (Atom "C") (Atom "A"))))) (Conj (Disj (Atom "C") (Atom "A")) (Neg (Atom "D")))
      l = leaf (Disj (Atom "C") (Atom "A"))
      l' = ensureValid l l
      x = cut (weakeningR c l') (weakeningL c l')
      x' = ensureValid x x
      xcf = ensureValid x' (cutElim x')
  in
    putStrLn (show x') >>
    putStrLn (show xcf)

