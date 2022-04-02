module Main where
import Types
import Helpers
import Show()
import CutElim

ensureValid :: Proof -> x -> x
ensureValid = maybe id (\ x -> error ("Invalid inference:\n" ++ show x)) . proofValid

main :: IO ()
main =
  let c = Imp (Conj (Atom "A") (Atom "B")) (Disj (Atom "C") (Neg (Atom "D")))
      l = Leaf "E"
      x = cut (weakeningR c l) (weakeningL c l)
      xcf = cutElim x
  in
--    ensureValid x $
--    ensureValid xcf $
    putStrLn (show x) >>
    putStrLn (show xcf)

