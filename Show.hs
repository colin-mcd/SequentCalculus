module Show where
import Types
import Helpers

data Sequent = Sequent Cedent Cedent

tpSeq :: ProofS -> Sequent
tpSeq = uncurry Sequent . typeof . expand

data ProofW = ProofW RuleLabel Sequent [ProofW]

texLabel :: RuleLabel -> String
texLabel RuleNegL = "$\\neg_l$"
texLabel RuleNegR = "$\\neg_r$"
texLabel RuleCut = "\textsc{Cut}"
texLabel RuleConjL = "$\\land_l$"
texLabel RuleConjR = "$\\land_r$"
texLabel RuleDisjL = "$\\lor_l$"
texLabel RuleDisjR = "$\\lor_r$"
texLabel RuleImpL = "$\\supset_l$"
texLabel RuleImpR = "$\\supset_r$"
texLabel _ = error "This shouldn't happen"


--typeofW :: ProofW -> (Cedent, Cedent)
--typeofW (ProofW rl cs xs) = cs

-- Collapses weak structural rules into one weak inference
proofS2W :: ProofS -> ProofW
proofS2W x = fst (h x) where
  h :: ProofS -> (ProofW, Maybe Sequent)
  h x@(ProofS rl cs ss xs)
    | rl `elem` weakRules =
      let [x'] = xs in -- all weak rules are unary
        (fst (h x'), Just (tpSeq x))
    | otherwise =
      let xws = map (\ x -> let (x', mtp) = h x in
                              maybe x' (\ tp -> ProofW RuleWeakeningL tp [x']) mtp) xs in
        (ProofW rl (tpSeq x) xws, Nothing)

instance Show Sequent where
  show (Sequent a s) = show a ++ " \\implies " ++ show s

instance Show ProofW where
  show (ProofW RuleLeaf tp []) = "\\AxiomC{" ++ show tp ++ "}"
  show (ProofW RuleWeakeningL tp [x]) =
    show x ++ "\n\\doubleLine\n\\UnaryInfC{" ++ show tp ++ "}"
  show (ProofW rl tp [x]) =
    show x ++ "\n\\RightLabel{\\scriptsize " ++ texLabel rl ++ "}\n\\UnaryInfC{" ++ show tp ++ "}"
  show (ProofW rl tp [x, y]) =
    show x ++ "\n" ++ show y ++ "\\RightLabel{\\scriptsize " ++ texLabel rl ++ "}\n\\BinaryInfC{" ++ show tp ++ "}"
