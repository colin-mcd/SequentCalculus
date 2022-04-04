module Show where
import Types

data Sequent = Sequent Cedent Cedent

tpSeq :: ProofS -> Sequent
tpSeq = uncurry Sequent . typeof . expand

data ProofW = ProofW (Maybe RuleLabel) Sequent [ProofW]

texLabel :: RuleLabel -> String
texLabel RuleNegL = "\\neg_l"
texLabel RuleNegR = "\\neg_r"
texLabel RuleCut = "\\textsc{Cut}"
texLabel RuleConjL = "\\land_l"
texLabel RuleConjR = "\\land_r"
texLabel RuleDisjL = "\\lor_l"
texLabel RuleDisjR = "\\lor_r"
texLabel RuleImpL = "\\supset_l"
texLabel RuleImpR = "\\supset_r"
texLabel RuleLeaf = ""
texLabel RuleExchangeL = "\\textsc{Exchange}_l"
texLabel RuleExchangeR = "\\textsc{Exchange}_r"
texLabel RuleWeakeningL = "\\textsc{Weakening}_l"
texLabel RuleWeakeningR = "\\textsc{Weakening}_r"
texLabel RuleContractionL = "\\textsc{Contraction}_l"
texLabel RuleContractionR = "\\textsc{Contraction}_r"

instance Show Sentence where
  show (Atom v) = v
  show (Neg x) = "(\\neg " ++ show x ++ ")"
  show (Conj x y) = "(" ++ show x ++ " \\land " ++ show y ++ ")"
  show (Disj x y) = "(" ++ show x ++ " \\lor " ++ show y ++ ")"
  show (Imp x y) = "(" ++ show x ++ " \\supset " ++ show y ++ ")"


--typeofW :: ProofW -> (Cedent, Cedent)
--typeofW (ProofW rl cs xs) = cs

-- Collapses weak structural rules into one weak inference
proofS2W :: Bool -> ProofS -> ProofW
proofS2W collapseWeakRules x = weaken (h x) where
  weaken :: (ProofW, Maybe Sequent) -> ProofW
  weaken (p, Nothing) = p
  weaken (p, Just tp) = ProofW Nothing tp [p]
  
  h :: ProofS -> (ProofW, Maybe Sequent)
  h x@(ProofS rl cs ss xs)
    | rl `elem` weakRules && collapseWeakRules =
      let [x'] = xs in -- all weak rules are unary
        (fst (h x'), Just (tpSeq x))
    | otherwise =
      let xws = map (weaken . h) xs in
        (ProofW (Just rl) (tpSeq x) xws, Nothing)


instance Show Sequent where
  show (Sequent a s) = delimitWith "," (map show a) ++ " \\longrightarrow " ++ delimitWith "," (map show s)

instance Show ProofW where
  show (ProofW (Just RuleLeaf) tp []) = "\\AxiomC{$" ++ show tp ++ "$}"
  show (ProofW Nothing tp [x]) =
    show x ++ "\n\\doubleLine\n\\UnaryInfC{$" ++ show tp ++ "$}"
  show (ProofW (Just rl) tp [x]) =
    show x ++ "\n\\RightLabel{\\scriptsize $" ++ texLabel rl ++ "$}\n\\UnaryInfC{$" ++ show tp ++ "$}"
  show (ProofW (Just rl) tp [x, y]) =
    show x ++ "\n" ++ show y ++ "\\RightLabel{\\scriptsize $" ++ texLabel rl ++ "$}\n\\BinaryInfC{$" ++ show tp ++ "$}"


showProof :: Bool -> Proof -> String
showProof verbose x =
  "\\begin{prooftree}\n" ++ show (proofS2W (not verbose) (simplify x)) ++ "\n\\end{prooftree}"
  
instance Show Proof where
  show  = showProof False

-- Concats a list of lists, adding a delimiter
-- Example: delimitWith ", " ["item 1", "item 2", "item 3"] = "item 1, item 2, item 3"
delimitWith :: [a] -> [[a]] -> [a]
delimitWith del [] = []
delimitWith del [as] = as
delimitWith del (h : t) = h ++ del ++ delimitWith del t
