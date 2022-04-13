module Show where
import Types

data EmphSent = EmphSent Sentence Bool
type EmphCedent = [EmphSent]
data Sequent = Sequent EmphCedent EmphCedent

tpSeq :: ProofS -> Sequent
tpSeq = typeofEmph . expand

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
  weaken (p, Just tp) = ProofW Nothing (delemph tp) [p]
  
  h :: ProofS -> (ProofW, Maybe Sequent)
  h x@(ProofS rl cs ss xs)
    | rl `elem` weakRules && collapseWeakRules =
      let [x'] = xs in -- all weak rules are unary
        (fst (h x'), Just (tpSeq x))
    | otherwise =
      let xws = map (weaken . h) xs in
        (ProofW (Just rl) (tpSeq x) xws, Nothing)

instance Show EmphSent where
  show (EmphSent s False) = show s
  show (EmphSent s True) = "{\\color{red} " ++ show s ++ "}"
--  show (EmphSent s True) = "\\mathbf{" ++ show s ++ "}"

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


emph' :: Bool -> [Sentence] -> [EmphSent]
emph' e = map $ \ x -> EmphSent x e
emph = emph' True
noemph = emph' False
delemph' :: [EmphSent] -> [EmphSent]
delemph' = map $ \ (EmphSent x _) -> EmphSent x False
delemph :: Sequent -> Sequent
delemph (Sequent a s) = Sequent (delemph' a) (delemph' s)


typeofEmph :: Proof -> Sequent
typeofEmph (Leaf a) = Sequent (noemph [Atom a]) (noemph [Atom a])
typeofEmph (Cut gamma delta a x1 x2) = Sequent (noemph gamma) (noemph delta)
typeofEmph (ExchangeL gamma delta pi a b x) = Sequent (noemph gamma ++ emph [b, a] ++ noemph delta) (noemph pi)
typeofEmph (ExchangeR gamma delta pi a b x) = Sequent (noemph gamma) (noemph delta ++ emph [b, a] ++ noemph pi)
typeofEmph (ContractionL gamma delta a x) = Sequent (emph [a] ++ noemph gamma) (noemph delta)
typeofEmph (ContractionR gamma delta a x) = Sequent (noemph gamma) (noemph delta ++ emph [a])
typeofEmph (WeakeningL gamma delta a x) = Sequent (emph [a] ++ noemph gamma) (noemph delta)
typeofEmph (WeakeningR gamma delta a x) = Sequent (noemph gamma) (noemph delta ++ emph [a])
typeofEmph (NegL gamma delta a x) = Sequent (emph [Neg a] ++ noemph gamma) (noemph delta)
typeofEmph (NegR gamma delta a x) = Sequent (noemph gamma) (noemph delta ++ emph [Neg a])
typeofEmph (ConjL gamma delta a b x) = Sequent (emph [Conj a b] ++ noemph gamma) (noemph delta)
typeofEmph (ConjR gamma delta a b x1 x2) = Sequent (noemph gamma) (noemph delta ++ emph [Conj a b])
typeofEmph (DisjL gamma delta a b x1 x2) = Sequent (emph [Disj a b] ++ noemph gamma) (noemph delta)
typeofEmph (DisjR gamma delta a b x) = Sequent (noemph gamma) (noemph delta ++ emph [Disj a b])
typeofEmph (ImpL gamma delta a b x1 x2) = Sequent (emph [Imp a b] ++ noemph gamma) (noemph delta)
typeofEmph (ImpR gamma delta a b x) = Sequent (noemph gamma) (noemph delta ++ emph [Imp a b])
