module Types where

type Atom = String

data Sentence =
    Atom Atom
  | Neg Sentence
  | Conj Sentence Sentence
  | Disj Sentence Sentence
  | Imp Sentence Sentence
  deriving (Eq, Ord)

{-instance Eq Sentence where
  Atom v == Atom u = v == u
  Neg s == Neg t = s == t
  Conj s1 s2 == Conj t1 t2 = s1 == t1 && s2 == t2
  Disj s1 s2 == Disj t1 t2 = s1 == t1 && s2 == t2
  Imp s1 s2 == Imp t1 t2 = s1 == t1 && s2 == t2
  _ == _ = False-}

type Cedent = [Sentence]

data Proof =
  -- leaf : (A : Atom) → ([ atom A ] ==> [ atom A ])
    Leaf Atom
  
  -- cut : (Γ Δ : Cedent) (A : Sentence) →
  --  (Γ ==> Δ ¸ A) → (A ¸ Γ ==> Δ) →
  --  (Γ ==> Δ)
  | Cut Cedent Cedent Sentence Proof Proof

  -- exchangeₗ : (Γ Δ Π : Cedent) (A B : Sentence) →
  --  (Γ ¸ A ¸ B ¸ Δ ==> Π) →
  --  (Γ ¸ B ¸ A ¸ Δ ==> Π)
  | ExchangeL Cedent Cedent Cedent Sentence Sentence Proof

  -- exchangeᵣ : (Γ Δ Π : Cedent) (A B : Sentence) →
  --  (Γ ==> Δ ¸ A ¸ B ¸ Π) →
  --  (Γ ==> Δ ¸ B ¸ A ¸ Π)
  | ExchangeR Cedent Cedent Cedent Sentence Sentence Proof

  -- contractionₗ : (Γ Δ   : Cedent) (A   : Sentence) →
  --  (A ¸ A ¸ Γ ==> Δ) →
  --  (A ¸ Γ ==> Δ)
  | ContractionL Cedent Cedent Sentence Proof

  -- contractionᵣ : (Γ Δ : Cedent) (A : Sentence) →
  --  (Γ ==> Δ ¸ A ¸ A) →
  --  (Γ ==> Δ ¸ A)
  | ContractionR Cedent Cedent Sentence Proof

  -- weakeningₗ : (Γ Δ : Cedent) (A : Sentence) →
  --  (Γ ==> Δ) →
  --  (A ¸ Γ ==> Δ)
  | WeakeningL Cedent Cedent Sentence Proof

  -- weakeningᵣ : (Γ Δ : Cedent) (A : Sentence) →
  --  (Γ ==> Δ) →
  --  (Γ ==> Δ ¸ A)
  | WeakeningR Cedent Cedent Sentence Proof


  -- ¬ₗ : (Γ Δ : Cedent) (A : Sentence) →
  --  (Γ ==> Δ ¸ A) →
  --  (¬ A ¸ Γ ==> Δ)
  | NegL Cedent Cedent Sentence Proof

  -- ¬ᵣ : (Γ Δ : Cedent) (A : Sentence) →
  --  (A ¸ Γ ==> Δ) →
  --  (Γ ==> Δ ¸ ¬ A)
  | NegR Cedent Cedent Sentence Proof

  -- ∧ₗ : (Γ Δ : Cedent) (A B : Sentence) →
  --  (A ¸ B ¸ Γ ==> Δ) →
  --  (A ∧ B ¸ Γ ==> Δ)
  | ConjL Cedent Cedent Sentence Sentence Proof

  -- ∧ᵣ : (Γ Δ : Cedent) (A B : Sentence) →
  --  (Γ ==> Δ ¸ A) → (Γ ==> Δ ¸ B) →
  --  (Γ ==> Δ ¸ A ∧ B)
  | ConjR Cedent Cedent Sentence Sentence Proof Proof

  -- ∨ₗ : (Γ Δ : Cedent) (A B : Sentence) →
  --  (A ¸ Γ ==> Δ) → (B ¸ Γ ==> Δ) →
  --  (A ∨ B ¸ Γ ==> Δ)
  | DisjL Cedent Cedent Sentence Sentence Proof Proof

  -- ∨ᵣ : (Γ Δ : Cedent) (A B : Sentence) →
  --  (Γ ==> Δ ¸ A ¸ B) →
  --  (Γ ==> Δ ¸ A ∨ B)
  | DisjR Cedent Cedent Sentence Sentence Proof

  -- ⊃ₗ : (Γ Δ : Cedent) (A B : Sentence) →
  --  (Γ ==> Δ ¸ A) → (B ¸ Γ ==> Δ) →
  --  (A ⊃ B ¸ Γ ==> Δ)
  | ImpL Cedent Cedent Sentence Sentence Proof Proof

  -- ⊃ᵣ : (Γ Δ : Cedent) (A B : Sentence) →
  --  (A ¸ Γ ==> Δ ¸ B) →
  --  (Γ ==> Δ ¸ A ⊃ B)
  | ImpR Cedent Cedent Sentence Sentence Proof
  deriving (Eq, Ord)

typeof :: Proof -> (Cedent, Cedent)
typeof (Leaf a) = ([Atom a], [Atom a])
typeof (Cut gamma delta a x1 x2) = ((gamma), (delta))
typeof (ExchangeL gamma delta pi a b x) = ((gamma ++ [b, a] ++ delta), (pi))
typeof (ExchangeR gamma delta pi a b x) = ((gamma), (delta ++ [b, a] ++ pi))
typeof (ContractionL gamma delta a x) = (([a] ++ gamma), (delta))
typeof (ContractionR gamma delta a x) = ((gamma), (delta ++ [a]))
typeof (WeakeningL gamma delta a x) = (([a] ++ gamma), (delta))
typeof (WeakeningR gamma delta a x) = ((gamma), (delta ++ [a]))
typeof (NegL gamma delta a x) = (([Neg a] ++ gamma), (delta))
typeof (NegR gamma delta a x) = ((gamma), (delta ++ [Neg a]))
typeof (ConjL gamma delta a b x) = (([Conj a b] ++ gamma), (delta))
typeof (ConjR gamma delta a b x1 x2) = ((gamma), (delta ++ [Conj a b]))
typeof (DisjL gamma delta a b x1 x2) = (([Disj a b] ++ gamma), (delta))
typeof (DisjR gamma delta a b x) = ((gamma), (delta ++ [Disj a b]))
typeof (ImpL gamma delta a b x1 x2) = (([Imp a b] ++ gamma), (delta))
typeof (ImpR gamma delta a b x) = ((gamma), (delta ++ [Imp a b]))

data RuleLabel = RuleLeaf | RuleCut | RuleExchangeL | RuleExchangeR | RuleContractionL | RuleContractionR | RuleWeakeningL | RuleWeakeningR | RuleNegL | RuleNegR | RuleConjL | RuleConjR | RuleDisjL | RuleDisjR | RuleImpL | RuleImpR
  deriving (Eq, Ord)

data ProofS = ProofS RuleLabel [Cedent] [Sentence] [ProofS]
  deriving (Eq, Ord)

foldProofS :: (RuleLabel -> [Cedent] -> [Sentence] -> [a] -> a) -> ProofS -> a
foldProofS f (ProofS rl cs ss ps) = f rl cs ss (foldProofS f <$> ps)

foldProofSS :: (RuleLabel -> [Cedent] -> [Sentence] -> [ProofS] -> [a] -> a) -> ProofS -> a
foldProofSS f (ProofS rl cs ss ps) = f rl cs ss ps (foldProofSS f <$> ps)

simplify :: Proof -> ProofS
simplify (Leaf a) = (ProofS RuleLeaf [] [Atom a] [])
simplify (Cut g d a x1 x2) = (ProofS RuleCut [g, d] [a] [simplify x1, simplify x2])
simplify (ExchangeL g d p a b x) = (ProofS RuleExchangeL [g, d, p] [a, b] [simplify x])
simplify (ExchangeR g d p a b x) = (ProofS RuleExchangeR [g, d, p] [a, b] [simplify x])
simplify (ContractionL g d a x) = (ProofS RuleContractionL [g, d] [a] [simplify x])
simplify (ContractionR g d a x) = (ProofS RuleContractionR [g, d] [a] [simplify x])
simplify (WeakeningL g d a x) = (ProofS RuleWeakeningL [g, d] [a] [simplify x])
simplify (WeakeningR g d a x) = (ProofS RuleWeakeningR [g, d] [a] [simplify x])
simplify (NegL g d a x) = (ProofS RuleNegL [g, d] [a] [simplify x])
simplify (NegR g d a x) = (ProofS RuleNegR [g, d] [a] [simplify x])
simplify (ConjL g d a b x) = (ProofS RuleConjL [g, d] [a, b] [simplify x])
simplify (ConjR g d a b x1 x2) = (ProofS RuleConjR [g, d] [a, b] [simplify x1, simplify x2])
simplify (DisjL g d a b x1 x2) = (ProofS RuleDisjL [g, d] [a, b] [simplify x1, simplify x2])
simplify (DisjR g d a b x) = (ProofS RuleDisjR [g, d] [a, b] [simplify x])
simplify (ImpL g d a b x1 x2) = (ProofS RuleImpL [g, d] [a, b] [simplify x1, simplify x2])
simplify (ImpR g d a b x) = (ProofS RuleImpR [g, d] [a, b] [simplify x])

expand :: ProofS -> Proof
expand (ProofS RuleLeaf [] [Atom a] []) = (Leaf a)
expand (ProofS RuleCut [g, d] [a] [x1, x2]) = (Cut g d a (expand x1) (expand x2))
expand (ProofS RuleExchangeL [g, d, p] [a, b] [x]) = (ExchangeL g d p a b (expand x))
expand (ProofS RuleExchangeR [g, d, p] [a, b] [x]) = (ExchangeR g d p a b (expand x))
expand (ProofS RuleContractionL [g, d] [a] [x]) = (ContractionL g d a (expand x))
expand (ProofS RuleContractionR [g, d] [a] [x]) = (ContractionR g d a (expand x))
expand (ProofS RuleWeakeningL [g, d] [a] [x]) = (WeakeningL g d a (expand x))
expand (ProofS RuleWeakeningR [g, d] [a] [x]) = (WeakeningR g d a (expand x))
expand (ProofS RuleNegL [g, d] [a] [x]) = (NegL g d a (expand x))
expand (ProofS RuleNegR [g, d] [a] [x]) = (NegR g d a (expand x))
expand (ProofS RuleConjL [g, d] [a, b] [x]) = (ConjL g d a b (expand x))
expand (ProofS RuleConjR [g, d] [a, b] [x1, x2]) = (ConjR g d a b (expand x1) (expand x2))
expand (ProofS RuleDisjL [g, d] [a, b] [x1, x2]) = (DisjL g d a b (expand x1) (expand x2))
expand (ProofS RuleDisjR [g, d] [a, b] [x]) = (DisjR g d a b (expand x))
expand (ProofS RuleImpL [g, d] [a, b] [x1, x2]) = (ImpL g d a b (expand x1) (expand x2))
expand (ProofS RuleImpR [g, d] [a, b] [x]) = (ImpR g d a b (expand x))


weakRules :: [RuleLabel]
weakRules = [RuleExchangeL, RuleExchangeR,
             RuleContractionL, RuleContractionR,
             RuleWeakeningL, RuleWeakeningR]

propRules :: [RuleLabel]
propRules = [RuleNegL, RuleNegR,
             RuleConjL, RuleConjR,
             RuleDisjL, RuleDisjR,
             RuleImpL, RuleImpR]

binaryRules :: [RuleLabel]
binaryRules = [RuleCut, RuleConjR, RuleDisjL, RuleImpL]

