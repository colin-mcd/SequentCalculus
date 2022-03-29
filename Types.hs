module Types where

type Atom = Int

data Sentence =
    Atom Atom
  | Neg Sentence
  | Conj Sentence Sentence
  | Disj Sentence Sentence
  | Imp Sentence Sentence
  deriving (Eq, Ord, Show)

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
  deriving (Eq, Ord, Show)

data RuleLabel = RuleLeaf | RuleCut | RuleExchangeL | RuleExchangeR | RuleContractionL | RuleContractionR | RuleWeakeningL | RuleWeakeningR | RuleNegL | RuleNegR | RuleConjL | RuleConjR | RuleDisjL | RuleDisjR | RuleImpL | RuleImpR
  deriving (Eq, Ord, Show)

data ProofS = ProofS RuleLabel [Cedent] [Sentence] [ProofS]
  deriving (Eq, Ord, Show)

foldProofS :: (RuleLabel -> [Cedent] -> [Sentence] -> [a] -> a) -> ProofS -> a
foldProofS f (ProofS rl cs ss ps) = f rl cs ss (foldProofS f <$> ps)

foldProofSS :: (RuleLabel -> [Cedent] -> [Sentence] -> [ProofS] -> [a] -> a) -> ProofS -> a
foldProofSS f (ProofS rl cs ss ps) = f rl cs ss ps (foldProofSS f <$> ps)
