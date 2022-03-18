module Helpers where
open import lib
open import Types

isCutFree : ∀ {Γ Δ} → (Γ ==> Δ) → Bool
isCutFree (leaf A) = true
isCutFree (cut Γ Δ A x1 x2) = false
isCutFree (exchangeₗ Γ Π Δ A B x) = isCutFree x
isCutFree (exchangeᵣ Γ Π Δ A B x) = isCutFree x
isCutFree (contractionₗ Γ Δ A x) = isCutFree x
isCutFree (contractionᵣ Γ Δ A x) = isCutFree x
isCutFree (weakeningₗ Γ Δ A x) = isCutFree x
isCutFree (weakeningᵣ Γ Δ A x) = isCutFree x
isCutFree (¬ₗ Γ Δ A x) = isCutFree x
isCutFree (¬ᵣ Γ Δ A x) = isCutFree x
isCutFree (∧ₗ Γ Δ A B x) = isCutFree x
isCutFree (∧ᵣ Γ Δ A B x1 x2) = isCutFree x1 && isCutFree x2
isCutFree (∨ₗ Γ Δ A B x1 x2) = isCutFree x1 && isCutFree x2
isCutFree (∨ᵣ Γ Δ A B x) = isCutFree x
isCutFree (⊃ₗ Γ Δ A B x1 x2) = isCutFree x1 && isCutFree x2
isCutFree (⊃ᵣ Γ Δ A B x) = isCutFree x

sentenceDepth : Sentence → ℕ
sentenceDepth (atom x) = 0
sentenceDepth (¬ s) = 1 + sentenceDepth s
sentenceDepth (s1 ∨ s2) = 1 + max (sentenceDepth s1) (sentenceDepth s2)
sentenceDepth (s1 ∧ s2) = 1 + max (sentenceDepth s1) (sentenceDepth s2)
sentenceDepth (s1 ⊃ s2) = 1 + max (sentenceDepth s1) (sentenceDepth s2)

proofDepth :  ∀{Γ Δ} → (Γ ==> Δ) → ℕ
proofDepth (leaf _) = 0
proofDepth (cut _ _ _ p1 p2) = max (proofDepth p1) (proofDepth p2) + 1
proofDepth (exchangeₗ _ _ _ _ _ p) = proofDepth p -- + 1
proofDepth (exchangeᵣ _ _ _ _ _ p) = proofDepth p -- + 1
proofDepth (contractionₗ _ _ _ p) = proofDepth p -- + 1
proofDepth (contractionᵣ _ _ _ p) = proofDepth p -- + 1
proofDepth (weakeningₗ _ _ _ p) = proofDepth p -- + 1
proofDepth (weakeningᵣ _ _ _ p) = proofDepth p -- + 1
proofDepth (¬ₗ _ _ _ p) = proofDepth p + 1
proofDepth (¬ᵣ _ _ _ p) = proofDepth p + 1
proofDepth (∧ₗ _ _ _ _ p) = proofDepth p + 1
proofDepth (∧ᵣ _ _ _ _ p1 p2) = max (proofDepth p1) (proofDepth p2) + 1
proofDepth (∨ₗ _ _ _ _ p1 p2) = max (proofDepth p1) (proofDepth p2) + 1
proofDepth (∨ᵣ _ _ _ _ p) = proofDepth p + 1
proofDepth (⊃ₗ _ _ _ _ p1 p2) = max (proofDepth p1) (proofDepth p2) + 1
proofDepth (⊃ᵣ _ _ _ _ p) = proofDepth p + 1

maxCutDepth :  ∀{Γ Δ} → (Γ ==> Δ) → ℕ
maxCutDepth (leaf _) = 0
maxCutDepth p@(cut _ _ _ _ _) = proofDepth p
maxCutDepth (exchangeₗ _ _ _ _ _ p) = maxCutDepth p
maxCutDepth (exchangeᵣ _ _ _ _ _ p) = maxCutDepth p
maxCutDepth (contractionₗ _ _ _ p) = maxCutDepth p
maxCutDepth (contractionᵣ _ _ _ p) = maxCutDepth p
maxCutDepth (weakeningₗ _ _ _ p) = maxCutDepth p
maxCutDepth (weakeningᵣ _ _ _ p) = maxCutDepth p
maxCutDepth (¬ₗ _ _ _ p) = maxCutDepth p
maxCutDepth (¬ᵣ _ _ _ p) = maxCutDepth p
maxCutDepth (∧ₗ _ _ _ _ p) = maxCutDepth p
maxCutDepth (∧ᵣ _ _ _ _ p1 p2) = max (maxCutDepth p1) (maxCutDepth p2)
maxCutDepth (∨ₗ _ _ _ _ p1 p2) = max (maxCutDepth p1) (maxCutDepth p2)
maxCutDepth (∨ᵣ _ _ _ _ p) = maxCutDepth p
maxCutDepth (⊃ₗ _ _ _ _ p1 p2) = max (maxCutDepth p1) (maxCutDepth p2)
maxCutDepth (⊃ᵣ _ _ _ _ p) = maxCutDepth p
