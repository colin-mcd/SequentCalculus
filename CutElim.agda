module CutElim where
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

infix 0 _==>'_

_==>'_ : Cedent → Cedent → Set
Γ ==>' Δ = Σ (Γ ==> Δ) (λ p → isCutFree p ≡ true)

