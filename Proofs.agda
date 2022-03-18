module Proofs where
open import lib
open import Types
open import Helpers
open import CutElim

{-

infix 0 _=/=>_

_=/=>_ : Cedent → Cedent → Set
_=/=>_ Γ Δ = Σ (Γ ==> Δ) (λ p → isCutFree p ≡ true)



CutTree : Cedent → Cedent → ℕ → Set
CutTree Γ Δ d = Σ (Γ ==> Δ) (λ p → maxCutDepth p ≤ d)

whichMax : (m n : ℕ) → (max m n ≡ m × n ≤ m) ⊎ (max m n ≡ n × m ≤ n)
whichMax zero zero = inj₁ (refl , z≤n)
whichMax zero (suc n) = inj₂ (refl , z≤n)
whichMax (suc m) zero = inj₁ (refl , z≤n)
whichMax (suc m) (suc n) with whichMax m n
...| inj₁ (h , g) rewrite h = inj₁ (refl , {!!})
...| inj₂ (h , g) rewrite h = inj₂ (refl , {!!})

CutTree0 : ∀ {Γ Δ : Cedent} → (ct : CutTree Γ Δ 0) → (isCutFree (proj₁ ct) ≡ true)
CutTree0 {.([ A ])} {.([ A ])} (leaf A , d) = refl
CutTree0 {.(Γ ¸ B ¸ A ¸ Π)} {Δ} (exchangeₗ Γ Π .Δ A B p , d) = CutTree0 (p , d)
CutTree0 {Γ} {.(Δ ¸ B ¸ A ¸ Π)} (exchangeᵣ .Γ Π Δ A B p , d) = CutTree0 (p , d)
CutTree0 {.(A ¸ Γ)} {Δ} (contractionₗ Γ .Δ A p , d) = CutTree0 (p , d)
CutTree0 {Γ} {.(Δ ¸ A)} (contractionᵣ .Γ Δ A p , d) = CutTree0 (p , d)
CutTree0 {.(A ¸ Γ)} {Δ} (weakeningₗ Γ .Δ A p , d) = CutTree0 (p , d)
CutTree0 {Γ} {.(Δ ¸ A)} (weakeningᵣ .Γ Δ A p , d) = CutTree0 (p , d)
CutTree0 {.(¬ A ¸ Γ)} {Δ} (¬ₗ Γ .Δ A p , d) = CutTree0 (p , d)
CutTree0 {Γ} {.(Δ ¸ ¬ A)} (¬ᵣ .Γ Δ A p , d) = CutTree0 (p , d)
CutTree0 {.(A ∧ B ¸ Γ)} {Δ} (∧ₗ Γ .Δ A B p , d) = CutTree0 (p , d)
CutTree0 {Γ} {.(Δ ¸ A ∧ B)} (∧ᵣ .Γ Δ A B p1 p2 , d) with whichMax (maxCutDepth p1) (maxCutDepth p2)
...| inj₁ (h , g) rewrite h rewrite n≤0⇒n≡0 d = {!d!}
...| inj₂ (h , g) rewrite h = {!!}
CutTree0 {.(A ∨ B ¸ Γ)} {Δ} (∨ₗ Γ .Δ A B p1 p2 , d) = {!!}
CutTree0 {Γ} {.(Δ ¸ A ∨ B)} (∨ᵣ .Γ Δ A B p , d) = CutTree0 (p , d)
CutTree0 {.((A ⊃ B) ¸ Γ)} {Δ} (⊃ₗ Γ .Δ A B p1 p2 , d) = {!!}
CutTree0 {Γ} {.(Δ ¸ (A ⊃ B))} (⊃ᵣ .Γ Δ A B p , d) = CutTree0 (p , d)

cutLower : (Γ Δ : Cedent) (d : ℕ) → CutTree Γ Δ d → CutTree Γ Δ (pred d)
cutLower .([ A ]) .([ A ]) d (leaf A , z≤n) = leaf A , z≤n
cutLower Γ Δ d (cut .Γ .Δ A x x₁ , p) = {!!}
cutLower .(Γ ¸ B ¸ A ¸ Π) Δ d (exchangeₗ Γ Π .Δ A B x , p) = {!!}
cutLower Γ .(Δ ¸ B ¸ A ¸ Π) d (exchangeᵣ .Γ Π Δ A B x , p) = {!!}
cutLower .(A ¸ Γ) Δ d (contractionₗ Γ .Δ A x , p) = {!!}
cutLower Γ .(Δ ¸ A) d (contractionᵣ .Γ Δ A x , p) = {!!}
cutLower .(A ¸ Γ) Δ d (weakeningₗ Γ .Δ A x , p) = {!!}
cutLower Γ .(Δ ¸ A) d (weakeningᵣ .Γ Δ A x , p) = {!!}
cutLower .(¬ A ¸ Γ) Δ d (¬ₗ Γ .Δ A x , p) = {!!}
cutLower Γ .(Δ ¸ ¬ A) d (¬ᵣ .Γ Δ A x , p) = {!!}
cutLower .(A ∧ B ¸ Γ) Δ d (∧ₗ Γ .Δ A B x , p) = {!!}
cutLower Γ .(Δ ¸ A ∧ B) d (∧ᵣ .Γ Δ A B x x₁ , p) = {!!}
cutLower .(A ∨ B ¸ Γ) Δ d (∨ₗ Γ .Δ A B x x₁ , p) = {!!}
cutLower Γ .(Δ ¸ A ∨ B) d (∨ᵣ .Γ Δ A B x , p) = {!!}
cutLower .((A ⊃ B) ¸ Γ) Δ d (⊃ₗ Γ .Δ A B x x₁ , p) = {!!}
cutLower Γ .(Δ ¸ (A ⊃ B)) d (⊃ᵣ .Γ Δ A B x , p) = {!!}

cutReduce : (Γ Δ : Cedent) (A : Sentence) (x1 : (Γ ==> Δ ¸ A)) (x2 : (A ¸ Γ ==> Δ)) → CutTree Γ Δ (max (proofDepth x1) (proofDepth x2))
cutReduce Γ Δ (atom m) x1 x2 = {!!}
cutReduce Γ Δ (¬ A) x1 x2 = {!!}
cutReduce Γ Δ (A ∨ A₁) x1 x2 = {!!}
cutReduce Γ Δ (A ∧ A₁) x1 x2 = {!!}
cutReduce Γ Δ (A ⊃ A₁) x1 x2 = {!!}

CutElimCorrect : (Γ Δ : Cedent) → (p : Γ ==> Δ) → (isCutFree (cutFree Γ Δ p) ≡ true)
CutElimCorrect .([ A ]) .([ A ]) (leaf A) = {!!}
CutElimCorrect Γ Δ (cut .Γ .Δ A p p₁) = {!!}
CutElimCorrect .(Γ ¸ B ¸ A ¸ Π) Δ (exchangeₗ Γ Π .Δ A B p) = {!!}
CutElimCorrect Γ .(Δ ¸ B ¸ A ¸ Π) (exchangeᵣ .Γ Π Δ A B p) = {!!}
CutElimCorrect .(A ¸ Γ) Δ (contractionₗ Γ .Δ A p) = {!!}
CutElimCorrect Γ .(Δ ¸ A) (contractionᵣ .Γ Δ A p) = {!!}
CutElimCorrect .(A ¸ Γ) Δ (weakeningₗ Γ .Δ A p) = {!!}
CutElimCorrect Γ .(Δ ¸ A) (weakeningᵣ .Γ Δ A p) = {!!}
CutElimCorrect .(¬ A ¸ Γ) Δ (¬ₗ Γ .Δ A p) = {!!}
CutElimCorrect Γ .(Δ ¸ ¬ A) (¬ᵣ .Γ Δ A p) = {!!}
CutElimCorrect .(A ∧ B ¸ Γ) Δ (∧ₗ Γ .Δ A B p) = {!!}
CutElimCorrect Γ .(Δ ¸ A ∧ B) (∧ᵣ .Γ Δ A B p p₁) = {!!}
CutElimCorrect .(A ∨ B ¸ Γ) Δ (∨ₗ Γ .Δ A B p p₁) = {!!}
CutElimCorrect Γ .(Δ ¸ A ∨ B) (∨ᵣ .Γ Δ A B p) = {!!}
CutElimCorrect .((A ⊃ B) ¸ Γ) Δ (⊃ₗ Γ .Δ A B p p₁) = {!!}
CutElimCorrect Γ .(Δ ¸ (A ⊃ B)) (⊃ᵣ .Γ Δ A B p) = {!!}

-}
