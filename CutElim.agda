module CutElim where
open import lib
open import Types
open import Helpers

-- Deletes direct ancestors
deleteDAs : Sentence → Cedent → Cedent
deleteDAs A = mapMaybe λ B → if A =sentence B then nothing else just B

--foldlInd : ∀ {A : Set} {P : List A → Set} → P [] → ((a : A) → (l : List A) → P l → P (l ∷ʳ a)) → (l : List A) → P l
--foldlInd n c [] = n
--foldlInd n c (a ∷ l) = {!!}

--exchangesLₗ : ∀ {Γ Π Δ Λ : Cedent} {A : Sentence} → (Γ ¸ Π ¸ A ¸ Δ ==> Λ) → (Γ ¸ A ¸ Π ¸ Δ ==> Λ)
--exchangesLₗ {Γ} {[]} {Δ} {Λ} {A} p = p
--exchangesLₗ {Γ} {B ∷ Π} {Δ} {Λ} {A} p = {!exchangesLₗ {Γ ∷ʳ B} {Π} {} {} {A} (exchangeₗ ? ? ? ? ? !} -- Γ ¸ A ¸ B ∷ Π ¸ Δ ==> Λ

--++[] : ∀ {a} {A : Set a} → (l : List A) → l ++ [] ≡ l
--++[] [] = refl
--++[] (h ∷ t) rewrite ++[] t = refl

congF : ∀ {A : Set} {P : A → Set} {a b : A} → a ≡ b → P a → P b
congF p rewrite p = λ x → x

exchangesLₗ : ∀ {Γ Δ Π Λ : Cedent} {A : Sentence} → (Γ ¸ Δ ¸ A ¸ Π ==> Λ) → (Γ ¸ A ¸ Δ ¸ Π ==> Λ)
exchangesLₗ {Γ} {[]} {Π} {Λ} {A} p = p
exchangesLₗ {Γ} {B ∷ Δ} {Π} {Λ} {A} p =
  exchangeₗ Γ (Δ ++ Π) Λ B A (congF {P = λ x → x ==> Λ} (++-assoc Γ [ B ] (A ¸ Δ ¸ Π))
    (exchangesLₗ (congF {P = λ x → x ==> Λ} (sym (++-assoc Γ [ B ] (Δ ¸ A ¸ Π))) p)))

exchangesRₗ : ∀ {Γ Δ Π Λ : Cedent} {A : Sentence} → (Γ ¸ A ¸ Δ ¸ Π ==> Λ) → (Γ ¸ Δ ¸ A ¸ Π ==> Λ)
exchangesRₗ {Γ} {[]} {Π} {Λ} {A} p = p
exchangesRₗ {Γ} {B ∷ Δ} {Π} {Λ} {A} p rewrite sym (++-assoc Γ [ B ] (Δ ¸ A ¸ Π)) =
  exchangesRₗ {Γ ¸ B} {Δ} {Π} {Λ} {A} (h (exchangeₗ Γ (Δ ++ Π) Λ A B p))
  where
  h : (Γ ¸ B ¸ A ¸ Δ ++ Π ==> Λ) → ((Γ ¸ B) ¸ A ¸ Δ ¸ Π ==> Λ)
  h p'' rewrite ++-assoc Γ [ B ] (A ¸ Δ ¸ Π) = p''

exchangesRₗ' : ∀ {Γ Δ : Cedent} {A : Sentence} → (A ¸ Γ ==> Δ) → (Γ ¸ A ==> Δ)
exchangesRₗ' {Γ} {Δ} {A} p = exchangesRₗ {[]} {Γ} {[]} {Δ} {A} (congF {P = λ x → x ==> Δ} (sym (++-identityʳ (A ∷ Γ))) p)


cutReduce : ∀ {Γ Δ : Cedent} (A : Sentence) (Q : (Γ ==> Δ ¸ A)) (R : (A ¸ Γ ==> Δ)) → Γ ==> Δ
cutReduce (atom v) Q R =
  {!!}
cutReduce (¬ B) Q R =
  let Q' = mkQ' Q in
    {!!}
  where
  _⁻ : Cedent → Cedent
  _⁻ = deleteDAs (¬ B)
  mkQ' : ∀ {Π Λ : Cedent} → (Π ==> Λ) → (Π ¸ B ==> Λ ⁻)
  mkQ' (leaf C) = exchangeₗ [] [] [ atom C ] B (atom C) (weakeningₗ [ atom C ] [ atom C ] B (leaf C))
  mkQ' (cut _ _ C x x₁) = {!!}
  mkQ' (exchangeₗ Γ Π Δ C D x) rewrite (++-assoc Γ (D ¸ C ¸ Π) [ B ]) =
    exchangeₗ Γ (Π ∷ʳ B) (Δ ⁻) C D (congF {P = λ x → x ==> Δ ⁻} (++-assoc Γ (C ¸ D ¸ Π) [ B ]) (mkQ' x))
  mkQ' (exchangeᵣ Γ Π Δ C D x) = {!!}
  mkQ' (contractionₗ Γ Δ C x) = {!!}
  mkQ' (contractionᵣ Γ Δ C x) = {!!}
  mkQ' (weakeningₗ Γ Δ C x) = {!!}
  mkQ' (weakeningᵣ Γ Δ C x) = {!!}
  mkQ' (¬ₗ Γ Δ C x) = {!!}
  mkQ' (¬ᵣ Γ Δ C x) = {!!}
  mkQ' (∧ₗ Γ Δ C D x) = {!!}
  mkQ' (∧ᵣ Γ Δ C D x x₁) = {!!}
  mkQ' (∨ₗ Γ Δ C D x x₁) = {!!}
  mkQ' (∨ᵣ Γ Δ C D x) = {!!}
  mkQ' (⊃ₗ Γ Δ C D x x₁) = {!!}
  mkQ' (⊃ᵣ Γ Δ C D x) = {!!}
cutReduce (B ∨ C) Q R =
  {!!}
cutReduce (B ∧ C) Q R =
  {!!}
cutReduce (B ⊃ C) Q R =
  {!!}

-- Given a proof of greatest cut depth d+1, lower the max cut to depth d
cutLower : ∀ {Γ Δ : Cedent} → ℕ → Γ ==> Δ → Γ ==> Δ
cutLower d (leaf A) = leaf A
cutLower d (cut Γ Δ A x1 x2) =
  if suc d ≡ᵇ proofDepth (cut Γ Δ A x1 x2)
    then cutReduce A x1 x2
    else cut Γ Δ A (cutLower d x1) (cutLower d x2)
cutLower d (exchangeₗ Γ Π Δ A B x) = exchangeₗ Γ Π Δ A B (cutLower d x)
cutLower d (exchangeᵣ Γ Π Δ A B x) = exchangeᵣ Γ Π Δ A B (cutLower d x)
cutLower d (contractionₗ Γ Δ A x) = contractionₗ Γ Δ A (cutLower d x)
cutLower d (contractionᵣ Γ Δ A x) = contractionᵣ Γ Δ A (cutLower d x)
cutLower d (weakeningₗ Γ Δ A x) = weakeningₗ Γ Δ A (cutLower d x)
cutLower d (weakeningᵣ Γ Δ A x) = weakeningᵣ Γ Δ A (cutLower d x)
cutLower d (¬ₗ Γ Δ A x) = ¬ₗ Γ Δ A (cutLower d x)
cutLower d (¬ᵣ Γ Δ A x) = ¬ᵣ Γ Δ A (cutLower d x)
cutLower d (∧ₗ Γ Δ A B x) = ∧ₗ Γ Δ A B (cutLower d x)
cutLower d (∧ᵣ Γ Δ A B x1 x2) = ∧ᵣ Γ Δ A B (cutLower d x1) (cutLower d x2)
cutLower d (∨ₗ Γ Δ A B x1 x2) = ∨ₗ Γ Δ A B (cutLower d x1) (cutLower d x2)
cutLower d (∨ᵣ Γ Δ A B x) = ∨ᵣ Γ Δ A B (cutLower d x)
cutLower d (⊃ₗ Γ Δ A B x1 x2) = ⊃ₗ Γ Δ A B (cutLower d x1) (cutLower d x2)
cutLower d (⊃ᵣ Γ Δ A B x) = ⊃ᵣ Γ Δ A B (cutLower d x)

cutElim : (Γ Δ : Cedent) → (Γ ==> Δ) → (Γ ==> Δ)
cutElim Γ Δ p = h (maxCutDepth p) p
  where
  h : ℕ → Γ ==> Δ → Γ ==> Δ
  h zero p = p
  h (suc d) p = h d (cutLower d p)

