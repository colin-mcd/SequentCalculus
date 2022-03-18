module Types where
open import lib

data Atom : Set where
  aZ : Atom
  aS : Atom → Atom

infixr 6 _∧_
infixr 5 _∨_
infix 7 ¬_

data Sentence : Set where
  atom : Atom → Sentence
  ¬_ : Sentence → Sentence -- "\neg"
  _∨_ : Sentence → Sentence → Sentence -- "\or"
  _∧_ : Sentence → Sentence → Sentence -- "\and"
  _⊃_ : Sentence → Sentence → Sentence -- "\sup"

_=atom_ : Atom → Atom → Bool
aZ =atom aZ = true
(aS a1) =atom (aS a2) = a1 =atom a2
a1 =atom a2 = false

_=sentence_ : Sentence → Sentence → Bool
(atom v) =sentence (atom u) = v =atom u
(¬ s) =sentence (¬ t) = s =sentence t
(s1 ∨ s2) =sentence (t1 ∨ t2) = (s1 =sentence t1) && (s2 =sentence t2)
(s1 ∧ s2) =sentence (t1 ∧ t2) = (s1 =sentence t1) && (s2 =sentence t2)
(s1 ⊃ s2) =sentence (t1 ⊃ t2) = (s1 =sentence t1) && (s2 =sentence t2)
s =sentence t = false

Cedent : Set
Cedent = List Sentence

ccat : ∀ {l r : Bool} {A : Set} →
  (if l then A else List A) → (if r then A else List A) → List A
ccat {true} {true} a1 a2 = a1 ∷ a2 ∷ []
ccat {true} {false} a1 l2 = a1 ∷ l2
ccat {false} {true} l1 a2 = l1 ∷ʳ a2
ccat {false} {false} l1 l2 = l1 ++ l2

infixr 4 _¸_
_¸_ = ccat

infix 0 _==>_
data _==>_ : Cedent → Cedent → Set where
  leaf : (A : Atom) → ([ atom A ] ==> [ atom A ])


  cut : (Γ Δ : Cedent) (A : Sentence) →
    (Γ ==> Δ ¸ A) → (A ¸ Γ ==> Δ) →
    (Γ ==> Δ)


  exchangeₗ : (Γ Π Δ : Cedent) (A B : Sentence) →
    (Γ ¸ A ¸ B ¸ Π ==> Δ) →
    (Γ ¸ B ¸ A ¸ Π ==> Δ)

  exchangeᵣ : (Γ Π Δ : Cedent) (A B : Sentence) →
    (Γ ==> Δ ¸ A ¸ B ¸ Π) →
    (Γ ==> Δ ¸ B ¸ A ¸ Π)

  contractionₗ : (Γ Δ   : Cedent) (A   : Sentence) →
    (A ¸ A ¸ Γ ==> Δ) →
    (A ¸ Γ ==> Δ)

  contractionᵣ : (Γ Δ : Cedent) (A : Sentence) →
    (Γ ==> Δ ¸ A ¸ A) →
    (Γ ==> Δ ¸ A)

  weakeningₗ : (Γ Δ : Cedent) (A : Sentence) →
    (Γ ==> Δ) →
    (A ¸ Γ ==> Δ)

  weakeningᵣ : (Γ Δ : Cedent) (A : Sentence) →
    (Γ ==> Δ) →
    (Γ ==> Δ ¸ A)


  ¬ₗ : (Γ Δ : Cedent) (A : Sentence) →
    (Γ ==> Δ ¸ A) →
    (¬ A ¸ Γ ==> Δ)

  ¬ᵣ : (Γ Δ : Cedent) (A : Sentence) →
    (A ¸ Γ ==> Δ) →
    (Γ ==> Δ ¸ ¬ A)

  ∧ₗ : (Γ Δ : Cedent) (A B : Sentence) →
    (A ¸ B ¸ Γ ==> Δ) →
    (A ∧ B ¸ Γ ==> Δ)

  ∧ᵣ : (Γ Δ : Cedent) (A B : Sentence) →
    (Γ ==> Δ ¸ A) → (Γ ==> Δ ¸ B) →
    (Γ ==> Δ ¸ A ∧ B)

  ∨ₗ : (Γ Δ : Cedent) (A B : Sentence) →
    (A ¸ Γ ==> Δ) → (B ¸ Γ ==> Δ) →
    (A ∨ B ¸ Γ ==> Δ)

  ∨ᵣ : (Γ Δ : Cedent) (A B : Sentence) →
    (Γ ==> Δ ¸ A ¸ B) →
    (Γ ==> Δ ¸ A ∨ B)

  ⊃ₗ : (Γ Δ : Cedent) (A B : Sentence) →
    (Γ ==> Δ ¸ A) → (B ¸ Γ ==> Δ) →
    (A ⊃ B ¸ Γ ==> Δ)

  ⊃ᵣ : (Γ Δ : Cedent) (A B : Sentence) →
    (A ¸ Γ ==> Δ ¸ B) →
    (Γ ==> Δ ¸ A ⊃ B)

{-

isCutFree : ∀ {Γ Δ} → (Γ ==> Δ) → Bool
isCutFree (leaf A) = {!!}P
isCutFree (cut Γ Δ A x x₁) = {!!}
isCutFree (exchangeₗ Γ Π _ A B x) = {!!}
isCutFree (exchangeᵣ Γ Π Δ A B x) = {!!}
isCutFree (contractionₗ Γ Δ A x) = {!!}
isCutFree (contractionᵣ Γ Δ A x) = {!!}
isCutFree (weakeningₗ Γ Δ A x) = {!!}
isCutFree (weakeningᵣ Γ Δ A x) = {!!}
isCutFree (¬ₗ Γ Δ A x) = {!!}
isCutFree (¬ᵣ Γ Δ A x) = {!!}
isCutFree (∧ₗ Γ Δ A B x) = {!!}
isCutFree (∧ᵣ Γ Δ A B x x₁) = {!!}
isCutFree (∨ₗ Γ Δ A B x x₁) = {!!}
isCutFree (∨ᵣ Γ Δ A B x) = {!!}
isCutFree (⊃ₗ Γ Δ A B x x₁) = {!!}
isCutFree (⊃ᵣ Γ Δ A B x) = {!!}

-}
