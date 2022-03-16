module CutElim where
open import Data.Bool hiding (_∨_; _∧_)
open import Data.List
--open import Data.Vec hiding (_∷_; _∷ʳ_; _++_)
open import Data.Nat hiding (_⊔_)
open import Level using (Level; _⊔_)

Atom : Set
Atom = ℕ

data Sentence : Set where
  atom : Atom → Sentence
  ¬_ : Sentence → Sentence -- "\neg"
  _∨_ : Sentence → Sentence → Sentence -- "\or"
  _∧_ : Sentence → Sentence → Sentence -- "\and"
  _⊃_ : Sentence → Sentence → Sentence -- "\sup"

Cedent : Set
Cedent = List Sentence

infixl 3 _==>_
data Sequent : Set where
  _==>_ : Cedent -> Cedent → Sequent

antecedent : Sequent → Cedent
antecedent (a ==> s) = a

succedent : Sequent → Cedent
succedent (a ==> s) = s

ccat : ∀ {l r : Bool} {A : Set} →
  (if l then A else List A) → (if r then A else List A) → List A
ccat {true} {true} a1 a2 = a1 ∷ a2 ∷ []
ccat {true} {false} a1 l2 = a1 ∷ l2
ccat {false} {true} l1 a2 = l1 ∷ʳ a2
ccat {false} {false} l1 l2 = l1 ++ l2

infixr 9 _,_
_,_ = ccat

data Proof : Sequent → Set where
  leaf : (A : Sentence) → Proof ([ A ] ==> [ A ])


  cut : (Γ Δ : Cedent) (A : Sentence) →
    Proof (Γ ==> Δ , A) → Proof (A , Γ ==> Δ) →
    Proof (Γ ==> Δ)


  exchangeₗ : (Γ Π Δ : Cedent) (A B : Sentence) →
    Proof (Γ , A , B , Π ==> Δ) →
    Proof (Γ , B , A , Π ==> Δ)

  exchangeᵣ : (Γ Π Δ : Cedent) (A B : Sentence) →
    Proof (Γ ==> Δ , A , B , Π) →
    Proof (Γ ==> Δ , B , A , Π)

  contractionₗ : (Γ Δ   : Cedent) (A   : Sentence) →
    Proof (A , A , Γ ==> Δ) →
    Proof (A , Γ ==> Δ)

  contractionᵣ : (Γ Δ : Cedent) (A : Sentence) →
    Proof (Γ ==> Δ , A , A) →
    Proof (Γ ==> Δ , A)

  weakeningₗ : (Γ Δ : Cedent) (A : Sentence) →
    Proof (Γ ==> Δ) →
    Proof (A , Γ ==> Δ)

  weakeningᵣ : (Γ Δ : Cedent) (A : Sentence) →
    Proof (Γ ==> Δ) →
    Proof (Γ ==> Δ , A)


  ¬ₗ : (Γ Δ : Cedent) (A : Sentence) →
    Proof (Γ ==> Δ , A) →
    Proof (¬ A , Γ ==> Δ)

  ¬ᵣ : (Γ Δ : Cedent) (A : Sentence) →
    Proof (A , Γ ==> Δ) →
    Proof (Γ ==> Δ , ¬ A)

  ∧ₗ : (Γ Δ : Cedent) (A B : Sentence) →
    Proof (A , B , Γ ==> Δ) →
    Proof (A ∧ B , Γ ==> Δ)

  ∧ᵣ : (Γ Δ : Cedent) (A B : Sentence) →
    Proof (Γ ==> Δ , A) → Proof (Γ ==> Δ , B) →
    Proof (Γ ==> Δ , A ∧ B)

  ∨ₗ : (Γ Δ : Cedent) (A B : Sentence) →
    Proof (A , Γ ==> Δ) → Proof (B , Γ ==> Δ) →
    Proof (A ∨ B , Γ ==> Δ)

  ∨ᵣ : (Γ Δ : Cedent) (A B : Sentence) →
    Proof (Γ ==> Δ , A , B) →
    Proof (Γ ==> Δ , A ∨ B)

  ⊃ₗ : (Γ Δ : Cedent) (A B : Sentence) →
    Proof (Γ ==> Δ , A) → Proof (B , Γ ==> Δ) →
    Proof (A ⊃ B , Γ ==> Δ)

  ⊃ᵣ : (Γ Δ : Cedent) (A B : Sentence) →
    Proof (A , Γ ==> Δ , B) →
    Proof (Γ ==> Δ , A ⊃ B)

--isCutFree : {S} → 
