module lib where
open import Data.Bool using (Bool; true; false; if_then_else_) public
open import Data.List public
open import Data.List.Properties public
open import Data.Nat renaming (_⊔_ to max) public
open import Data.Nat.Properties public
open import Agda.Builtin.Nat public
  using () renaming (_<_ to _<ᵇ_)
open import Level public using (Level; _⊔_)
open import Data.Product public hiding (map; zip)
--open import Relation.Binary
open import Agda.Builtin.Equality public
open import Agda.Builtin.Maybe public
open import Data.Sum public hiding (assocʳ; assocˡ; map; map₁; map₂; swap)
open import Relation.Binary.PropositionalEquality.Core public

_&&_ = Data.Bool._∧_
_||_ = Data.Bool._∨_

_>ᵇ_ = λ x y → y <ᵇ x
_≥ᵇ_ = λ x y → Data.Bool.not (x <ᵇ y)
--_≤ᵇ_ = λ x y → not (y <ᵇ x)
