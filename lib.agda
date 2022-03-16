module lib where
open import Data.Bool renaming (_∨_ to _||_; _∧_ to _&&_) public
open import Data.List public
--open import Data.Nat hiding (_⊔_) public
open import Level public using (Level; _⊔_)
open import Data.Product public hiding (map; zip)
--open import Relation.Binary
open import Agda.Builtin.Equality public
