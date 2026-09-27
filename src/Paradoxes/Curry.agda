open import Data.Empty
open import Relation.Nullary.Negation.Core

module Paradoxes.Curry where

{-# NO_POSITIVITY_CHECK #-}
data Curry : Set where
  roll : (Curry → ⊥) → Curry

not-curry : ¬ Curry
not-curry (roll H) = H (roll H)

curry : Curry
curry = roll not-curry

false : ⊥
false = not-curry curry
