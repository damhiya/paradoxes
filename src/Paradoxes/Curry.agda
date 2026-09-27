open import Data.Empty
open import Relation.Nullary.Negation.Core

module Paradoxes.Curry where

{-# NO_POSITIVITY_CHECK #-}
data D : Set where
  roll : (D → ⊥) → D

ω : ¬ D
ω (roll H) = H (roll H)

Ω : ⊥
Ω = ω (roll ω)
