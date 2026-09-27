{-# OPTIONS --type-in-type #-}

-- Coquand, T. The paradox of trees in type theory. BIT 32, 10–14 (1992).
-- https://doi.org/10.1007/BF01995104

open import Data.Empty
open import Data.Product.Base
open import Relation.Binary.PropositionalEquality.Core
open import Relation.Nullary.Negation.Core

module Paradoxes.Coquand92 where

data V : Set where
  set : ∀ (A : Set) → (A → V) → V

_∈_ : V → V → Set
y ∈ set A f = Σ[ a ∈ A ] f a ≡ y

normal : V → Set
normal x = ¬ x ∈ x

module Russell where

  -- set of all normal sets
  R : V
  R = set (Σ[ x ∈ V ] normal x) proj₁

  normal→∈R : ∀ x → ¬ x ∈ x → x ∈ R
  normal→∈R x x∉x = (x , x∉x) , refl

  ∈R→normal : ∀ x → x ∈ R → ¬ x ∈ x
  ∈R→normal x ((.x , x∉x) , refl) = x∉x

  R∉R : ¬ R ∈ R
  R∉R R∈R = ∈R→normal R R∈R R∈R

  R∈R : R ∈ R
  R∈R = normal→∈R R R∉R

  Russell : ⊥
  Russell = R∉R R∈R

module Burali-Forti where

  ind : (V → Set) → Set
  ind p = ∀ x → (∀ y → y ∈ x → p y) → p x

  ∈-induction : ∀ (p : V → Set)
                  (p-ind : ind p) →
                ∀ x → p x
  ∈-induction p p-ind (set A f) =
    p-ind
      (set A f)
      λ { .(f a) (a , refl) → ∈-induction p p-ind (f a) }

  ∈-irrefl : ∀ x → ¬ x ∈ x
  ∈-irrefl = ∈-induction normal normal-ind
    where
      normal-ind : ind normal
      normal-ind x ∈x→normal x∈x = ∈x→normal x x∈x x∈x

  -- Since V is inductively defined, every sets are well-founded by construction.
  -- Hence we can use the set of all sets instead of the set of all well-founded sets.
  Ω : V
  Ω = set V (λ x → x)

  Ω∉Ω : ¬ Ω ∈ Ω
  Ω∉Ω = ∈-irrefl Ω

  Ω∈Ω : Ω ∈ Ω
  Ω∈Ω = Ω , refl

  Burali-Forti : ⊥
  Burali-Forti = Ω∉Ω Ω∈Ω
