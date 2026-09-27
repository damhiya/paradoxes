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

module Russell where

  R : V
  R = set (Σ[ x ∈ V ] ¬ x ∈ x) proj₁

  R-intro : ∀ x → ¬ x ∈ x → x ∈ R
  R-intro x x∉x = (x , x∉x) , refl

  R-elim : ∀ x → x ∈ R → ¬ x ∈ x
  R-elim x ((.x , x∉x) , refl) = x∉x

  R∉R : ¬ R ∈ R
  R∉R R∈R = R-elim R R∈R R∈R

  R∈R : R ∈ R
  R∈R = R-intro R R∉R

  Russell : ⊥
  Russell = R∉R R∈R

module Burali-Forti where

  -- Since we defined V as an inductive type,
  -- every sets in V are inductive by construction
  ∈-ind : ∀ (P : V → Set)
            (P-ind : ∀ x → (∀ y → y ∈ x → P y) → P x) →
          ∀ x → P x
  ∈-ind P P-ind (set A f) =
    P-ind
      (set A f)
      λ { y (a , p) → subst P p (∈-ind P P-ind (f a)) }

  ∈-irrefl : ∀ x → ¬ x ∈ x
  ∈-irrefl =
    let
      P : V → Set
      P x = ¬ x ∈ x

      P-ind : ∀ x → (∀ y → y ∈ x → P y) → P x
      P-ind x H x∈x = H x x∈x x∈x
    in ∈-ind P P-ind

  Ω : V
  Ω = set V (λ x → x)

  Ω∉Ω : ¬ Ω ∈ Ω
  Ω∉Ω = ∈-irrefl Ω

  Ω∈Ω : Ω ∈ Ω
  Ω∈Ω = Ω , refl

  Burali-Forti : ⊥
  Burali-Forti = Ω∉Ω Ω∈Ω
