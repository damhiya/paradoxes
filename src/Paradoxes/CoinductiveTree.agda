{-# OPTIONS --type-in-type #-}

-- This is a modification of the proof given in Coquand92.
-- Here, we use a coinductively defined universe instead of an inductively defined one.
--
-- Coquand, T. The paradox of trees in type theory. BIT 32, 10–14 (1992).
-- https://doi.org/10.1007/BF01995104

open import Data.Empty
open import Data.Product.Base
open import Relation.Binary.PropositionalEquality.Core
open import Relation.Nullary.Negation.Core

module Paradoxes.CoinductiveTree where

record V : Set where
  coinductive
  constructor set
  field
    Index : Set
    family : Index → V

open V

_∈_ : V → V → Set
y ∈ x = Σ[ a ∈ x .Index ] x .family a ≡ y

normal : V → Set
normal x = ¬ x ∈ x

module Russell where

  -- set of all normal sets
  R : V
  R = set (Σ[ x ∈ V ] normal x) proj₁

  normal→∈R : ∀ x → normal x → x ∈ R
  normal→∈R x x∉x = (x , x∉x) , refl

  ∈R→normal : ∀ x → x ∈ R → normal x
  ∈R→normal x ((.x , x∉x) , refl) = x∉x

  R∉R : ¬ R ∈ R
  R∉R R∈R = ∈R→normal R R∈R R∈R

  R∈R : R ∈ R
  R∈R = normal→∈R R R∉R

  Russell : ⊥
  Russell = R∉R R∈R

module Burali-Forti where

  -- inductive property
  ind : (V → Set) → Set
  ind p = ∀ x → (∀ y → y ∈ x → p y) → p x

  -- well-foundedness is defined as the least inductive property
  wf : V → Set
  wf x = ∀ p → ind p → p x

  wf-ind : ind wf
  wf-ind x ∈x→wf p p-ind = p-ind x ∈x→p
    where
      ∈x→p : ∀ y → y ∈ x → p y
      ∈x→p y y∈x = ∈x→wf y y∈x p p-ind

  wf-induction : ∀ x → wf x → ∀ p → ind p → p x
  wf-induction x x-wf p p-ind = x-wf p p-ind

  wf→normal : ∀ x → wf x → normal x
  wf→normal x x-wf = wf-induction x x-wf normal normal-ind
    where
      normal-ind : ind normal
      normal-ind x ∈x→normal x∈x = ∈x→normal x x∈x x∈x

  -- set of all well-founded sets
  Ω : V
  Ω = set (Σ[ x ∈ V ] wf x) proj₁

  Ω-wf : wf Ω
  Ω-wf = wf-ind Ω ∈Ω→wf
    where
      ∈Ω→wf : ∀ x → x ∈ Ω → wf x
      ∈Ω→wf x ((.x , x-wf) , refl) = x-wf

  Ω∉Ω : ¬ Ω ∈ Ω
  Ω∉Ω = wf→normal Ω Ω-wf

  Ω∈Ω : Ω ∈ Ω
  Ω∈Ω = (Ω , Ω-wf) , refl

  Burali-Forti : ⊥
  Burali-Forti = Ω∉Ω Ω∈Ω
