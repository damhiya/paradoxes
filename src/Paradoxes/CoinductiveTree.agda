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

ind : (V → Set) → Set
ind p = ∀ x → (∀ y → y ∈ x → p y) → p x

wf : V → Set
wf x = ∀ p → ind p → p x

wf-induction : ∀ x → wf x → ∀ p → ind p → p x
wf-induction x x-wf p p-ind = x-wf p p-ind

wf→normal : ∀ x → wf x → ¬ x ∈ x
wf→normal =
  let
    P : V → Set
    P x = ¬ x ∈ x

    P-ind : ind P
    P-ind x H x∈x = H x x∈x x∈x
  in λ x x-wf → wf-induction x x-wf P P-ind

Ω : V
Ω = set (Σ[ x ∈ V ] wf x) proj₁

∈Ω→wf : ∀ x → x ∈ Ω → wf x
∈Ω→wf x ((.x , x-wf) , refl) = x-wf

Ω-wf : wf Ω
Ω-wf p p-ind = p-ind Ω λ x x∈Ω → ∈Ω→wf x x∈Ω p p-ind

Ω∉Ω : ¬ Ω ∈ Ω
Ω∉Ω = wf→normal Ω Ω-wf

Ω∈Ω : Ω ∈ Ω
Ω∈Ω = (Ω , Ω-wf) , refl

Burali-Forti : ⊥
Burali-Forti = Ω∉Ω Ω∈Ω
