{-# OPTIONS --type-in-type #-}

-- Hurkens' paradox.
-- Follows 2.6.4 of Principles of Dependent Type Theory
-- Hurkens presents several variants of the proof.
-- This one is the version using [Π (X : Type). (𝒫²(X) → X) → 𝒫²(X)].

open import Data.Empty
open import Data.Product.Base renaming (proj₁ to fst; proj₂ to snd)
open import Relation.Nullary.Negation.Core
open import Relation.Binary.PropositionalEquality.Core

module Hurkens where

-- Impredicative encoding of inductive types
μ : (Set → Set) → Set
μ F = ∀ (X : Set) → (F X → X) → F X

module μ
  (F : Set → Set)
  (F[_] : ∀ {X Y : Set} → (X → Y) → F X → F Y)
  where

  cata : ∀ (X : Set) → (F X → X) → μ F → X
  cata X ϕ u = ϕ (u X ϕ)

  fold : F (μ F) → μ F
  fold u X ϕ = F[ cata X ϕ ] u

  unfold : μ F → F (μ F)
  unfold u = u (μ F) fold

-- Power set
𝒫 : Set → Set
𝒫 X = X → Set

𝒫[_] : ∀ {X Y : Set} → (X → Y) → 𝒫 Y → 𝒫 X
𝒫[ ϕ ] p x = p (ϕ x)

𝒫𝒫 : Set → Set
𝒫𝒫 X = 𝒫 (𝒫 X)

𝒫𝒫[_] : ∀ {X Y : Set} → (X → Y) → 𝒫𝒫 X → 𝒫𝒫 Y
𝒫𝒫[ ϕ ] = 𝒫[ 𝒫[ ϕ ] ]

-- Intuition.
-- ⟦ fold Φ ⟧     = ⋂ { p | Φ p } = { x | ∀ p. Φ p → p x }
-- ⟦ unfold x ⟧   = { p | ∀ y ∈ x. p y }
-- ⟦ unfold x p ⟧ = x ⊆ p = (∀ y. y ∈ x → p y)
U : Set
U = μ 𝒫𝒫

fold : 𝒫𝒫 U → U
fold = μ.fold 𝒫𝒫 𝒫𝒫[_]

unfold : U → 𝒫𝒫 U
unfold = μ.unfold 𝒫𝒫 𝒫𝒫[_]

powerful : ∀ (Φ : 𝒫𝒫 U) → unfold (fold Φ) ≡ λ p → Φ (λ v → p (fold (unfold v)))
powerful = λ Φ → refl

_∈_ : U → U → Set
y ∈ x = ∀ (p : 𝒫 U) → unfold x p → p y

_ : ∀ (x : U) (p : 𝒫 U) → unfold x p → (∀ y → y ∈ x → p y)
_ = λ x p H y y∈x → y∈x p H

-- Intuition.
-- ⟦ ind p ⟧ = ∀ x. (∀ y. y ∈ x → p y) → p x
-- ⟦ wf x ⟧  = ∀ p. ind p → p x
-- ⟦ Ω ⟧     = ⋂ { p | ind p }
--           = { x | ∀ p. ind p → p x }
--           = { x | wf x }
ind : 𝒫 U → Set
ind p = ∀ (x : U) → unfold x p → p x

wf : U → Set
wf x = ∀ (p : 𝒫 U) → ind p → p x

Ω : U
Ω = fold (λ p → ind p)

Ω-wf : wf Ω
Ω-wf p p-ind =
  let
    Ω⊆p : unfold Ω p
    Ω⊆p x = p-ind (fold (unfold x))
  in p-ind Ω Ω⊆p

Ω∉Ω : ¬ fold (unfold Ω) ∈ Ω
Ω∉Ω =
  let
    ϕ : 𝒫 U
    ϕ = λ y → ¬ fold (unfold y) ∈ y

    ∈-expand : ∀ x y → x ∈ y → fold (unfold x) ∈ fold (unfold y)
    ∈-expand x y x∈y p = x∈y (λ z → p (fold (unfold z)))

    ϕ-ind : ind ϕ
    ϕ-ind = λ x x⊆ϕ x∈x → x∈x ϕ x⊆ϕ (∈-expand (fold (unfold x)) x x∈x)

    wf-ϕ : ∀ x → wf x → ϕ x
    wf-ϕ x x-wf = x-wf ϕ ϕ-ind
  in wf-ϕ Ω Ω-wf

_ : ∀ Φ p → unfold (fold Φ) p ≡ Φ (λ x → p (fold (unfold x)))
_ = λ Φ p → refl

Ω∈Ω : fold (unfold Ω) ∈ Ω
Ω∈Ω p Ω⊆p =
  let
    ϕ : 𝒫 U
    ϕ = λ x → p (fold (unfold x))

    ϕ-ind : ind ϕ
    ϕ-ind = Ω⊆p
  in Ω-wf ϕ ϕ-ind

Hurkens : ⊥
Hurkens = Ω∉Ω Ω∈Ω
