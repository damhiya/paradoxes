{-# OPTIONS --type-in-type #-}

-- Hurkens' paradox.
-- Follows 2.6.4 of Principles of Dependent Type Theory
-- Hurkens presents several variants of the proof.
-- This one is the version using [Π (X : Type). (𝒫²(X) → X) → 𝒫²(X)].

open import Data.Empty
open import Data.Product.Base renaming (proj₁ to fst; proj₂ to snd)
open import Relation.Nullary.Negation.Core
open import Relation.Binary.PropositionalEquality.Core

module Paradoxes.Hurkens where

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

𝒫² : Set → Set
𝒫² X = 𝒫 (𝒫 X)

𝒫²[_] : ∀ {X Y : Set} → (X → Y) → 𝒫² X → 𝒫² Y
𝒫²[ ϕ ] = 𝒫[ 𝒫[ ϕ ] ]

-- Intuition.
-- ⟦ fold Φ ⟧     = ⋂ { {x | p x} | Φ p } = { x | ∀ p. Φ p → p x }
-- ⟦ unfold x p ⟧ = ∀ y. y ∈ x → p y
U : Set
U = μ 𝒫²

fold : 𝒫² U → U
fold = μ.fold 𝒫² 𝒫²[_]

unfold : U → 𝒫² U
unfold = μ.unfold 𝒫² 𝒫²[_]

powerful : ∀ (Φ : 𝒫² U) → unfold (fold Φ) ≡ λ p → Φ (λ v → p (fold (unfold v)))
powerful = λ Φ → refl

_∈_ : U → U → Set
y ∈ x = ∀ (p : 𝒫 U) → unfold x p → p y

_ : ∀ (x : U) (p : 𝒫 U) → unfold x p → (∀ y → y ∈ x → p y)
_ = λ x p H y y∈x → y∈x p H

-- Intuition.
-- ⟦ ind p ⟧ = ∀ x. (∀ y. y ∈ x → p y) → p x
-- ⟦ wf x ⟧  = ∀ p. ind p → p x
-- ⟦ Ω ⟧     = { x | wf x }
--           = { x | ∀ p. ind p → p x }
--           = ⋂ { {x | p x} | ind p }
ind : 𝒫 U → Set
ind p = ∀ x → unfold x p → p x

wf : U → Set
wf x = ∀ p → ind p → p x

wf-induction : ∀ x → wf x → ∀ p → ind p → p x
wf-induction x x-wf p p-ind = x-wf p p-ind

normal : U → Set
normal x = ¬ fold (unfold x) ∈ x

wf→normal : ∀ x → wf x → normal x
wf→normal x x-wf = wf-induction x x-wf normal normal-ind
  where
    ∈-expand : ∀ x y → x ∈ y → fold (unfold x) ∈ fold (unfold y)
    ∈-expand x y x∈y p = x∈y (λ z → p (fold (unfold z)))

    normal-ind : ind normal
    normal-ind x ∈x→normal x∈x = x∈x normal ∈x→normal (∈-expand (fold (unfold x)) x x∈x)

Ω : U
Ω = fold (λ p → ind p)

Ω-wf : wf Ω
Ω-wf p p-ind = p-ind Ω ∈Ω→p
  where
    ∈Ω→p : unfold Ω p
    ∈Ω→p x = p-ind (fold (unfold x))

Ω∉Ω : ¬ fold (unfold Ω) ∈ Ω
Ω∉Ω = wf→normal Ω Ω-wf

_ : ∀ Φ p → unfold (fold Φ) p ≡ Φ (λ x → p (fold (unfold x)))
_ = λ Φ p → refl

Ω∈Ω : fold (unfold Ω) ∈ Ω
Ω∈Ω p ∈Ω→p = wf-induction Ω Ω-wf ϕ ϕ-ind
  where
    ϕ : 𝒫 U
    ϕ x = p (fold (unfold x))

    -- ∈Ω→p : unfold Ω p
    --      = ind ϕ
    ϕ-ind : ind ϕ
    ϕ-ind = ∈Ω→p

Hurkens : ⊥
Hurkens = Ω∉Ω Ω∈Ω
