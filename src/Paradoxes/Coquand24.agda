{-# OPTIONS --type-in-type #-}

-- Coquand, T. (2024). A Variation of Reynolds-Hurkens Paradox.
-- In: Capretta, V., Krebbers, R., Wiedijk, F. (eds) Logics and Type Systems in Theory and Practice.
-- Lecture Notes in Computer Science, vol 14560. Springer, Cham.
-- https://doi.org/10.1007/978-3-031-61716-4_7

open import Data.Empty
open import Data.Product.Base renaming (proj₁ to fst; proj₂ to snd)
open import Function.Base
open import Relation.Nullary.Negation.Core
open import Relation.Binary.PropositionalEquality.Core

module Paradoxes.Coquand24 where

-- Impredicative encoding of inductive types
μ : (Set → Set) → Set
μ F = ∀ (X : Set) → (F X → X) → X

module μ
  (F : Set → Set)
  (F[_] : ∀ {X Y : Set} → (X → Y) → F X → F Y)
  where

  cata : ∀ (X : Set) → (F X → X) → μ F → X
  cata X ϕ u = u X ϕ

  intro : F (μ F) → μ F
  intro u X ϕ = ϕ (F[ cata X ϕ ] u)

  match : μ F → F (μ F)
  match u = u (F (μ F)) F[ intro ]

-- Power set
𝒫 : Set → Set
𝒫 X = X → Set

𝒫[_] : ∀ {X Y : Set} → (X → Y) → 𝒫 Y → 𝒫 X
𝒫[ ϕ ] p x = p (ϕ x)

𝒫² : Set → Set
𝒫² X = 𝒫 (𝒫 X)

𝒫²[_] : ∀ {X Y : Set} → (X → Y) → 𝒫² X → 𝒫² Y
𝒫²[ ϕ ] = 𝒫[ 𝒫[ ϕ ] ]

-- Universe
V : Set
V = μ 𝒫²

intro : 𝒫² V → V
intro = μ.intro 𝒫² 𝒫²[_]

match : V → 𝒫² V
match = μ.match 𝒫² 𝒫²[_]

δ : V → V
δ x = intro (match x)

powerful : ∀ Φ → match (intro Φ) ≡ λ p → Φ (p ∘ δ)
powerful = λ Φ → refl

p₀ : V → Set
p₀ x = ∀ p → p (δ x) → ¬ match x p

X₀ : 𝒫² V
X₀ p = ∀ x → p x → ¬ match x p

x₀ : V
x₀ = intro X₀

s₁ : ∀ x → p₀ x → p₀ (δ x)
s₁ x h p = h (p ∘ δ)

s₂ : ∀ p → X₀ p → X₀ (p ∘ δ)
s₂ p h x = h (δ x)

l₀ : ∀ p → p x₀ → ¬ X₀ p
l₀ p h h₀ = h₀ x₀ h (s₂ p h₀)

l₁ : X₀ p₀
l₁ x h = h p₀ (s₁ x h)

l₂ : p₀ x₀
l₂ p = l₀ (p ∘ δ)

false : ⊥
false = l₀ p₀ l₂ l₁
