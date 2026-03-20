module SystemF where

open import Data.String
open import Data.Maybe
open import Data.Bool hiding (_≟_)
open import Relation.Nullary.Decidable
open import Relation.Binary.PropositionalEquality


------------------------------------------------------------------------
-- Syntax
------------------------------------------------------------------------

data Type : Set where
  tv_ : String → Type
  _⇒_ : Type → Type → Type
  ∀⟨_⟩_ : String → Type → Type

data Term : Set where
  v_ : String → Term
  λ⟨_⦂_⟩_ : String → Type → Term → Term
  _·_ : Term → Term → Term
  Λ⟨_⟩_ : String → Term → Term
  _＠_ : Term → Type → Term

data TContext : Set where
  ∅ : TContext
  _,_type : TContext → String → TContext

data Context : Set where
  ∅ : Context
  _,_⦂_ : Context → String → Type → Context

variable
  x y t t′ : String
  e e′ e₁ e₂ : Term
  τ τ′ τ₁ τ₂ : Type
  Δ Δ′ : TContext
  Γ Γ′ : Context


------------------------------------------------------------------------
-- Substitutions
------------------------------------------------------------------------

[_/ₜ_]ₜ_ : Type → String → Type → Type
[ τ /ₜ t ]ₜ (tv t′) = if ⌊ t ≟ t′ ⌋ then τ else (tv t′)
[ τ /ₜ t ]ₜ (τ₁ ⇒ τ₂) = ([ τ /ₜ t ]ₜ τ₁) ⇒ ([ τ /ₜ t ]ₜ τ₂)
[ τ /ₜ t ]ₜ (∀⟨ t′ ⟩ τ′) = ∀⟨ t′ ⟩ (if ⌊ t ≟ t′ ⌋ then τ′ else [ τ /ₜ t ]ₜ τ′)

[_/ₜ_]C_ : Type → String → Context → Context
[ τ /ₜ t ]C ∅ = ∅
[ τ /ₜ t ]C (Γ , x ⦂ τ′) = [ τ /ₜ t ]C Γ , x ⦂ ([ τ /ₜ t ]ₜ τ′)

[_/ₜ_]_ : Type → String → Term → Term
[ τ /ₜ t ] (v x) = v x
[ τ /ₜ t ] (λ⟨ x ⦂ τ′ ⟩ e) = λ⟨ x ⦂ [ τ /ₜ t ]ₜ τ′ ⟩ ([ τ /ₜ t ] e)
[ τ /ₜ t ] (e₁ · e₂) = ([ τ /ₜ t ] e₁) · ([ τ /ₜ t ] e₂)
[ τ /ₜ t ] (Λ⟨ t′ ⟩ e) = Λ⟨ t′ ⟩ (if ⌊ t ≟ t′ ⌋ then e else [ τ /ₜ t ] e)
[ τ /ₜ t ] (e ＠ τ′) = ([ τ /ₜ t ] e) ＠ ([ τ /ₜ t ]ₜ τ′)

[_/_]_ : Term → String → Term → Term
[ e / x ] (v y) = if ⌊ x ≟ y ⌋ then e else v y
[ e / x ] (λ⟨ y ⦂ τ ⟩ e′) = λ⟨ y ⦂ τ ⟩ (if ⌊ x ≟ y ⌋ then e′ else [ e / x ] e′)
[ e / x ] (e₁ · e₂) = ([ e / x ] e₁) · ([ e / x ] e₂)
[ e / x ] (Λ⟨ t ⟩ e′) = Λ⟨ t ⟩ ([ e / x ] e′)
[ e / x ] (e′ ＠ τ) = ([ e / x ] e′) ＠ τ


------------------------------------------------------------------------
-- Statics
------------------------------------------------------------------------

data _∋_type : TContext → String → Set where
  zero : Δ , t type ∋ t type
  suc : Δ ∋ t type → Δ , t′ type ∋ t type

data _∋_⦂_ : Context → String → Type → Set where
  zero : (Γ , x ⦂ τ) ∋ x ⦂ τ
  suc : x ≢ y → Γ ∋ x ⦂ τ → (Γ , y ⦂ τ′) ∋ x ⦂ τ

data _⊢_type : TContext → Type → Set where
  type-v : Δ ∋ t type → Δ ⊢ tv t type
  type-⇒ : Δ ⊢ τ₁ type → Δ ⊢ τ₂ type → Δ ⊢ τ₁ ⇒ τ₂ type
  type-∀ : Δ , t type ⊢ τ type → Δ ⊢ (∀⟨ t ⟩ τ) type

data _⊢_types (Δ : TContext) : Context → Set where
  [] : Δ ⊢ ∅ types
  _∷_ : Δ ⊢ τ type → Δ ⊢ Γ types → Δ ⊢ (Γ , x ⦂ τ) types

data _,_⊢_⦂_ : TContext → Context → Term → Type → Set where
  τ-v : Γ ∋ x ⦂ τ → Δ , Γ ⊢ (v x) ⦂ τ
  τ-λ : Δ ⊢ τ₁ type → Δ , (Γ , x ⦂ τ₁) ⊢ e ⦂ τ₂ → Δ , Γ ⊢ λ⟨ x ⦂ τ₁ ⟩ e ⦂ (τ₁ ⇒ τ₂)
  τ-· : Δ , Γ ⊢ e₁ ⦂ (τ ⇒ τ′) →  Δ , Γ ⊢ e₂ ⦂ τ → Δ , Γ ⊢ e₁ · e₂ ⦂ τ′
  τ-Λ : ∀ {t} → (Δ , t type) , Γ ⊢ e ⦂ τ → Δ , Γ ⊢ (Λ⟨ t ⟩ e) ⦂ (∀⟨ t ⟩ τ)
  τ-＠ : Δ , Γ ⊢ e ⦂ (∀⟨ t ⟩ τ′) → Δ ⊢ τ type → Δ , Γ ⊢ (e ＠ τ) ⦂ ([ τ /ₜ t ]ₜ τ′)

_⦂₀_ = ∅ , ∅ ⊢_⦂_


------------------------------------------------------------------------
-- Dynamics
------------------------------------------------------------------------

data _Val : Term → Set where
  λ-Val : (λ⟨ x ⦂ τ ⟩ e) Val
  Λ-Val : (Λ⟨ t ⟩ e) Val

data _↦_ : Term → Term → Set where
  β-λ : e₂ Val → (λ⟨ x ⦂ τ₁ ⟩ e) · e₂ ↦ [ e₂ / x ] e
  β-Λ : (Λ⟨ t ⟩ e) ＠ τ ↦ [ τ /ₜ t ] e
  ξ-·-ₗ : e ↦ e′ → e · e₂ ↦ e′ · e₂
  ξ-·-ᵣ : e₁ Val → e ↦ e′ → e₁ · e ↦ e₁ · e′
  ξ-＠  : e ↦ e′ → e ＠ τ ↦ e′ ＠ τ


------------------------------------------------------------------------
-- Fixity
------------------------------------------------------------------------

infix 0 _∋_type _∋_⦂_ _⊢_type _⊢_types _,_⊢_⦂_
infixl 1 _,_type _,_⦂_ _Val _↦_

infixr 10 _⇒_
infix  11 ∀⟨_⟩_
infix  12 tv_

infixl 20 _·_ _＠_
infix  21 λ⟨_⦂_⟩_ Λ⟨_⟩_
infix  22 v_
