module Properties where

open import Function
open import Data.Nat as ℕ using (ℕ; zero; suc)
open import Data.String
open import Data.Bool hiding (_≟_)
open import Data.Sum
open import Data.Product
open import Relation.Nullary.Decidable
open import Relation.Nullary.Negation
open import Relation.Binary.PropositionalEquality
open import SystemF

weaken-type : (∀ {t} → Δ ∋ t type → Δ′ ∋ t type) → Δ ⊢ τ type → Δ′ ⊢ τ type
weaken-type σ (type-v n) = type-v (σ n)
weaken-type σ (type-⇒ D D₁) = type-⇒ (weaken-type σ D) (weaken-type σ D₁)
weaken-type σ (type-∀ D) = type-∀ (weaken-type (λ{ zero → zero ; (suc n) → suc (σ n)}) D)

weaken-types : (∀ {t} → Δ ∋ t type → Δ′ ∋ t type) → Δ ⊢ Γ types → Δ′ ⊢ Γ types
weaken-types σ []       = []
weaken-types σ (t ∷ ts) = weaken-type σ t ∷ weaken-types σ ts

subst-type : Δ ⊢ τ type → Δ , t type ⊢ τ′ type → Δ ⊢ ([ τ /ₜ t ]ₜ τ′) type
subst-type {t = t} D₁ (type-v {t = t′} n) with n | t ≟ t′
... | n     | yes refl = D₁
... | zero  | no ¬t≡t′ = type-v (contradiction refl ¬t≡t′)
... | suc n | no _     = type-v n
subst-type D₁ (type-⇒ D₂ D₃) = type-⇒ (subst-type D₁ D₂) (subst-type D₁ D₃)
subst-type {t = t} D₁ (type-∀ {t = t′} D₂) with t ≟ t′
... | yes refl = type-∀ (weaken-type (λ { zero → zero ; (suc n) → n }) D₂)
... | no ¬t≡t′ = type-∀ (subst-type (weaken-type (λ {t = t₁} → suc) D₁)
                                 (weaken-type (λ { zero          → suc zero
                                            ; (suc zero)    → zero
                                            ; (suc (suc n)) → suc (suc n) }) D₂))

regular : Δ ⊢ Γ types → Δ , Γ ⊢ e ⦂ τ → Δ ⊢ τ type
regular (t ∷ _ ) (τ-v zero) = t
regular (_ ∷ ts) (τ-v (suc _ n)) = regular ts (τ-v n)
regular types (τ-λ t D) = type-⇒ t (regular (t ∷ types) D)
regular types (τ-· D₁ D₂) with type-⇒ _ t₂ ← regular types D₁ = t₂
regular types (τ-Λ D) = type-∀ (regular (weaken-types (λ {t} → suc) types) D)
regular types (τ-＠ D t) with type-∀ t′ ← regular types D = subst-type t t′


------------------------------------------------------------------------
-- Typing properties
------------------------------------------------------------------------

weaken :
  (∀ {t} → Δ ∋ t type → Δ′ ∋ t type) →
  (∀ {x τ} → Γ ∋ x ⦂ τ → Γ′ ∋ x ⦂ τ) →
  Δ , Γ ⊢ e ⦂ τ → Δ′ , Γ′ ⊢ e ⦂ τ
weaken δ ρ (τ-v n) = τ-v (ρ n)
weaken δ ρ (τ-λ t D) = τ-λ (weaken-type δ t) (weaken δ (λ{ zero → zero ; (suc x n) → suc x (ρ n) }) D)
weaken δ ρ (τ-· D₁ D₂) = τ-· (weaken δ ρ D₁) (weaken δ ρ D₂)
weaken δ ρ (τ-Λ D) = τ-Λ (weaken (λ{ zero → zero ; (suc n) → suc (δ n) }) ρ D)
weaken δ ρ (τ-＠ D t) = τ-＠ (weaken δ ρ D) (weaken-type δ t)

-- Substitution of types preserves types
subst-τ : ∅ ⊢ τ type → (Δ , t type) , Γ ⊢ e′ ⦂ τ′ → Δ , ([ τ /ₜ t ]C Γ) ⊢ ([ τ /ₜ t ] e′) ⦂ ([ τ /ₜ t ]ₜ τ′)
subst-τ t (τ-v zero) = τ-v zero
subst-τ t (τ-v (suc ≢₁ n)) = τ-v (suc ≢₁ (lemma n)) where
  lemma : ∀ {Γ x t τ τ′} → Γ ∋ x ⦂ τ′ → [ τ /ₜ t ]C Γ ∋ x ⦂ [ τ /ₜ t ]ₜ τ′
  lemma zero = zero
  lemma (suc ≢₁ n) = suc ≢₁ (lemma n)
subst-τ t (τ-λ t′ D) = τ-λ (subst-type (weaken-type (λ ()) t) t′) (subst-τ t D)
subst-τ t (τ-· D₁ D₂) = τ-· (subst-τ t D₁) (subst-τ t D₂)
subst-τ {t = t₁} t (τ-Λ {t = t₂} D) with t₁ ≟ t₂
... | yes refl = τ-Λ {!!}
... | no t₁≢t₂ = τ-Λ (subst-τ (weaken-type (λ ()) t) (weaken (λ{ zero          → suc zero
                                                               ; (suc zero)    → zero
                                                               ; (suc (suc n)) → suc (suc n)}) id D))
subst-τ t (τ-＠ D t′) = {!!}

-- Substitution of closed terms preserves types
subst-e : Δ , ∅ ⊢ e ⦂ τ → Δ , (Γ , x ⦂ τ) ⊢ e′ ⦂ τ′ → Δ , Γ ⊢ [ e / x ] e′ ⦂ τ′
subst-e {x = x} D₁ (τ-v {x = y} n) with n | x ≟ y
... | zero     | yes refl = weaken id (λ ()) D₁
... | suc _  n | no _     = τ-v n
... | zero      | no x≢y   = contradiction refl x≢y
... | suc x≢y _ | yes refl = contradiction refl x≢y
subst-e {x = x} D₁ (τ-λ {x = y} t D₂) with x ≟ y
... | yes refl = τ-λ t (weaken id (λ{ zero                → zero
                                    ; (suc x≢y zero)      → contradiction refl x≢y
                                    ; (suc x≢y (suc _ n)) → suc x≢y n }) D₂)
... | no  x≢y  = τ-λ t (subst-e D₁ (weaken id (λ{ zero → suc (x≢y ∘ sym) zero
                                                ; (suc _ zero) → zero
                                                ; (suc ≢₁ (suc ≢₂ n)) → suc ≢₂ (suc ≢₁ n) }) D₂))
subst-e D₁ (τ-· D₂ D₃) = τ-· (subst-e D₁ D₂) (subst-e D₁ D₃)
subst-e D₁ (τ-Λ D₂) = τ-Λ (subst-e (weaken (λ {t} → suc) id D₁) D₂)
subst-e D₁ (τ-＠ D₂ t) = τ-＠ (subst-e D₁ D₂) t

preservation : e ⦂₀ τ → e ↦ e′ → e′ ⦂₀ τ
preservation (τ-· (τ-λ _ D₁) D₂) (β-λ _) = subst-e D₂ D₁
preservation (τ-· D₁ D₂) (ξ-·-ₗ ↦) = τ-· (preservation D₁ ↦) D₂
preservation (τ-· D₁ D₂) (ξ-·-ᵣ x ↦) = τ-· D₁ (preservation D₂ ↦)
preservation (τ-＠ D t) (ξ-＠ ↦) = τ-＠ (preservation D ↦) t
preservation (τ-＠ (τ-Λ D) t) β-Λ = subst-τ t D

progress : e ⦂₀ τ → (e Val) ⊎ ∃[ e′ ] (e ↦ e′)
progress (τ-λ t D) = inj₁ λ-Val
progress (τ-Λ D)   = inj₁ Λ-Val
progress (τ-· {e₁ = e₁} {e₂ = e₂} D₁ D₂) with progress D₁
... | inj₂ (e′ , ↦) = inj₂ ((e′ · e₂) , ξ-·-ₗ ↦)
... | inj₁ (λ-Val {e = e}) with progress D₂
... | inj₂ (e′ , ↦) = inj₂ (((λ⟨ _ ⦂ _ ⟩ e) · e′) , ξ-·-ᵣ λ-Val ↦)
... | inj₁ val₂ = inj₂ (([ e₂ / _ ] e) , β-λ val₂)
progress (τ-＠ D t) with progress D
... | inj₁ Λ-Val = inj₂ (([ _ /ₜ _ ] _) , β-Λ)
... | inj₂ (e′ , ↦) = inj₂ ((e′ ＠ _) , ξ-＠ ↦)
