open import Level using (lift)
open import Data.List using (List; []; _∷_; length)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool  using (Bool) renaming (_≟_ to _=?_)
open import Data.Integer using (ℤ) renaming (_≟_ to _=int_)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩ )
open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Vec using (Vec) renaming ([] to []̌; _∷_ to _∷̌_)
open import Data.Unit using (tt) renaming (⊤ to Top)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)

module Compile where

open import Coercions
open import LanguageSyntax
open import TypeSystemMetaGTLC


𝒞o⇐ : ∀ {Γ T} (Mᴼ : Term) → Γ ⊢o Mᴼ ⇐ T → Term

𝒞o⇒ : ∀ {Γ T} (Mᴼ : Term) → Γ ⊢o Mᴼ ⇒ T → Term

𝒞 : ∀ {Γ A} (M : Term) → Γ ⊢m M ⦂ A → Term

𝒞o⇐ (ƛ N) (⊢lam ⊢N) = ƛ (𝒞o⇐ _ ⊢N)
𝒞o⇐ _ (⊢splice {A = A} {T} {ℓ = ℓ} ⊢M A~CodeT) =
  ~ (𝒞 _ ⊢M ⟨ coerce A (Code T) {A~CodeT} ℓ ⟩)
𝒞o⇐ M (⊢check-infer ⊢M) = 𝒞o⇒ M ⊢M

𝒞o⇒ (€ r # p) (⊢const _) = € r # p
𝒞o⇒ (` x) (⊢var ∋x) = ` x
𝒞o⇒ (L · M) (⊢app ⊢L ⊢M) = (𝒞o⇒ L ⊢L) · (𝒞o⇐ M ⊢M)
𝒞o⇒ (M ⦂ T) (⊢ann ⊢M) = (𝒞o⇐ M ⊢M) ⦂ T

𝒞 ($ r # p) (⊢const _) = const r p
𝒞 (` x) (⊢var ∋x) = ` x
𝒞 (ƛ A ˙ Nᴹ) (⊢lam ⊢N) = lam A (𝒞 Nᴹ ⊢N)
𝒞 (Lᴹ · Mᴹ at ℓ) (⊢app {A₁ = A₁} {A₂} {B} ⊢L ⊢M A₁~B) =
  app (𝒞 Lᴹ ⊢L) (𝒞 Mᴹ ⊢M ⟨ coerce B A₁ {~-sym A₁~B} ℓ ⟩)
𝒞 (Lᴹ · Mᴹ at ℓ) (⊢app⋆ {A = A} ⊢L ⊢M) =
  app (𝒞 Lᴹ ⊢L ⟨ coerce ⋆ (⋆ ⇒ ⋆) {unk~L} ℓ ⟩) (𝒞 Mᴹ ⊢M ⟨ coerce A ⋆ {unk~R} ℓ ⟩)
𝒞 (≺ Mᴼ ≻) (⊢quote ⊢M) = qt (𝒞o⇒ Mᴼ ⊢M)
