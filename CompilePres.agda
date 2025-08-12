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

module CompilePres where

open import Coercions
open import LanguageSyntax
open import TypeSystemMetaGTLC
open import TypeSystemMetaCC
open import Compile

𝒞-pres : ∀ {Γ A} M → (⊢M : Γ ⊢m M ⦂ A) → Γ ⊢c 𝒞 M ⊢M ⦂ A

𝒞o⇐-pres : ∀ {Γ T} (Mᴼ : Term) → (⊢M : Γ ⊢o Mᴼ ⇐ T) → Γ ⊢oc (𝒞o⇐ Mᴼ ⊢M) ⦂ T

𝒞o⇒-pres : ∀ {Γ T} (Mᴼ : Term) → (⊢M : Γ ⊢o Mᴼ ⇒ T) → Γ ⊢oc (𝒞o⇒ Mᴼ ⊢M) ⦂ T

𝒞o⇐-pres (ƛ N) (⊢lam ⊢N) = ⊢lam (𝒞o⇐-pres N ⊢N)
𝒞o⇐-pres (~ M at ℓ) (⊢splice ⊢M A~CodeT) = ⊢splice (⊢cast (𝒞-pres M ⊢M))
𝒞o⇐-pres M (⊢check-infer ⊢M) = 𝒞o⇒-pres M ⊢M

𝒞o⇒-pres (€ r # p) (⊢const T≡typeof) = ⊢const T≡typeof
𝒞o⇒-pres (` x) (⊢var ∋x) = ⊢var ∋x
𝒞o⇒-pres (L · M) (⊢app ⊢L ⊢M) = ⊢app (𝒞o⇒-pres L ⊢L) (𝒞o⇐-pres M ⊢M)
𝒞o⇒-pres (M ⦂ T) (⊢ann ⊢M) = ⊢ann (𝒞o⇐-pres M ⊢M)

𝒞-pres ($ r # p) (⊢const A≡typeof) = (⊢const A≡typeof)
𝒞-pres (` x) (⊢var ∋x) = ⊢var ∋x
𝒞-pres (ƛ A ˙ N) (⊢lam ⊢N) = ⊢lam (𝒞-pres N ⊢N)
𝒞-pres (L · M at ℓ) (⊢app ⊢L ⊢M A₁~B) = ⊢app (𝒞-pres L ⊢L) (⊢cast (𝒞-pres M ⊢M))
𝒞-pres (L · M at ℓ) (⊢app⋆ ⊢L ⊢M) =
  ⊢app (⊢cast (𝒞-pres L ⊢L)) (⊢cast (𝒞-pres M ⊢M))
𝒞-pres (≺ Mᴼ ≻) (⊢quote ⊢M) = ⊢quote (𝒞o⇒-pres Mᴼ ⊢M)
