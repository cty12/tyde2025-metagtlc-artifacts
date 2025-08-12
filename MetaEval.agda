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
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym)
open import Relation.Nullary.Negation using (contradiction)
open import Function using (case_of_; case_return_of_)

module MetaEval where

open import BlameLabels
open import LanguageSyntax
open import TypeSystemMetaGTLC
open import TypeSystemMetaCC
open import Semantics
open import Compile
open import CompilePres
open import Progress
open import Preservation

data Result : Set where
  timeout : Result
  error : Label → Result
  stlc : (M : Term) → IsSTLC M → Result

data ⊢_⦂_ : Result → OType → Set where
  ⊢timeout : ∀ {T} → ⊢ timeout ⦂ T
  ⊢error : ∀ {ℓ T} → ⊢ error ℓ ⦂ T
  ⊢stlc : ∀ {M T}
    → [] ⊢oc M ⦂ T
    → (M-is-stlc : IsSTLC M)
    → ⊢ stlc M M-is-stlc ⦂ T

meta-eval-cc : ∀ {T} M → [] ⊢c M ⦂ Code T → (k : ℕ) → Result
meta-eval-cc M ⊢M 0 = timeout
meta-eval-cc M ⊢M (suc k) with progress ⊢M em-nil
... | step {N = N} M→N = meta-eval-cc N (pres ⊢M M→N) k
... | (err {ℓ = ℓ} _) = error ℓ
... | done (V-const {p} {r}) =
  case ⊢M of λ where
  (⊢const Code≡typeof) →
    contradiction (sym Code≡typeof) prim-not-code
... | done (V-cast v i) =
  case ⟨ ⊢M , i ⟩ of λ where
  ⟨ ⊢cast _ , () ⟩
... | done (V-quote M-is-stlc) = stlc _ M-is-stlc

meta-eval : ∀ {T} M → [] ⊢m M ⦂ Code T → (k : ℕ) → Result
meta-eval M ⊢M k = meta-eval-cc (𝒞 M ⊢M) (𝒞-pres M ⊢M) k

meta-eval-cc-safe : ∀ {T} M → (⊢M : [] ⊢c M ⦂ Code T) → (k : ℕ) → ⊢ meta-eval-cc M ⊢M k ⦂ T
meta-eval-cc-safe M ⊢M 0 = ⊢timeout
meta-eval-cc-safe M ⊢M (suc k) with progress ⊢M em-nil
... | step {N = N} M→N = meta-eval-cc-safe N (pres ⊢M M→N) k
... | (err {ℓ = ℓ} _) = ⊢error
... | done (V-const {p} {r}) =
  case ⊢M of λ where
  (⊢const Code≡typeof) →
    contradiction (sym Code≡typeof) prim-not-code
... | done (V-cast v i) =
  case ⟨ ⊢M , i ⟩ of λ where
  ⟨ ⊢cast _ , () ⟩
... | done (V-quote Mᴼ-is-stlc) =
  case ⊢M of λ where
  (⊢quote ⊢Mᴼ) → ⊢stlc ⊢Mᴼ Mᴼ-is-stlc

meta-eval-safe : ∀ {T} M → (⊢M : [] ⊢m M ⦂ Code T) → (k : ℕ) → ⊢ meta-eval M ⊢M k ⦂ T
meta-eval-safe M ⊢M k = meta-eval-cc-safe (𝒞 M ⊢M) (𝒞-pres M ⊢M) k
