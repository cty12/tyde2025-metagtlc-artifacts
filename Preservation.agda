open import Level using (lift)
open import Data.List using (List; []; _∷_; length)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool  using (Bool) renaming (_≟_ to _=?_)
open import Data.Integer using (ℤ) renaming (_≟_ to _=int_)
open import Data.Product using (∃; ∃-syntax; _×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩ )
open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Vec using (Vec) renaming ([] to []̌; _∷_ to _∷̌_)
open import Data.Unit using (tt) renaming (⊤ to Top)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)
open import Relation.Nullary using (Dec; yes; no; ¬_; ¬?)
open import Relation.Nullary.Negation using (contradiction)

module Preservation where

open import Utils
open import Types
open import Syntax
open import LanguageSyntax
open import Coercions
open import TypeSystemMetaCC
open import Semantics
open import SubstitutionPreservesTypes

plugₘ-inv : ∀ {Γ} {M} {F : MFrame} {A}
   → Γ ⊢c plugₘ M F ⦂ A
     --------------------------------------------------------------------
   → ∃[ B ] Γ ⊢c M ⦂ B × (∀ M' → Γ ⊢c M' ⦂ B → Γ ⊢c plugₘ M' F ⦂ A)
plugₘ-inv {F = app□ x} (⊢app ⊢L ⊢M) = ⟨ _ , ⊢L , (λ M′ ⊢M′ → ⊢app ⊢M′ ⊢M) ⟩
plugₘ-inv {F = app V □ v} (⊢app ⊢V ⊢M) = ⟨ _ , ⊢M , (λ M ⊢M′ → ⊢app ⊢V ⊢M′) ⟩
plugₘ-inv {F = □⟨ c ⟩} (⊢cast ⊢M) = ⟨ _ , ⊢M , (λ M ⊢M′ → ⊢cast ⊢M′) ⟩

pres-oc : ∀ {Γ T Mᴼ Nᴼ}
  → Γ ⊢oc Mᴼ ⦂ T
  → Mᴼ —→ₒ Nᴼ
    --------------------
  → Γ ⊢oc Nᴼ ⦂ T

pres : ∀ {Γ A M N}
  → Γ ⊢c M ⦂ A
  → M —→ₘ N
    --------------------
  → Γ ⊢c N ⦂ A

pres-oc ⊢LM (ξ {F = □· M} L→N) with ⊢LM
... | (⊢app ⊢L ⊢M) = ⊢app (pres-oc ⊢L L→N) ⊢M
pres-oc ⊢VM (ξ {F = (V ·□) v} M→N) with ⊢VM
... | (⊢app ⊢V ⊢M) = ⊢app ⊢V (pres-oc ⊢M M→N)
pres-oc ⊢M⦂T (ξ {F = □⦂ T} M→N) with ⊢M⦂T
... | (⊢ann ⊢M) = ⊢ann (pres-oc ⊢M M→N)
pres-oc ⊢ƛM (ξ {F = ƛ□} M→N) with ⊢ƛM
... | ⊢lam ⊢M = ⊢lam (pres-oc ⊢M M→N)
pres-oc (⊢splice ⊢Mꟲ) (ξ-splice Mꟲ→Nꟲ) = ⊢splice (pres ⊢Mꟲ Mꟲ→Nꟲ)
pres-oc (⊢splice (⊢quote ⊢Nᴼ)) (splice v) = ⊢Nᴼ
pres-oc _ ξ-splice-blame = ⊢splice ⊢blame

pres ⊢M (ξ {M} {N} {F} M→N) with plugₘ-inv ⊢M
... | ⟨ _ , ⊢M′ , plug-wt ⟩ = plug-wt N (pres ⊢M′ M→N)
pres ⊢M ξ-blame with plugₘ-inv ⊢M
... | ⟨ _ , ⊢M′ , plug-wt ⟩ = ⊢blame
pres (⊢quote ⊢Mᴼ) (ξ-quote Mᴼ→Nᴼ) = ⊢quote (pres-oc ⊢Mᴼ Mᴼ→Nᴼ)
pres (⊢app (⊢lam ⊢N) ⊢V) (β v) = substitution-pres ⊢N ⊢V
pres (⊢app (⊢const refl) (⊢const _)) δ = ⊢const refl
pres (⊢app (⊢cast ⊢V) ⊢W) (fun-cast v w) = ⊢cast (⊢app ⊢V (⊢cast ⊢W))
pres (⊢cast ⊢V) (id v) = ⊢V
pres (⊢cast (⊢cast ⊢V)) (proj v) = ⊢V
pres _ (proj-blame v G≢H) = ⊢blame
pres (⊢cast ⊢V) (seq v) = ⊢cast (⊢cast ⊢V)
pres (⊢cast ⊢V) (code-id⋆ v) = ⊢V
pres (⊢cast ⊢V) (code-idT v) = ⊢V
pres (⊢cast (⊢cast ⊢V)) (code-proj v) = ⊢V
pres _ (code-proj-blame v S≢T) = ⊢blame
pres _ quote-splice-blame = ⊢blame

pres-mult : ∀ {Γ A M N}
  → Γ ⊢c M ⦂ A
  → M —↠ N
    --------------------
  → Γ ⊢c N ⦂ A
pres-mult ⊢M (_ ∎) = ⊢M
pres-mult ⊢M (_ —→⟨ M→L ⟩ L↠N) = pres-mult (pres ⊢M M→L) L↠N
