open import Data.Nat
open import Data.List hiding ([_])
open import Function using (case_of_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; subst; sym)

module SubstitutionPreservesTypes where

open import Syntax

open import Utils
open import Types
open import Coercions
open import LanguageSyntax
open import TypeSystemMetaCC

WTRename_⦂_⇒_ : Rename → List Type → List Type → Set
WTRename_⦂_⇒_ ρ Γ Δ = ∀ {x A} → Γ ∋ x ⦂ A → Δ ∋ ρ x ⦂ A

ext-pres : ∀ {Γ Δ ρ} {A : Type}
  → WTRename ρ ⦂ Γ ⇒ Δ
    ----------------------------------------
  → WTRename ext ρ ⦂ (A ∷ Γ) ⇒ (A ∷ Δ)
ext-pres ⊢ρ {zero} eq = eq
ext-pres ⊢ρ {suc x} Γ∋x = ⊢ρ Γ∋x


rename-pres-oc : ∀ {Γ Δ : List Type} {T M ρ}
  → Γ ⊢oc M ⦂ T
  → WTRename ρ ⦂ Γ ⇒ Δ
    --------------------------------
  → Δ ⊢oc rename ρ M ⦂ T

rename-pres : ∀ {Γ Δ : List Type} {A M ρ}
  → Γ ⊢c M ⦂ A
  → WTRename ρ ⦂ Γ ⇒ Δ
    --------------------------------
  → Δ ⊢c rename ρ M ⦂ A

rename-pres-oc (⊢const T≡typeof) ⊢ρ = ⊢const T≡typeof
rename-pres-oc {Γ} {Δ} (⊢lam ⊢N) ⊢ρ =
  ⊢lam (rename-pres-oc ⊢N (λ {x} {T} → ext-pres {Γ} {Δ} ⊢ρ {x} {T}))
rename-pres-oc (⊢splice ⊢M) ⊢ρ = ⊢splice (rename-pres ⊢M ⊢ρ)
rename-pres-oc (⊢var Γ∋x) ⊢ρ = ⊢var (⊢ρ Γ∋x)
rename-pres-oc (⊢app ⊢L ⊢M) ⊢ρ =
  ⊢app (rename-pres-oc ⊢L ⊢ρ) (rename-pres-oc ⊢M ⊢ρ)
rename-pres-oc (⊢ann ⊢M) ⊢ρ = ⊢ann (rename-pres-oc ⊢M ⊢ρ)

rename-pres (⊢const A≡typeof) ⊢ρ = (⊢const A≡typeof)
rename-pres (⊢var Γ∋x) ⊢ρ = ⊢var (⊢ρ Γ∋x)
rename-pres {Γ} {Δ} (⊢lam ⊢N) ⊢ρ =
  ⊢lam (rename-pres ⊢N (λ {x} {A} → ext-pres {Γ} {Δ} ⊢ρ {x} {A}))
rename-pres (⊢app ⊢L ⊢M) ⊢ρ = ⊢app (rename-pres ⊢L ⊢ρ) (rename-pres ⊢M ⊢ρ)
rename-pres (⊢quote ⊢Mᴼ) ⊢ρ = ⊢quote (rename-pres-oc ⊢Mᴼ ⊢ρ)
rename-pres (⊢cast ⊢M) ⊢ρ = ⊢cast (rename-pres ⊢M ⊢ρ)
rename-pres ⊢blame ⊢ρ = ⊢blame

rename-↑1-pres : ∀ {Γ M A B}
  → Γ ⊢c M ⦂ B
    ------------------------------------------------------------
  → (A ∷ Γ) ⊢c rename (Syntax.↑ 1) M ⦂ B
rename-↑1-pres ⊢M = rename-pres ⊢M (λ {x} {A} Γ∋x → Γ∋x)

rename-↑1-pres-o : ∀ {Γ M A B}
  → Γ ⊢oc M ⦂ B
    ------------------------------------------------------------
  → (A ∷ Γ) ⊢oc rename (Syntax.↑ 1) M ⦂ B
rename-↑1-pres-o ⊢M = rename-pres-oc ⊢M (λ {x} {A} Γ∋x → Γ∋x)

WTSubstM_⦂_⇒_ : Subst → List Type → List Type → Set
WTSubstM σ ⦂ Γ ⇒ Δ = ∀ {x A} → Γ ∋ x ⦂ mtype A → Δ ⊢c σ x ⦂ A

WTSubstO_⦂_⇒_ : Subst → List Type → List Type → Set
WTSubstO σ ⦂ Γ ⇒ Δ = ∀ {x T} → Γ ∋ x ⦂ otype T → Δ ⊢oc σ x ⦂ T

exts-pres : ∀ {Γ Δ} {σ : Subst} {τ : Type}
  → WTSubstM σ ⦂ Γ ⇒ Δ
  → WTSubstM ext σ ⦂ (τ ∷ Γ) ⇒ (τ ∷ Δ)
exts-pres ⊢σ {0} eq = (⊢var eq)
exts-pres ⊢σ {suc x} Γ∋x = rename-↑1-pres (⊢σ Γ∋x)

exts-pres-o : ∀ {Γ Δ} {σ : Subst} {τ : Type}
  → WTSubstO σ ⦂ Γ ⇒ Δ
  → WTSubstO ext σ ⦂ (τ ∷ Γ) ⇒ (τ ∷ Δ)
exts-pres-o ⊢σ {0} eq = (⊢var eq)
exts-pres-o ⊢σ {suc x} Γ∋x = rename-↑1-pres-o (⊢σ Γ∋x)

subst-pres-oc : ∀ {Γ Δ : List Type} {A M σ}
  → Γ ⊢oc M ⦂ A
  → WTSubstM σ ⦂ Γ ⇒ Δ
  → WTSubstO σ ⦂ Γ ⇒ Δ
    -----------------------------------
  → Δ ⊢oc ⟪ σ ⟫ M ⦂ A

subst-pres : ∀ {Γ Δ : List Type} {A M σ}
  → Γ ⊢c M ⦂ A
  → WTSubstM σ ⦂ Γ ⇒ Δ
  → WTSubstO σ ⦂ Γ ⇒ Δ
    -----------------------------------
  → Δ ⊢c ⟪ σ ⟫ M ⦂ A

subst-pres-oc (⊢const T≡typeof) ⊢σₘ ⊢σₒ = ⊢const T≡typeof
subst-pres-oc {Γ} {Δ} (⊢lam ⊢N) ⊢σₘ ⊢σₒ =
  ⊢lam (subst-pres-oc ⊢N (λ {x} {A} → exts-pres {Γ} {Δ} ⊢σₘ {x} {A})
       (λ {x} {A} → exts-pres-o {Γ} {Δ} ⊢σₒ {x} {A}))
subst-pres-oc (⊢splice ⊢M) ⊢σₘ ⊢σₒ = ⊢splice (subst-pres ⊢M ⊢σₘ ⊢σₒ)
subst-pres-oc (⊢var Γ∋x) ⊢σₘ ⊢σₒ = ⊢σₒ Γ∋x
subst-pres-oc (⊢app ⊢L ⊢M) ⊢σₘ ⊢σₒ =
  ⊢app (subst-pres-oc ⊢L ⊢σₘ ⊢σₒ) (subst-pres-oc ⊢M ⊢σₘ ⊢σₒ)
subst-pres-oc (⊢ann ⊢M) ⊢σₘ ⊢σₒ = ⊢ann (subst-pres-oc ⊢M ⊢σₘ ⊢σₒ)

subst-pres (⊢const A≡typeof) ⊢σₘ ⊢σₒ = (⊢const A≡typeof)
subst-pres (⊢var Γ∋x) ⊢σₘ ⊢σₒ = ⊢σₘ Γ∋x
subst-pres {Γ} {Δ} (⊢lam ⊢N) ⊢σₘ ⊢σₒ =
  ⊢lam (subst-pres ⊢N (λ {x} {A} → exts-pres {Γ} {Δ} ⊢σₘ {x} {A})
       (λ {x} {A} → exts-pres-o {Γ} {Δ} ⊢σₒ {x} {A}))
subst-pres (⊢app ⊢L ⊢M) ⊢σₘ ⊢σₒ = ⊢app (subst-pres ⊢L ⊢σₘ ⊢σₒ) (subst-pres ⊢M ⊢σₘ ⊢σₒ)
subst-pres (⊢quote ⊢Mᴼ) ⊢σₘ ⊢σₒ = ⊢quote (subst-pres-oc ⊢Mᴼ ⊢σₘ ⊢σₒ)
subst-pres (⊢cast ⊢M) ⊢σₘ ⊢σₒ = ⊢cast (subst-pres ⊢M ⊢σₘ ⊢σₒ)
subst-pres ⊢blame ⊢σₘ ⊢σₒ = ⊢blame

substitution-pres : ∀ {Γ N V A B}
  → (mtype A ∷ Γ) ⊢c N ⦂ B
  → Γ ⊢c V ⦂ A
    ----------------------------
  → Γ ⊢c N [ V ] ⦂ B
substitution-pres ⊢N ⊢V =
  subst-pres ⊢N
    (λ { {0} refl → ⊢V ; {suc x} ∋x → ⊢var ∋x })
    (λ { {suc x} ∋x → ⊢var ∋x })
