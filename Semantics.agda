open import Level using (lift)
open import Data.List using (List; []; _∷_; length)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool  using (Bool) renaming (_≟_ to _=?_)
open import Data.Integer using (ℤ) renaming (_≟_ to _=int_)
open import Data.Product using (_×_; proj₁; proj₂; ∃-syntax) renaming (_,_ to ⟨_,_⟩ )
open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Vec using (Vec) renaming ([] to []̌; _∷_ to _∷̌_)
open import Data.Unit using (tt) renaming (⊤ to Top)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym)

open import Utils

module Semantics where

open import LanguageSyntax
open import Coercions

{- The STLC subset of the code language -}
data IsSTLC : Term → Set where

  is-const : ∀ {p : Prim} {r : rep p}
      ------------------------------------
    → IsSTLC (€ r # p)

  is-var : ∀ {x}
      ----------------
    → IsSTLC (` x)

  is-ƛ : ∀ {N}
    → IsSTLC N
      ----------------
    → IsSTLC (ƛ N)

  is-· : ∀ {L M}
    → IsSTLC L
    → IsSTLC M
      ----------------
    → IsSTLC (L · M)

  is-⦂ : ∀ {M T}
    → IsSTLC M
      --------------------
    → IsSTLC (M ⦂ T)

infix 2 _—→ₒ_
infix 2 _—→ₘ_

data _—→ₒ_ : Term → Term → Set
data _—→ₘ_  : Term → Term → Set

data OFrame : Set where
  □·_ : Term → OFrame

  _·□ : (M : Term) → IsSTLC M → OFrame

  □⦂_ : (T : OType) → OFrame

  ƛ□ : OFrame

plugₒ : Term → OFrame → Term
plugₒ Lᴼ (□· Mᴼ)     = Lᴼ · Mᴼ
plugₒ Mᴼ ((Lᴼ ·□) _) = Lᴼ · Mᴼ
plugₒ Mᴼ (□⦂ T)      = Mᴼ ⦂ T
plugₒ Nᴼ (ƛ□)        = ƛ Nᴼ

data _—→ₒ_ where

  ξ : ∀ {Mᴼ Nᴼ} {F : OFrame}
    → Mᴼ —→ₒ Nᴼ
      ------------------------------------
    → plugₒ Mᴼ F  —→ₒ plugₒ Nᴼ F

  ξ-splice : ∀ {Mꟲ Nꟲ}
    → Mꟲ —→ₘ Nꟲ
      --------------------
    → ~ Mꟲ —→ₒ ~ Nꟲ

  ξ-splice-blame : ∀ {ℓ} {F : OFrame}
      ----------------------------------------
    → plugₒ (~ (blame ℓ)) F —→ₒ ~ (blame ℓ)

  splice : ∀ {Mᴼ}
    → IsSTLC Mᴼ
      ----------------------------
    → ~ (qt Mᴼ) —→ₒ Mᴼ


data MValue : Term → Set where

  V-const : ∀ {p : Prim} {r : rep p}
      ------------------------------------
    → MValue (const r p)

  V-ƛ : ∀ {A Nꟲ}
      ------------------------------------
    → MValue (lam A Nꟲ)

  V-quote : ∀ {Mᴼ}
    → IsSTLC Mᴼ
      --------------------
    → MValue (qt Mᴼ)

  V-cast : ∀ {A B Vꟲ} {c : Cast A ⇒ B}
    → MValue Vꟲ
    → Inert c
      --------------------------------
    → MValue (Vꟲ ⟨ c ⟩)

data MFrame : Set where

  app□_ : Term → MFrame

  app_□ : (Vꟲ : Term) → (v : MValue Vꟲ) →  MFrame

  □⟨_⟩ : ∀ {A B} → Cast A ⇒ B → MFrame

plugₘ : Term → MFrame → Term
plugₘ Lꟲ (app□ Mꟲ) = app Lꟲ Mꟲ
plugₘ Mꟲ (app Vꟲ □ v) = app Vꟲ Mꟲ
plugₘ Mꟲ □⟨ c ⟩ = Mꟲ ⟨ c ⟩

data _—→ₘ_ where

  ξ : ∀ {Mꟲ Nꟲ} {F : MFrame}
    → Mꟲ —→ₘ Nꟲ
      --------------------------------
    → plugₘ Mꟲ F —→ₘ plugₘ Nꟲ F

  ξ-blame : ∀ {ℓ} {F : MFrame}
      ------------------------------------
    → plugₘ (blame ℓ) F —→ₘ blame ℓ

  ξ-quote : ∀ {Mᴼ Nᴼ}
    → Mᴼ —→ₒ Nᴼ
      ------------------------
    → qt Mᴼ —→ₘ qt Nᴼ

  β : ∀ {A Nꟲ Vꟲ}
    → MValue Vꟲ
      ----------------------------------------
    → app (lam A Nꟲ) Vꟲ —→ₘ Nꟲ [ Vꟲ ]

  δ : ∀ {ι p} {f k}
      --------------------------------------------------------------------
    → app (const f (P-Fun ι p)) (const k (P-Base ι)) —→ₘ (const (f k) p)

  fun-cast : ∀ {A B C D Vꟲ Wꟲ} {c : Cast C ⇒ A} {d : Cast B ⇒ D}
    → MValue Vꟲ
    → MValue Wꟲ
      ----------------------------------------------------------------
    → app (Vꟲ ⟨ cfun c d ⟩) Wꟲ —→ₘ (app Vꟲ (Wꟲ ⟨ c ⟩)) ⟨ d ⟩

  id : ∀ {A Vꟲ} {a : Atomic A}
    → MValue Vꟲ
      ------------------------------------
    → Vꟲ ⟨ id A {a} ⟩ —→ₘ Vꟲ

  proj : ∀ {G Vꟲ} {g : Ground G} {ℓ}
    → MValue Vꟲ
      ----------------------------------------
    → Vꟲ ⟨ inj G {g} ⟩ ⟨ proj G ℓ {g} ⟩ —→ₘ Vꟲ

  proj-blame : ∀ {G H Vꟲ} {g : Ground G} {h : Ground H} {ℓ}
    → MValue Vꟲ
    → G ≢ H
      ----------------------------------------------------
    → Vꟲ ⟨ inj G {g} ⟩ ⟨ proj H ℓ {h} ⟩ —→ₘ blame ℓ

  seq : ∀ {A B C Vꟲ} {c : Cast A ⇒ B} {d : Cast B ⇒ C}
    → MValue Vꟲ
      ----------------------------------------------------
    → Vꟲ ⟨ cseq c d ⟩ —→ₘ Vꟲ ⟨ c ⟩ ⟨ d ⟩

  {- cast application for coercions between Code types -}
  code-id⋆ : ∀ {Vꟲ}
    → MValue Vꟲ
      --------------------------------
    → Vꟲ ⟨ code-id⋆ ⟩ —→ₘ Vꟲ

  code-idT : ∀ {T Vꟲ}
    → MValue Vꟲ
      --------------------------------
    → Vꟲ ⟨ code-idT T ⟩ —→ₘ Vꟲ

  code-proj : ∀ {T Vꟲ ℓ}
    → MValue Vꟲ
      ----------------------------------------------------
    → Vꟲ ⟨ code-inj T ⟩ ⟨ code-proj T ℓ ⟩ —→ₘ Vꟲ

  code-proj-blame : ∀ {S T Vꟲ ℓ}
    → MValue Vꟲ
    → S ≢ T
      ----------------------------------------------------
    → Vꟲ ⟨ code-inj S ⟩ ⟨ code-proj T ℓ ⟩ —→ₘ blame ℓ

  quote-splice-blame : ∀ {ℓ}
      ------------------------------------
    → qt (~ (blame ℓ)) —→ₘ blame ℓ


infix  2 _—↠_
infixr 2 _—→⟨_⟩_
infix  3 _∎

data _—↠_ : Term → Term → Set where
  _∎ : ∀ M
      ------------
    → M —↠ M

  _—→⟨_⟩_ : ∀ L {M N}
    → L —→ₘ M
    → M —↠ N
      ------------
    → L —↠ N

open import TypeSystemMetaCC

canonical-codeT : ∀ {Γ V T}
  → Γ ⊢c V ⦂ Code T
  → MValue V
  → ∃[ M ] (V ≡ qt M ) × (IsSTLC M)
canonical-codeT (⊢const {p = P-Base _} ()) V-const
canonical-codeT (⊢const {p = P-Fun _ _} ()) V-const
canonical-codeT ⊢V (V-quote is-stlc) = ⟨ _ , refl , is-stlc ⟩
