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
open import Relation.Nullary using (Dec; yes; no; ¬_; ¬?)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)
open import Relation.Nullary.Negation using (contradiction)
open import Function using (case_of_; case_return_of_)

module Progress where

open import Utils
open import Types
open import Syntax
open import LanguageSyntax
open import Coercions
open import TypeSystemMetaCC
open import Semantics
open import SubstitutionPreservesTypes


-- there is no meta language variables in the context
data EmptyM : List Type → Set where

  em-nil : EmptyM []

  em-cons : ∀ {Γ T}
    → EmptyM Γ
      ----------------------------
    → EmptyM (otype T ∷ Γ)

no-mtype : ∀ {Γ x A}
  → EmptyM Γ
    ----------------------------
  → ¬ (Γ ∋ x ⦂ mtype A)
no-mtype {x = suc x} (em-cons emΓ) Γ∋x = no-mtype {x = x} emΓ Γ∋x

data Progress : Term → Set where

  step : ∀ {M N}
    → M —→ₘ N
      ------------------------
    → Progress M

  done : ∀ {M}
    → MValue M
      ------------------------
    → Progress M

  err : ∀ {M ℓ}
    → M ≡ blame ℓ
      ------------------------
    → Progress M

data ProgressO : Term → Set where

  step : ∀ {Mᴼ Nᴼ}
    → Mᴼ —→ₒ Nᴼ
      ------------------------
    → ProgressO Mᴼ

  done : ∀ {Mᴼ}
    → IsSTLC Mᴼ
      ------------------------
    → ProgressO Mᴼ

  err : ∀ {Mᴼ ℓ}
    → Mᴼ ≡ (~ (blame ℓ))
      ----------------------------
    → ProgressO Mᴼ

{- Canonical form of a value of function type -}
data Fun : Term → Set where
  fun : ∀ {A N}
      ------------------------
    → Fun (lam A N)

  prim-fun : ∀ {ι p f}
      --------------------------------
    → Fun (const f (P-Fun ι p))

  fun-proxy : ∀ {A B C D} {M} {c : Cast C ⇒ A} {d : Cast B ⇒ D}
    → Fun M
      ----------------------------
    → Fun (M ⟨ cfun c d ⟩)

fun-is-val : ∀ {M}
  → Fun M
  → MValue M
fun-is-val fun = V-ƛ
fun-is-val prim-fun = V-const
fun-is-val (fun-proxy funM) = V-cast (fun-is-val funM) I-fun

canonical-fun : ∀ {Γ A B V}
  → Γ ⊢c V ⦂ A ⇒ B
  → MValue V
    ------------------------
  → Fun V
canonical-fun (⊢const {p = P-Fun ι p} A≡typeof) V-const = prim-fun
canonical-fun (⊢lam ⊢N) V-ƛ = fun
canonical-fun (⊢cast ⊢V) (V-cast v I-fun) = fun-proxy (canonical-fun ⊢V v)

data QuotedCode : Term → Set where
  code : ∀ {Mᴼ}
    → IsSTLC Mᴼ
      ------------------------
    → QuotedCode (qt Mᴼ)

canonical-code : ∀ {Γ T V}
  → Γ ⊢c V ⦂ Code T
  → MValue V
    ------------------------
  → QuotedCode V
canonical-code (⊢const CodeT≡typeofp) V-const =
  contradiction (sym CodeT≡typeofp) prim-not-code
canonical-code ⊢V (V-quote M-is-stlc) = code M-is-stlc
canonical-code (⊢cast ⊢V) (V-cast v ())

data Const : Base → Term → Set where
  base-const : ∀ {ι k}
      ------------------------------------
    → Const ι (const k (P-Base ι))

canonical-base : ∀ {Γ ι V}
  → Γ ⊢c V ⦂ ` ι
  → MValue V
    --------------------
  → Const ι V
canonical-base (⊢const {p = P-Base ι} refl) V-const = base-const
canonical-base (⊢cast ⊢V) (V-cast v ())

progress-oc : ∀ {Γ T Mᴼ}
  → Γ ⊢oc Mᴼ ⦂ T
  → EmptyM Γ
    ------------------------
  → ProgressO Mᴼ

progress : ∀ {Γ A M}
  → Γ ⊢c M ⦂ A
  → EmptyM Γ
    --------------------------------------------
  → Progress M

progress-oc (⊢const _) emΓ = done is-const
progress-oc (⊢var Γ∋x) emΓ = done is-var
progress-oc (⊢app ⊢Lᴼ ⊢Mᴼ) emΓ =
  case progress-oc ⊢Lᴼ emΓ of λ where
  (done L-is-stlc) →
    case progress-oc ⊢Mᴼ emΓ of λ where
    (done M-is-stlc) → done (is-· L-is-stlc M-is-stlc)
    (step M→M′) → step (ξ {F = (_ ·□) L-is-stlc} M→M′)
    (err refl) → step (ξ-splice-blame {F = (_ ·□) L-is-stlc})
  (step L→L′) → step (ξ {F = □· _} L→L′)
  (err refl) → step (ξ-splice-blame {F = □· _})
progress-oc (⊢ann ⊢Mᴼ) emΓ =
  case progress-oc ⊢Mᴼ emΓ of λ where
  (done M-is-stlc) → done (is-⦂ M-is-stlc)
  (step M→M′) → step (ξ {F = □⦂ _} M→M′)
  (err refl) → step (ξ-splice-blame {F = □⦂ _})
progress-oc (⊢lam ⊢M) emΓ =
  case progress-oc ⊢M (em-cons emΓ) of λ where
  (done M-is-stlc) → done (is-ƛ M-is-stlc)
  (step M→M′) → step (ξ {F = ƛ□} M→M′)
  (err refl) → step (ξ-splice-blame {F = ƛ□})
progress-oc (⊢splice ⊢M) emΓ =
  case progress ⊢M emΓ of λ where
  (done v) →
    case canonical-code ⊢M v of λ where
    (code M-is-stlc) → step (splice M-is-stlc)
  (step M→M′) → step (ξ-splice M→M′)
  (err refl) → err refl

progress (⊢var Γ∋x) emΓ = contradiction Γ∋x (no-mtype emΓ)
progress (⊢const A≡typeof) emΓ = done V-const
progress (⊢lam ⊢N) emΓ = done V-ƛ
progress (⊢app ⊢L ⊢M) emΓ =
  case progress ⊢L emΓ of λ where
  (step L→L′) → step (ξ {F = app□ _} L→L′)
  (err refl) → step (ξ-blame {F = app□ _})
  (done v) →
    case progress ⊢M emΓ of λ where
    (step M→M′) → step (ξ {F = (app _ □) v} M→M′)
    (err refl) → step (ξ-blame {F = (app _ □) v})
    (done w) →
      case canonical-fun ⊢L v of λ where
      fun → step (β w)  -- applying a λ
      prim-fun →        -- applying a primitive function
        case ⊢L of λ where
        (⊢const refl) →
          case canonical-base ⊢M w of λ where
          base-const → step δ
      (fun-proxy f) →   -- applying a function proxy
        step (fun-cast (fun-is-val f) w)
progress (⊢quote ⊢M) emΓ =
  case progress-oc ⊢M emΓ of λ where
  (done M-is-stlc) → done (V-quote M-is-stlc)
  (step M→M′) → step (ξ-quote M→M′)
  (err refl) → step quote-splice-blame  -- propagate blame through quote and splice
progress (⊢cast {c = c} ⊢M) emΓ
  with progress ⊢M emΓ
... | step M→M′ = step (ξ {F = □⟨ _ ⟩} M→M′)
... | (err refl) = step (ξ-blame {F = □⟨ _ ⟩})
... | done v with v | ⊢M | c
...   | V-const | ⊢const {p = P-Base _} refl | id _ =      -- casting a constant
  step (_—→ₘ_.id v)
...   | V-const | ⊢const {p = P-Fun ι p} refl | cfun c d = -- casting a primitive function
  done (V-cast v I-fun)
...   | V-ƛ | ⊢lam ⊢N | cfun c d = done (V-cast v I-fun)
...   | (V-quote M-is-stlc) | ⊢quote ⊢M | code-idT T = step (code-idT v)
...   | (V-quote M-is-stlc) | ⊢quote ⊢M | code-inj T = done (V-cast v I-code-inj)
...   | (V-cast v I-fun) | ⊢cast ⊢M | cfun c d =
  done (V-cast (V-cast v I-fun) I-fun)
...   | (V-cast v I-inj) | ⊢cast ⊢M | id ⋆ = step (_—→ₘ_.id (V-cast v I-inj))
...   | (V-cast {A} {.⋆} v (I-inj {g = g})) | ⊢cast ⊢M | proj B ℓ {h} =
  case mtype-eq? A B of λ where
  (yes refl) →
    case ground-eq g h of λ where
    refl → step (proj v)
  (no A≢B) → step (proj-blame v A≢B)
...   | (V-cast v I-code-inj) | ⊢cast ⊢M | code-id⋆ = step (code-id⋆ (V-cast v I-code-inj))
...   | (V-cast v (I-code-inj {S})) | ⊢cast ⊢M | code-proj T ℓ =
  case otype-eq? S T of λ where
  (yes refl) → step (code-proj v)
  (no S≢T) → step (code-proj-blame v S≢T)
...   | (V-cast v I-code-inj) | ⊢cast ⊢M | id A {()}
...   | v | _ | inj _ = done (V-cast v I-inj)
...   | v | _ | cseq c d = step (seq v)
progress ⊢blame _ = (err refl)
