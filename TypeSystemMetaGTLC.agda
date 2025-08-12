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

module TypeSystemMetaGTLC where

open import Syntax
open import Types
open import LanguageSyntax
open import Coercions

infix 4 _⊢o_⇐_
infix 4 _⊢o_⇒_
infix 4 _⊢m_⦂_

{- typing of the code language -}
data _⊢o_⇐_ : List Type → Term → OType → Set
data _⊢o_⇒_ : List Type → Term → OType → Set
{- typing of the meta language -}
data _⊢m_⦂_  : List Type → Term → MType → Set


data _⊢o_⇒_ where

  ⊢const : ∀ {Γ T}{p : Prim}{r : rep p}
    → T ≡ typeof-o p
      ------------------------
    → Γ ⊢o (€ r # p) ⇒ T

  ⊢var : ∀ {Γ T x}
    → Γ ∋ x ⦂ otype T
      --------------------
    → Γ ⊢o ` x ⇒ T

  ⊢app : ∀ {Γ S T Lᴼ Mᴼ}
    → Γ ⊢o Lᴼ ⇒ (S ⇒ T)
    → Γ ⊢o Mᴼ ⇐ S
      --------------------
    → Γ ⊢o Lᴼ · Mᴼ ⇒ T

  ⊢ann : ∀ {Γ T Mᴼ}
    → Γ ⊢o Mᴼ ⇐ T
      ------------------------
    → Γ ⊢o Mᴼ ⦂ T ⇒ T

  -- can't have, for the static GG
  -- ⊢splice : ∀ {Γ A Mᴹ}
  --   → Γ ⊢ Mᴹ ⦂ Code A
  --     ------------------------
  --   → Γ ⊢o ~ Mᴹ ⇒ A


{- counter example to the splice rule in syn mode:
lambda x:code<int>. < let y = (~ x) in 1 + y > // type checks
⊑
lambda x:code<*>. < let y = (~ x) in 1 + y > // won't type check
-}

data _⊢o_⇐_ where

  ⊢lam : ∀ {Γ S T Nᴼ}
    → (otype S ∷ Γ) ⊢o Nᴼ ⇐ T
      ------------------------
    → Γ ⊢o ƛ Nᴼ ⇐ (S ⇒ T)

  ⊢splice : ∀ {Γ A T Mᴹ ℓ}
    → Γ ⊢m Mᴹ ⦂ A
    → A ~ Code T
      ------------------------
    → Γ ⊢o ~ Mᴹ at ℓ ⇐ T

  ⊢check-infer : ∀ {Γ T Mᴼ}
    → Γ ⊢o Mᴼ ⇒ T
      --------------------
    → Γ ⊢o Mᴼ ⇐ T


data _⊢m_⦂_ where

  ⊢const : ∀ {Γ A}{p : Prim}{r : rep p}
    → A ≡ typeof p
      --------------------
    → Γ ⊢m ($ r # p) ⦂ A

  ⊢var : ∀ {Γ A}{x : ℕ}
    → Γ ∋ x ⦂ mtype A
      ----------------
    → Γ ⊢m ` x ⦂ A

  ⊢lam : ∀ {Γ A B}{Nᴹ}
    → (mtype A ∷ Γ) ⊢m Nᴹ ⦂ B
      --------------------
    → Γ ⊢m ƛ A ˙ Nᴹ ⦂ (A ⇒ B)

  ⊢app : ∀ {Γ A₁ A₂ B}{Lᴹ Mᴹ}{ℓ}
    → Γ ⊢m Lᴹ ⦂ (A₁ ⇒ A₂)
    → Γ ⊢m Mᴹ ⦂ B
    → A₁ ~ B
      ----------------------------
    → Γ ⊢m Lᴹ · Mᴹ at ℓ ⦂ A₂

  ⊢app⋆ : ∀ {Γ A}{Lᴹ Mᴹ}{ℓ}
    → Γ ⊢m Lᴹ ⦂ ⋆
    → Γ ⊢m Mᴹ ⦂ A
      ----------------------------
    → Γ ⊢m Lᴹ · Mᴹ at ℓ ⦂ ⋆

  ⊢quote : ∀ {Γ T Mᴼ}
    → Γ ⊢o Mᴼ ⇒ T
      ----------------------------
    → Γ ⊢m ≺ Mᴼ ≻ ⦂ Code T
