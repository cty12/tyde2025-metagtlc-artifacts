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

module TypeSystemMetaCC where

open import Syntax
open import Types
open import LanguageSyntax
open import Coercions

infix 4 _⊢oc_⦂_
infix 4 _⊢c_⦂_

{- typing of the code language after cast insertion -}
data _⊢oc_⦂_ : List Type → Term → OType → Set
{- typing of meta CC -}
data _⊢c_⦂_   : List Type → Term → MType → Set

data _⊢oc_⦂_ where

  ⊢const : ∀ {Γ T}{p : Prim}{r : rep p}
    → T ≡ typeof-o p
      ------------------------
    → Γ ⊢oc (€ r # p) ⦂ T

  ⊢var : ∀ {Γ T x}
    → Γ ∋ x ⦂ otype T
      --------------------
    → Γ ⊢oc ` x ⦂ T

  ⊢lam : ∀ {Γ S T Nᴼ}
    → (otype S ∷ Γ) ⊢oc Nᴼ ⦂ T
      ------------------------
    → Γ ⊢oc ƛ Nᴼ ⦂ (S ⇒ T)

  ⊢app : ∀ {Γ S T Lᴼ Mᴼ}
    → Γ ⊢oc Lᴼ ⦂ (S ⇒ T)
    → Γ ⊢oc Mᴼ ⦂ S
      --------------------
    → Γ ⊢oc Lᴼ · Mᴼ ⦂ T

  ⊢ann : ∀ {Γ T Mᴼ}
    → Γ ⊢oc Mᴼ ⦂ T
      ------------------------
    → Γ ⊢oc (Mᴼ ⦂ T) ⦂ T

  ⊢splice : ∀ {Γ T Mꟲ}
    → Γ ⊢c Mꟲ ⦂ (Code T)
      ------------------------
    → Γ ⊢oc ~ Mꟲ ⦂ T


data _⊢c_⦂_ where

  ⊢const : ∀ {Γ A}{p : Prim}{r : rep p}
    → A ≡ typeof p
      --------------------
    → Γ ⊢c const r p ⦂ A

  ⊢var : ∀ {Γ A}{x : ℕ}
    → Γ ∋ x ⦂ mtype A
      ----------------
    → Γ ⊢c ` x ⦂ A

  ⊢lam : ∀ {Γ A B}{Nꟲ}
    → (mtype A ∷ Γ) ⊢c Nꟲ ⦂ B
      --------------------
    → Γ ⊢c lam A Nꟲ ⦂ (A ⇒ B)

  ⊢app : ∀ {Γ A B}{Lꟲ Mꟲ}
    → Γ ⊢c Lꟲ ⦂ (A ⇒ B)
    → Γ ⊢c Mꟲ ⦂ A
      ----------------------------
    → Γ ⊢c app Lꟲ Mꟲ ⦂ B

  ⊢quote : ∀ {Γ T Mᴼ}
    → Γ ⊢oc Mᴼ ⦂ T
      ----------------------------
    → Γ ⊢c qt Mᴼ ⦂ Code T

  ⊢cast : ∀ {Γ A B Mꟲ} {c : Cast A ⇒ B}
    → Γ ⊢c Mꟲ ⦂ A
      ----------------------------
    → Γ ⊢c Mꟲ ⟨ c ⟩ ⦂ B

  ⊢blame : ∀ {Γ A ℓ}
      ----------------------------
    → Γ ⊢c blame ℓ ⦂ A
