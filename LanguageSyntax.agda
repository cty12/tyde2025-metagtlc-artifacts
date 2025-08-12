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

module LanguageSyntax where

open import Syntax
open import Types public
open import BlameLabels
open import Coercions

data Op : Set where
  -- TODO: add primitives to the code language
  op-const  : (p : Prim) → rep p → Op
  op-lam    : Op
  op-app    : Op
  op-ann    : OType → Op
  op-splice : Op
  op-spliceꟲ : Label → Op

  op-constᴹ   : (p : Prim) → rep p → Op
  op-lamᴹ   : MType → Op
  op-appᴹ   : Label → Op
  op-quoteᴹ : Op

  op-constꟲ   : (p : Prim) → rep p → Op
  op-lamꟲ   : MType → Op
  op-appꟲ   : Op
  op-quoteꟲ : Op
  op-castꟲ  : ∀ {A B} → Cast A ⇒ B → Op
  op-blameꟲ : Label → Op


sig : Op → List Sig
-- code lang
sig (op-const p r) = []
sig op-lam = (ν ■) ∷ []
sig op-app = ■ ∷ ■ ∷ []
sig (op-ann T) = ■ ∷ []
sig op-splice = ■ ∷ []
sig (op-spliceꟲ ℓ) = ■ ∷ []
-- meta lang
sig (op-constᴹ p r)  = []
sig (op-lamᴹ A) = (ν ■) ∷ []
sig (op-appᴹ ℓ) = ■ ∷ ■ ∷ []
sig op-quoteᴹ = ■ ∷ []
-- meta CC
sig (op-constꟲ p r) = []
sig (op-lamꟲ A) = (ν ■) ∷ []
sig op-appꟲ = ■ ∷ ■ ∷ []
sig op-quoteꟲ = ■ ∷ []
sig (op-castꟲ c) = ■ ∷ []
sig (op-blameꟲ ℓ) = []


open Syntax.OpSig Op sig renaming (ABT to Term; plug to plug-abt) public

infixl 7  _·_
infixl 7  _·_at_
infix 8 _⟨_⟩

-- code lang syntax
pattern €_#_ r p = (op-const p r) ⦅ nil ⦆
pattern ƛ N     = op-lam ⦅ cons (bind (ast N)) nil ⦆
pattern _·_ L M = op-app ⦅ cons (ast L) (cons (ast M) nil) ⦆
pattern _⦂_ M T = (op-ann T) ⦅ cons (ast M) nil ⦆
pattern ~_ Mᴹ = op-splice ⦅ cons (ast Mᴹ) nil ⦆
pattern ~_at_ Mᴹ ℓ = (op-spliceꟲ ℓ) ⦅ cons (ast Mᴹ) nil ⦆
-- meta lang syntax
pattern $_#_ r p     = (op-constᴹ p r) ⦅ nil ⦆
pattern ƛ_˙_ A N     = (op-lamᴹ A) ⦅ cons (bind (ast N)) nil ⦆
pattern _·_at_ L M ℓ = (op-appᴹ ℓ) ⦅ cons (ast L) (cons (ast M) nil) ⦆
pattern ≺_≻ M        = op-quoteᴹ ⦅ cons (ast M) nil ⦆
-- meta CC syntax
pattern const r p = (op-constꟲ p r) ⦅ nil ⦆
pattern lam A N = (op-lamꟲ A) ⦅ cons (bind (ast N)) nil ⦆
pattern app L M = op-appꟲ ⦅ cons (ast L) (cons (ast M) nil) ⦆
pattern qt M = op-quoteꟲ ⦅ cons (ast M) nil ⦆
pattern _⟨_⟩ M c = (op-castꟲ c) ⦅ cons (ast M) nil ⦆
pattern blame ℓ = (op-blameꟲ ℓ) ⦅ nil ⦆
