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
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)

module Coercions where

  open import Types
  open import BlameLabels
  open import Utils

  data Cast_⇒_ : MType → MType → Set where
    id : ∀ (A : MType)  → {a : Atomic A} → Cast A ⇒ A
    inj : ∀ (A : MType) → {g : Ground A} → Cast A ⇒ ⋆
    proj : ∀ (B : MType) → Label → {g : Ground B} → Cast ⋆ ⇒ B
    cfun : ∀ {A B A' B'}
      → Cast B  ⇒ A
      → Cast A' ⇒ B'
      → Cast (A ⇒ A') ⇒ (B ⇒ B')
    cseq : ∀ {A B C} → Cast A ⇒ B → Cast B ⇒ C → Cast A ⇒ C
    -- new
    code-id⋆  : Cast Code⋆ ⇒ Code⋆
    code-idT  : ∀ (T : OType) → Cast (Code T) ⇒ (Code T)
    code-inj  : ∀ (T : OType) → Cast (Code T) ⇒ Code⋆
    code-proj : ∀ (T : OType) → Label → Cast Code⋆ ⇒ (Code T)


  data Inert : ∀ {A B} → Cast A ⇒ B → Set where

    I-inj : ∀ {A g} → Inert (inj A {g})

    I-fun : ∀ {A B A' B' c d} → Inert (cfun {A} {B} {A'} {B'} c d)

    I-code-inj : ∀ {T} → Inert (code-inj T)

  {- The coerce function takes two consistent types A and B, a blame label, and
  returns a coercion from A to B -}
  coerce : ∀ (A B : MType) → {c : A ~ B} → Label → Cast A ⇒ B

  coerce-to-gnd   : (A B : MType) → {g : Ground B} → {c : A ~ B} → Label → Cast A ⇒ B
  coerce-from-gnd : (A B : MType) → {g : Ground A} → {c : A ~ B} → Label → Cast A ⇒ B

  coerce-to⋆ : (A : MType) → Label → Cast A ⇒ ⋆
  coerce-to⋆ A ℓ with eq-unk? A
  ... | yes eq rewrite eq = id ⋆ {A-Unk}
  ... | no neq with ground? A
  ...     | yes g = inj A {g}
  ...     | no ng with ground A {neq}
  ...        | ⟨ G , g , A~G ⟩ = cseq (coerce-to-gnd A G {g} {A~G} ℓ) (inj G {g})

  coerce-from⋆ : (B : MType) → Label → Cast ⋆ ⇒ B
  coerce-from⋆ B ℓ with eq-unk? B
  ... | yes eq rewrite eq = id ⋆ {A-Unk}
  ... | no neq with ground? B
  ...     | yes g = proj B ℓ {g}
  ...     | no ng with ground B {neq}
  ...        | ⟨ G , g , B~G ⟩ = cseq (proj G ℓ {g}) (coerce-from-gnd G B {g} {~-sym B~G} ℓ)

  coerce-to-gnd .⋆ B {g} {unk~L} ℓ = proj B ℓ {g}
  coerce-to-gnd A .⋆ {()} {unk~R} ℓ
  coerce-to-gnd (` ι) (` ι) {gb} {base~} ℓ = id (` ι) {A-Base}
  coerce-to-gnd (A₁ ⇒ A₂) .(⋆ ⇒ ⋆) {G-Fun} {fun~ c c₁} ℓ =
     cfun (coerce-from⋆ A₁ (flip ℓ)) (coerce-to⋆ A₂ ℓ)
  coerce-to-gnd Code⋆ Code⋆ {G-Code} {code⋆~} ℓ = code-id⋆
  coerce-to-gnd (Code T) Code⋆ {G-Code} {code⋆~R} ℓ = code-inj T

  coerce-from-gnd .⋆ B {()} {unk~L} ℓ
  coerce-from-gnd A .⋆ {g} {unk~R} ℓ = inj A {g}
  coerce-from-gnd (` ι) (` ι) {ga} {base~} ℓ = id (` ι)  {A-Base}
  coerce-from-gnd (⋆ ⇒ ⋆) (B₁ ⇒ B₂) {G-Fun} {fun~ c c₁} ℓ =
     cfun (coerce-to⋆ B₁ (flip ℓ)) (coerce-from⋆ B₂ ℓ)
  coerce-from-gnd Code⋆ (Code T) {G-Code} {code⋆~L} ℓ = code-proj T ℓ
  coerce-from-gnd Code⋆ Code⋆ {G-Code} {code⋆~} ℓ = code-id⋆

  coerce .⋆ B {unk~L} ℓ = coerce-from⋆ B ℓ
  coerce A .⋆ {unk~R} ℓ = coerce-to⋆ A ℓ
  coerce (` ι) .(` ι) {base~} ℓ = id (` ι) {A-Base}
  coerce (A ⇒ B) (C ⇒ D) {fun~ A~C B~D} ℓ =
    cfun (coerce C A {~-sym A~C} (flip ℓ)) (coerce B D {B~D} ℓ)
  coerce (Code T) .(Code T) {code~} ℓ = code-idT T
  coerce Code⋆ Code⋆ {code⋆~} ℓ = code-id⋆
  coerce Code⋆ (Code T) {code⋆~L} ℓ = code-proj T ℓ
  coerce (Code T) Code⋆ {code⋆~R} ℓ = code-inj T
