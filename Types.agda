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
open import Relation.Nullary using (¬_; ¬?; Dec; yes; no; recompute)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym)
open import Relation.Nullary.Negation using (contradiction)

module Types where

  open import Utils

  {- Base Types -}
  data Base : Set where
      Nat : Base
      Int : Base
      𝔹 : Base
      Unit : Base

  -- maps base types to their Agda types
  base-rep : Base → Set
  base-rep Nat = ℕ
  base-rep Int = ℤ
  base-rep 𝔹 = Bool
  base-rep Unit = Top

  base-eq? : ∀ (ι₁ ι₂ : Base) → Dec (ι₁ ≡ ι₂)
  base-eq? Nat Nat = yes refl
  base-eq? Nat Int = no λ ()
  base-eq? Nat 𝔹 = no λ ()
  base-eq? Nat Unit = no λ ()
  base-eq? Int Nat = no λ ()
  base-eq? Int Int = yes refl
  base-eq? Int 𝔹 = no λ ()
  base-eq? Int Unit = no λ ()
  base-eq? 𝔹 Nat = no λ ()
  base-eq? 𝔹 Int = no λ ()
  base-eq? 𝔹 𝔹 = yes refl
  base-eq? 𝔹 Unit = no λ ()
  base-eq? Unit Nat = no λ ()
  base-eq? Unit Int = no λ ()
  base-eq? Unit 𝔹 = no λ ()
  base-eq? Unit Unit = yes refl

  {- Primitive Types -}
  data Prim : Set where
      P-Base : Base → Prim
      P-Fun : Base → Prim → Prim

  -- maps primitive types to their Agda types
  rep : Prim → Set
  rep (P-Base b)  = base-rep b
  rep (P-Fun b p) = (base-rep b) → rep p


  {- Types of the Code Language -}
  module OTypes where

    data OType : Set where
      `_ : Base → OType
      _⇒_   : OType → OType → OType

    otype-eq? : ∀ (S T : OType) → Dec (S ≡ T)
    otype-eq? (` ι₁) (` ι₂)  with base-eq? ι₁ ι₂
    ... | yes refl = yes refl
    ... | no ι₁≢ι₁ = no λ { refl → contradiction refl ι₁≢ι₁ }
    otype-eq? (` _) (T ⇒ T₁) = no λ ()
    otype-eq? (S ⇒ S₁) (` _) = no λ ()
    otype-eq? (S₁ ⇒ S₂) (T₁ ⇒ T₂)
      with otype-eq? S₁ T₁ | otype-eq? S₂ T₂
    ... | yes refl | yes refl = yes refl
    ... | no neq | yes refl = no λ { refl → contradiction refl neq }
    ... | yes refl | no neq = no λ { refl → contradiction refl neq }
    ... | no neq | no _ = no λ { refl → contradiction refl neq }

    typeof-o : Prim → OType
    typeof-o (P-Base ι) = ` ι
    typeof-o (P-Fun ι p) = (` ι) ⇒ (typeof-o p)


  {- Types of the Meta Language -}
  module MTypes where

    open OTypes using (OType)

    infix  7 _⇒_
    infix 10 `_

    data MType : Set where
      ⋆ : MType
      `_ : Base → MType
      _⇒_ : MType → MType → MType
      Code⋆ : MType
      Code : OType → MType

    mtype-eq? : ∀ (A B : MType) → Dec (A ≡ B)
    mtype-eq? ⋆ ⋆ = yes refl
    mtype-eq? ⋆ (` x) = no λ ()
    mtype-eq? ⋆ (B ⇒ B₁) = no λ ()
    mtype-eq? ⋆ Code⋆ = no λ ()
    mtype-eq? ⋆ (Code x) = no λ ()
    mtype-eq? (` x) ⋆ = no λ ()
    mtype-eq? (` ι₁) (` ι₂) with base-eq? ι₁ ι₂
    ... | yes refl = yes refl
    ... | no ι₁≢ι₁ = no λ { refl → contradiction refl ι₁≢ι₁ }
    mtype-eq? (` x) (B ⇒ B₁) = no λ ()
    mtype-eq? (` x) Code⋆ = no λ ()
    mtype-eq? (` x) (Code x₁) = no λ ()
    mtype-eq? (A ⇒ A₁) ⋆ = no λ ()
    mtype-eq? (A ⇒ A₁) (` x) = no λ ()
    mtype-eq? (A ⇒ B) (C ⇒ D) with mtype-eq? A C | mtype-eq? B D
    ... | yes refl | yes refl = yes refl
    ... | yes refl | no B≢B = no λ { refl → contradiction refl B≢B }
    ... | no A≢A | yes refl = no λ { refl → contradiction refl A≢A }
    ... | no A≢A | no _ = no λ { refl → contradiction refl A≢A }
    mtype-eq? (A ⇒ A₁) Code⋆ = no λ ()
    mtype-eq? (A ⇒ A₁) (Code x) = no λ ()
    mtype-eq? Code⋆ ⋆ = no λ ()
    mtype-eq? Code⋆ (` x) = no λ ()
    mtype-eq? Code⋆ (B ⇒ B₁) = no λ ()
    mtype-eq? Code⋆ Code⋆ = yes refl
    mtype-eq? Code⋆ (Code x) = no λ ()
    mtype-eq? (Code x) ⋆ = no λ ()
    mtype-eq? (Code x) (` x₁) = no λ ()
    mtype-eq? (Code x) (B ⇒ B₁) = no λ ()
    mtype-eq? (Code x) Code⋆ = no λ ()
    mtype-eq? (Code T₁) (Code T₂) with OTypes.otype-eq? T₁ T₂
    ... | yes refl = yes refl
    ... | no neq = no λ { refl → contradiction refl neq }

    eq-unk? : (A : MType) → Dec (A ≡ ⋆)
    eq-unk? A = mtype-eq? A ⋆

    typeof : Prim → MType
    typeof (P-Base ι) = ` ι
    typeof (P-Fun ι p) = (` ι) ⇒ (typeof p)

    prim-not-code : ∀ {p T} → typeof p ≢ Code T
    prim-not-code {P-Base _} = λ ()
    prim-not-code {P-Fun _ _} = λ ()

    data Atomic : MType → Set where
      A-Unk  : Atomic ⋆
      A-Base : ∀{ι} → Atomic (` ι)

    {- Type consistency -}
    infix  5  _~_

    data _~_ : MType → MType → Set where

      unk~L : ∀ {A} → ⋆ ~ A

      unk~R : ∀ {A} → A ~ ⋆

      base~ : ∀ {ι} → ` ι ~ ` ι

      fun~ : ∀ {A B A' B'}
        → A ~ A'  →  B ~ B'
          -------------------
        → (A ⇒ B) ~ (A' ⇒ B')

      code~ : ∀ {T}
        → Code T ~ Code T

      code⋆~ : Code⋆ ~ Code⋆

      code⋆~L : ∀ {T}
        → Code⋆ ~ Code T

      code⋆~R : ∀ {T}
        → Code T ~ Code⋆

    ~-sym : ∀ {A B} → A ~ B → B ~ A
    ~-sym unk~L = unk~R
    ~-sym unk~R = unk~L
    ~-sym base~ = base~
    ~-sym (fun~ A~A' B~B') = fun~ (~-sym A~A') (~-sym B~B')
    ~-sym code~ = code~
    ~-sym code⋆~ = code⋆~
    ~-sym code⋆~L = code⋆~R
    ~-sym code⋆~R = code⋆~L

    data Ground : MType → Set where
      G-Base : ∀{ι} → Ground (` ι)
      G-Fun : Ground (⋆ ⇒ ⋆)
      G-Code : Ground Code⋆

    ground : (A : MType) → .{nd : A ≢ ⋆} → ∃[ B ] Ground B × (A ~ B)
    ground ⋆ {nd} = contradiction refl (recompute (¬? (yes refl)) nd)
    ground (` ι) {nd} = ⟨ ` ι , G-Base , base~ ⟩
    ground (A ⇒ B) {nd} = ⟨ ⋆ ⇒ ⋆ , G-Fun , fun~ unk~R unk~R ⟩
    ground (Code T) = ⟨ Code⋆ , G-Code , code⋆~R ⟩
    ground Code⋆ = ⟨ Code⋆ , G-Code , code⋆~ ⟩

    ground? : (A : MType) → Dec (Ground A)
    ground? ⋆ = no λ ()
    ground? (` ι) = yes (G-Base)
    ground? (A₁ ⇒ A₂) with eq-unk? A₁ | eq-unk? A₂
    ... | yes eq1 | yes eq2 rewrite eq1 | eq2 = yes G-Fun
    ... | yes eq | no neq rewrite eq = no λ gnd → ground⇒2 gnd neq
      where
      ground⇒2 : ∀{A}{B} → Ground (A ⇒ B) → B ≢ ⋆ → ⊥
      ground⇒2 G-Fun nd = nd refl
    ... | no neq | _ = no λ gnd → ground⇒1 gnd neq
      where
      ground⇒1 : ∀{A}{B} → Ground (A ⇒ B) → A ≢ ⋆ → ⊥
      ground⇒1 G-Fun nd = nd refl
    ground? Code⋆ = yes G-Code
    ground? (Code T) = no λ ()

    ground-eq : ∀ {A} → (g : Ground A) → (h : Ground A) → g ≡ h
    ground-eq G-Base G-Base = refl
    ground-eq G-Fun G-Fun = refl
    ground-eq G-Code G-Code = refl


  open OTypes public
  open MTypes public

  data Type : Set where
    otype : OType → Type
    mtype : MType → Type
