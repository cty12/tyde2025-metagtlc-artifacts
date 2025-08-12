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

open import BlameLabels
open import LanguageSyntax
open import Coercions
open import Semantics

-- example
M : Term
M = app (lam (Code (` Unit)) (qt (ƛ (~ (app (` 1) (qt ( ` 0))))))) (lam (Code (` Unit)) (qt (ƛ (~ (` 1)))))

_ : M —↠ qt (ƛ (ƛ (` 1)))
_ = _ -- (λ. ≺ λ. ~ ((var 1) ≺ var 0 ≻) ≻) (λ. ≺ λ. ~ (var 1) ≻)
        —→⟨ β V-ƛ ⟩
    -- ≺ λ. ~((λ. ≺ λ. ~ (var 1) ≻) ≺ var 0 ≻) ≻
    qt (ƛ (~ app (lam (Code (` Unit)) (qt (ƛ (~ (` 1))))) (qt (` 0))))
        —→⟨ ξ-quote (ξ {F = ƛ□} (ξ-splice (β (V-quote is-var)))) ⟩
    -- ≺ λ. ~ ≺ λ. ~ ≺ var 1 ≻ ≻ ≻
    qt (ƛ (~ qt (ƛ (~ qt (` 1)))))
        —→⟨ ξ-quote (ξ {F = ƛ□} (ξ-splice (ξ-quote (ξ {F = ƛ□} (splice is-var))))) ⟩
    -- ≺ λ. ~ ≺ λ. (var 1) ≻ ≻
    qt (ƛ (~ qt (ƛ (` 1))))
        —→⟨ ξ-quote (ξ {F = ƛ□} (splice (is-ƛ is-var))) ⟩
    -- ≺ λ. λ. (var 1) ≻
    qt (ƛ (ƛ (` 1))) ∎
