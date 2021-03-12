module PigeonholePrinciple where

open import Relation.Binary.PropositionalEquality.Core
open import Relation.Binary.Definitions
open import Function.Base
open import Data.Empty
open import Data.Product
open import Data.Sum renaming (_⊎_ to _∨_)
open import Data.Nat.Base
open import Data.Fin.Base as F
open import Data.Fin.Properties
  
-- record Bijective {A B : Set} (f : A → B) : Set where
--   constructor bijective
--   field
--     f⁻¹ : B → A
--     f∘f⁻¹≡id : ∀ x → (f ∘ f⁻¹) x ≡ x
--     f⁻¹∘f≡id : ∀ x → (f⁻¹ ∘ f) x ≡ x
  
record NonInjective {A B : Set} (f : A → B) : Set where
  constructor collision
  field
    x : A
    y : A
    x≢y : x ≢ y
    fx≡fy : f x ≡ f y

record Shrinked {n : ℕ} (f : Fin (suc (suc n)) → Fin (suc n)) : Set where
  constructor shrinked
  field
    ϕ : Fin (suc n) → Fin n
    perm  : Fin n → Fin (suc n)
    perm∘ϕ≡f∘suc : ∀ x → (perm ∘ ϕ) x ≡ (f ∘ suc) x
  
Pigeonhole1 : (n : ℕ) → Set
Pigeonhole1 n = ∀ (f : Fin (suc n) → Fin n) → NonInjective f

down : ∀ n (x y : Fin (suc n)) → x F.< y → Fin n
down zero zero (suc y) _ with toℕ<n (suc y)
down zero zero (suc y) _ | s≤s ()
down (suc n) zero y z<y = zero
down (suc n) (suc x) (suc y) (s≤s x<y) = suc (down n x y x<y)

find-collision : ∀ {n} (f : Fin (suc (suc n)) → Fin (suc n)) → NonInjective f ∨ (∀ x → f (suc x) ≢ f zero)
find-collision = {!!}
  
shrink : ∀ {n} {y} (f : Fin (suc (suc n)) → Fin (suc n)) → (∀ x → f (suc x) ≢ y) → Shrinked f
shrink {n} {y} f f'x≢y = {!!}
  where
    ϕ' : (x : Fin (suc n)) → f (suc x) ≢ y → Fin n
    ϕ' x f'x≢y with f (suc x) | (<-cmp (f (suc x)) y)
    ϕ' x f'x≢y | f'x | tri< f'x<y _ _ = down n f'x y f'x<y
    ϕ' x f'x≢y | f'x | tri≈ _ f'x≡y _ = ⊥-elim (f'x≢y f'x≡y)
    ϕ' x f'x≢y | suc w | tri> _ _ f'x>y = w

    ϕ : Fin (suc n) → Fin n
    ϕ x = ϕ' x (f'x≢y x)

pigeonhole1 : ∀ n → Pigeonhole1 n
pigeonhole1 0 f = ⊥-elim (¬Fin0 (f zero))
pigeonhole1 (suc n) f with find-collision f
... | inj₁ noninj-f = noninj-f
... | inj₂ fx≢fz = induce (shrink f fx≢fz)
  where
    induce : Shrinked f → NonInjective f
    induce (shrinked ϕ perm perm∘ϕ≡f∘suc) = collision x' y' x'≢y' fx'≡fy'
      where
        noninj-ϕ : NonInjective ϕ
        noninj-ϕ = pigeonhole1 n ϕ

        open NonInjective noninj-ϕ renaming (fx≡fy to ϕx≡ϕy)
        open ≡-Reasoning
  
        x' : Fin (suc (suc n))
        x' = suc x
  
        y' : Fin (suc (suc n))
        y' = suc y

        x'≢y' : x' ≢ y'
        x'≢y' x'≡y' = x≢y (suc-injective x'≡y')

        fx'≡fy' : f x' ≡ f y'
        fx'≡fy' = begin
          f x'         ≡˘⟨ perm∘ϕ≡f∘suc x ⟩
          (perm ∘ ϕ) x ≡⟨ cong perm ϕx≡ϕy ⟩
          (perm ∘ ϕ) y ≡⟨ perm∘ϕ≡f∘suc y ⟩
          f y'         ∎
