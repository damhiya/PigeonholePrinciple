module PigeonholePrinciple where

open import Relation.Nullary
open import Relation.Binary.PropositionalEquality.Core
open import Relation.Binary.Definitions
open import Function.Base
open import Data.Empty
open import Data.Product
open import Data.Sum renaming (_⊎_ to _∨_)
open import Data.Nat.Base as ℕ
open import Data.Nat.Properties as ℕ hiding (_≟_)
open import Data.Fin.Base as F
open import Data.Fin.Properties as F

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
    punch  : Fin n → Fin (suc n)
    punch∘ϕ≡f∘suc : ∀ x → (punch ∘ ϕ) x ≡ (f ∘ suc) x
  
Pigeonhole1 : (n : ℕ) → Set
Pigeonhole1 n = ∀ (f : Fin (suc n) → Fin n) → NonInjective f

find-collision : ∀ {n} (f : Fin (suc (suc n)) → Fin (suc n)) → NonInjective f ∨ (∀ x → f (suc x) ≢ f zero)
find-collision {n} f = result
  where
    fz : Fin (suc n)
    fz = f zero

    z≢sz : ∀ {m} {n : Fin m} → F.zero ≢ suc n
    z≢sz ()
  
    ≤z : ∀ {n} (x : Fin (suc n)) → x F.≤ zero → x ≡ zero
    ≤z zero z≤n = refl
  
    x≤m⇒x≡m∨x≤m-1 : ∀ {A : Set} (x : Fin (suc n)) m-1 →
      (m-1<n : m-1 ℕ.< n) → (toℕ x ℕ.≤ suc m-1) → (x ≡ suc (fromℕ< m-1<n) → A) → (toℕ x ℕ.≤ m-1 → A) → A
    x≤m⇒x≡m∨x≤m-1 x m-1 m-1<n x≤m f g with ℕ.<-cmp (toℕ x) (suc m-1)
    x≤m⇒x≡m∨x≤m-1 x m-1 m-1<n x≤m f g | tri< x<m _ _ = g (+-cancelˡ-≤ 1 x<m)
    x≤m⇒x≡m∨x≤m-1 x m-1 m-1<n x≤m f g | tri≈ _ x≡m _ with fromℕ<-cong (toℕ x) (suc m-1) x≡m (s≤s (ℕ.≤-trans x≤m m-1<n)) (s≤s m-1<n)
    x≤m⇒x≡m∨x≤m-1 x m-1 m-1<n x≤m f g | tri≈ _ x≡m _ | fromℕ<-toℕ-x≡m with fromℕ<-toℕ x (s≤s (ℕ.≤-trans x≤m m-1<n))
    x≤m⇒x≡m∨x≤m-1 x m-1 m-1<n x≤m f g | tri≈ _ x≡m _ | fromℕ<-toℕ-x≡m | fromℕ<-toℕ-x≡x = f (trans (sym fromℕ<-toℕ-x≡x) fromℕ<-toℕ-x≡m)
    x≤m⇒x≡m∨x≤m-1 x m-1 m-1<n x≤m f g | tri> _ _ x>m = ⊥-elim (<⇒≱ x>m x≤m)
  
    test : ∀ (m : ℕ) → (m ℕ.≤ n) → NonInjective f ∨ (∀ (x : Fin (suc n)) → toℕ x ℕ.≤ m → f (suc x) ≢ fz)
    test zero _ with fz ≟ f (suc zero)
    ... | yes fz≡fsz = inj₁ (collision zero (suc zero) z≢sz fz≡fsz)
    ... | no  fz≢fsz = inj₂ (λ x x≤z fsx≡fz → fz≢fsz (trans (sym fsx≡fz) (cong (f ∘ suc) (≤z x x≤z))))
    test (suc m-1) m-1<n with test m-1 (ℕ.≤-trans (n≤1+n m-1) m-1<n) | fz ≟ f (suc (suc (fromℕ< m-1<n)))
    test (suc m-1) m-1<n | inj₁ noninj-f | _ = inj₁ noninj-f
    test (suc m-1) m-1<n | inj₂ fsx≢fz   | yes fz≡fsm = inj₁ (collision zero (suc (suc (fromℕ< m-1<n))) z≢sz fz≡fsm)
    test (suc m-1) m-1<n | inj₂ fsx≢fz   | no  fz≢fsm = inj₂ (λ x x≤m fsx≡fz →
      x≤m⇒x≡m∨x≤m-1 x m-1 m-1<n x≤m
        (λ x≡m → fz≢fsm (trans (sym fsx≡fz) (cong (f ∘ suc) x≡m)))
        (λ x≤m-1 → fsx≢fz x x≤m-1 fsx≡fz))

    test-n : NonInjective f ∨ (∀ x → toℕ x ℕ.≤ n → f (suc x) ≢ fz)
    test-n = test n ℕ.≤-refl

    x≤n : ∀ (x : Fin (suc n)) → toℕ x ℕ.≤ n
    x≤n x with toℕ<n x
    ... | s≤s p = p
    
    result : NonInjective f ∨ (∀ x → f (suc x) ≢ fz)
    result with test-n
    ... | inj₁ noninj-f = inj₁ noninj-f
    ... | inj₂ fsx≢fz   = inj₂ λ x → fsx≢fz x (x≤n x)
  
shrink : ∀ {n} {y} (f : Fin (suc (suc n)) → Fin (suc n)) → (∀ x → f (suc x) ≢ y) → Shrinked f
shrink {n} {y} f f'x≢y = shrinked ϕ punch punch∘ϕ≡f∘suc
  where
    ϕ : Fin (suc n) → Fin n
    ϕ x = punchOut (≢-sym (f'x≢y x))

    punch  : Fin n → Fin (suc n)
    punch x = punchIn y x

    punch∘ϕ≡f∘suc : ∀ x → (punch ∘ ϕ) x ≡ (f ∘ suc) x
    punch∘ϕ≡f∘suc x = punchIn-punchOut (≢-sym (f'x≢y x))

pigeonhole1 : ∀ n → Pigeonhole1 n
pigeonhole1 0 f = ⊥-elim (¬Fin0 (f zero))
pigeonhole1 (suc n) f with find-collision f
... | inj₁ noninj-f = noninj-f
... | inj₂ fx≢fz = induce (shrink f fx≢fz)
  where
    induce : Shrinked f → NonInjective f
    induce shrinked-f = collision x' y' x'≢y' fx'≡fy'
      where
        open Shrinked shrinked-f

        noninj-ϕ : NonInjective ϕ
        noninj-ϕ = pigeonhole1 n ϕ

        open NonInjective noninj-ϕ renaming (fx≡fy to ϕx≡ϕy)
        open ≡-Reasoning
  
        x' : Fin (suc (suc n))
        x' = suc x
  
        y' : Fin (suc (suc n))
        y' = suc y

        x'≢y' : x' ≢ y'
        x'≢y' x'≡y' = x≢y (F.suc-injective x'≡y')

        fx'≡fy' : f x' ≡ f y'
        fx'≡fy' = begin
          f x'         ≡˘⟨ punch∘ϕ≡f∘suc x ⟩
          (punch ∘ ϕ) x ≡⟨ cong punch ϕx≡ϕy ⟩
          (punch ∘ ϕ) y ≡⟨ punch∘ϕ≡f∘suc y ⟩
          f y'         ∎
