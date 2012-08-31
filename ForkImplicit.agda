module ForkImplicit where
open import Prelude public
open import Equiv public

record Fork : Set₁ where
  field
    fork : {A B C : Set} (f : A → B) (g : A → C) → A → B × C
    charn : {A B C : Set} (f : A → B) (g : A → C)
      (h : A → B × C) (a : A) →
         h a ≡ (fork f g) a
      ⇔ (π₁ ∘ h) a ≡ f a × (π₂ ∘ h) a ≡ g a

{-
  (f : A → B) (g : A → C) (a : A) →
  Σ (B × C) λ bc →
  π₁ bc ≡ f a
    ×
  π₂ bc ≡ g a
-}

data PairL (A B : Set) : A → Set where
  _,_ : (a : A) → B → PairL A B a

data PairR (A B : Set) : B → Set where
  _,_ : A → (b : B) → PairR A B b

data Σ (A : Set) (B : A → Set) : Set where
  _,_ : (a : A) → B a → Σ A B

ifork : {A B C : Set} (f : A → B) (g : A → C) (a : A) →
  PairL B C (f a) × PairR B C (g a)
ifork f g a = (f a , g a) , (f a , g a)

record Fork′ : Set₁ where
  field
    charn : {A B C : Set} (f : A → B) (g : A → C)
      (fork : {A B C : Set} → (A → B) → (A → C) → A → B × C)
      (h : A → B × C) (a : A) →
         h a ≡ (fork f g) a
      ⇔ (π₁ ∘ h) a ≡ f a × (π₂ ∘ h) a ≡ g a


