module ForkImplicit where
open import Equiv public

infix 4 _≡_

data _≡_ {A : Set} (a : A) : A → Set where
  equal : a ≡ a

infix  3 _×_
infixr 4 _,_

record _×_ (A B : Set) : Set where
  constructor _,_
  field
    π₁ : A
    π₂ : B
open _×_ public

record Fork : Set₁ where
  field
    fork : {A B C : Set} (f : A → B) (g : A → C) → A → B × C
    charn : {A B C : Set} (f : A → B) (g : A → C) (h : A → B × C) (a : A) →
          (π₁ ∘ h) a ≡ f a 
        × (π₂ ∘ h) a ≡ g a
      ⇔ h a ≡ (fork f g) a

