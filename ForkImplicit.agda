module ForkImplicit where
open import Prelude public
open import Equiv public

record Fork : Set₁ where
  field
    fork : {A B C : Set} (f : A → B) (g : A → C) → A → B × C
    charn : {A B C : Set} (f : A → B) (g : A → C) (h : A → B × C) (a : A) →
         h a ≡ (fork f g) a
      ⇔ (π₁ ∘ h) a ≡ f a × (π₂ ∘ h) a ≡ g a

