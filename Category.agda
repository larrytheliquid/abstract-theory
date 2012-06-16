module Category where

infix 2 _≡_

data _≡_ {A : Set} (a : A) : A → Set where
  refl : a ≡ a

data _×_ (A B : Set) : Set where
  _,_ : A → B → A × B

record Category : Set₁ where
  field
    S : Set
    _⇴_ : (A B : S) → Set
    e : {A : S} → A ⇴ A
    _⊙_ : {A B C : S}
      (g : B ⇴ C) (f : A ⇴ B) → A ⇴ C
    ident-law : {A B : S} (f : A ⇴ B) →
      (f ⊙ e ≡ f) × (e ⊙ f ≡ f)
    assoc-law : {A B C D : S}
      (h : C ⇴ D) (g : B ⇴ C) (f : A ⇴ B) →
      (h ⊙ (g ⊙ f)) ≡ ((h ⊙ g) ⊙ f)
  
