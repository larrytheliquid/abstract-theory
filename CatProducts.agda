module CatProducts where

infix 2 _≡_

data _≡_ {A : Set} (a : A) : A → Set where
  refl : a ≡ a

data _∧_ (A B : Set) : Set where
  _,_ : A → B → A ∧ B

record Category : Set₁ where
  field
    S : Set
    _×_ : (A B : S) → S
    _⇴_ : (A B : S) → Set
    e : {A : S} → A ⇴ A
    _⊙_ : {A B C : S}
      (x : A ⇴ B) (y : B ⇴ C) → A ⇴ C
    _⊛_ : {A B C : S}
      (x : A ⇴ B) (y : A ⇴ C) → A ⇴ (B × C)
    ident-law : {A B : S} (x : A ⇴ B) →
      (x ⊙ e ≡ x) ∧ (e ⊙ x ≡ x)
    assoc-law : {A B C D : S}
      (x : A ⇴ B) (y : B ⇴ C) (z : C ⇴ D) →
      (x ⊙ (y ⊙ z)) ≡ ((x ⊙ y) ⊙ z)
  
