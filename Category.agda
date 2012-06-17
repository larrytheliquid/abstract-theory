module Category where

infix 2 _≡_

data _≡_ {A : Set} (a : A) : A → Set where
  refl : a ≡ a

data _∧_ (A B : Set) : Set where
  _,_ : A → B → A ∧ B

record Category : Set₁ where
  field
    U : Set
    _⇴_ : (A B : U) → Set

    e : {A : U} → A ⇴ A
    _⊙_ : {A B C : U}
      (x : A ⇴ B) (y : B ⇴ C) → A ⇴ C
    ident : {A B : U} (x : A ⇴ B) →
      (x ⊙ e ≡ x) ∧ (e ⊙ x ≡ x)
    assoc : {A B C D : U}
      (x : A ⇴ B) (y : B ⇴ C) (z : C ⇴ D) →
      (x ⊙ (y ⊙ z)) ≡ ((x ⊙ y) ⊙ z)

record Functor : Set₁ where
  field Α Β : Category
  open Category Α
  open Category Β renaming
    ( U to U′ ; _⇴_ to _⇴′_ ; e to e′ ; _⊙_ to _⊙′_ )

  field
    ∣f∣ : (X : U) → U′
    f : {X Y : U} (f : X ⇴ Y) → ∣f∣ X ⇴′ ∣f∣ Y
    preserves-e : {X : U} →
      f {X} e ≡ e′
    preserves-⊙ : {X Y Z : U}
      (x : X ⇴ Y) (y : Y ⇴ Z) →
      f (x ⊙ y) ≡ f x ⊙′ f y

