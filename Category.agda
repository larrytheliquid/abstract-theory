module Category where

infix 2 _≡_

data _≡_ {A : Set} (a : A) : A → Set where
  refl : a ≡ a

data _∧_ (A B : Set) : Set where
  _,_ : A → B → A ∧ B

record Category : Set₁ where
  field
    S : Set
    _⇴_ : (A B : S) → Set

    e : {A : S} → A ⇴ A
    _⊙_ : {A B C : S}
      (x : A ⇴ B) (y : B ⇴ C) → A ⇴ C
    ident : {A B : S} (x : A ⇴ B) →
      (x ⊙ e ≡ x) ∧ (e ⊙ x ≡ x)
    assoc : {A B C D : S}
      (x : A ⇴ B) (y : B ⇴ C) (z : C ⇴ D) →
      (x ⊙ (y ⊙ z)) ≡ ((x ⊙ y) ⊙ z)

record Functor : Set₁ where
  field Α Β : Category
  open Category Α
  open Category Β renaming
    ( S to S′ ; _⇴_ to _⇴′_ ; e to e′ ; _⊙_ to _⊙′_ )

  field
    ∣f∣ : (X : S) → S′
    f : {X Y : S} (f : X ⇴ Y) → ∣f∣ X ⇴′ ∣f∣ Y
    preserves-e : {X : S} →
      f {X} e ≡ e′
    preserves-⊙ : {X Y Z : S}
      (x : X ⇴ Y) (y : Y ⇴ Z) →
      f (x ⊙ y) ≡ f x ⊙′ f y

