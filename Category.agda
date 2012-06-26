module Category where

infix 2 _≡_

data _≡_ {A : Set} (a : A) : A → Set where
  refl : a ≡ a

data _∧_ (A B : Set) : Set where
  _,_ : A → B → A ∧ B

record Category : Set₁ where
  infixr 9 _⊙_

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

record Functor (C D : Category) : Set₁ where
  open Category C
  open Category D renaming
    ( U to U′ ; _⇴_ to _⇴′_ ; e to e′ ; _⊙_ to _⊙′_ )

  field
    ∣f∣ : (X : U) → U′
    f : {X Y : U} (f : X ⇴ Y) → ∣f∣ X ⇴′ ∣f∣ Y
    preserves-e : {X : U} →
      f {X} e ≡ e′
    preserves-⊙ : {X Y Z : U}
      (x : X ⇴ Y) (y : Y ⇴ Z) →
      f (x ⊙ y) ≡ f x ⊙′ f y

record NaturalTransformation {C D} (F G : Functor C D) : Set₁ where
  open Functor F
  open Functor G renaming ( ∣f∣ to ∣g∣ ; f to g )
  open Category C
  open Category D renaming
    ( U to U′ ; _⇴_ to _⇴′_ ; e to e′ ; _⊙_ to _⊙′_ )

  field
    h : {A B : U} → A ⇴ B → ∣f∣ A ⇴′ ∣g∣ B
    natural : {A B C D : U}
      (x : A ⇴ B) (y : B ⇴ C) (z : C ⇴ D) →
      h (x ⊙ y ⊙ z) ≡ f x ⊙′ h y ⊙′ g z
