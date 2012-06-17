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
  open Category Α renaming
    ( S to ∣Α∣ ; _⇴_ to _⇴₁_ ; e to e₁ ; _⊙_ to _⊙₁_ )
  open Category Β renaming
    ( S to ∣Β∣ ; _⇴_ to _⇴₂_ ; e to e₂ ; _⊙_ to _⊙₂_ )

  field
    φ : (X : ∣Α∣) → ∣Β∣
    ψ : {X Y : ∣Α∣} (f : X ⇴₁ Y) → φ X ⇴₂ φ Y
    preserves-e : {X : ∣Α∣} →
      ψ {X} e₁ ≡ e₂
    preserves-⊙ : {X Y Z : ∣Α∣}
      (f : X ⇴₁ Y) (g : Y ⇴₁ Z) →
      ψ (f ⊙₁ g) ≡ ψ f ⊙₂ ψ g

