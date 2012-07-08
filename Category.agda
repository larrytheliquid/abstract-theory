module Category where
open import Prelude
open import Equiv

record Category : Set₁ where
  infixr 9 _⊙_

  field
    U : Set
    _⇴_ : (A B : U) → Set

    e : {A : U} → A ⇴ A
    _⊙_ : {A B C : U}
      (x : A ⇴ B) (y : B ⇴ C) → A ⇴ C
    ident : {A B : U} (x : A ⇴ B) →
      (x ⊙ e ≡ x) × (e ⊙ x ≡ x)
    assoc : {A B C D : U}
      (x : A ⇴ B) (y : B ⇴ C) (z : C ⇴ D) →
      (x ⊙ (y ⊙ z)) ≡ ((x ⊙ y) ⊙ z)

record Functor (C D : Category) : Set where
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

record NaturalTransformation′ {C D} (F G : Functor C D) : Set where
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

record NaturalTransformation {C D} (F G : Functor C D) : Set where
  open Functor F
  open Functor G renaming ( ∣f∣ to ∣g∣ ; f to g )
  open Category C
  open Category D renaming
    ( U to U′ ; _⇴_ to _⇴′_ ; e to e′ ; _⊙_ to _⊙′_ )

  field
    h : {A : U} → ∣f∣ A ⇴′ ∣g∣ A
    natural : {A B : U} (x : A ⇴ B) →
      h ⊙′ g x ≡ f x ⊙′ h

record Adjunction {Α Β} (F : Functor Α Β) (G : Functor Β Α) : Set where
  open Functor F
  open Functor G renaming ( ∣f∣ to ∣g∣ ; f to g )
  open Category Α
  open Category Β renaming
    ( U to U′ ; _⇴_ to _⇴′_ ; e to e′ ; _⊙_ to _⊙′_ )

  field
    η : {A : U} → A ⇴ ∣g∣ (∣f∣ A)
    ε : {B : U′} → ∣f∣ (∣g∣ B) ⇴′ B
    adjunction : {A : U} {B : U′}
      (φ : A ⇴ ∣g∣ B) (ψ : ∣f∣ A ⇴′ B) →
      φ ≡ η ⊙ g ψ ⇔ ψ ≡ f φ ⊙′ ε

record Isomorphism′ (C : Category) : Set where
  open Category C
  field
    {A B} : U
    f : A ⇴ B
    fº : B ⇴ A
    f⊙fº≡e : f ⊙ fº ≡ e
    fº⊙f≡e : fº ⊙ f ≡ e

record Isomorphism (C : Category) : Set where
  open Category C
  field
    {A B} : U
    f : A ⇴ B
    fº : B ⇴ A
    X : U
    charn : (a : X ⇴ A) (b : X ⇴ B) →
      a ≡ b ⊙ fº ⇔ b ≡ a ⊙ f
