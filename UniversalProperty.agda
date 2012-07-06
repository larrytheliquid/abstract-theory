module UniversalProperty where
open import Prelude
open import Equiv

record Universal {A X Y : Set} (a : A) (P : A → X → Y → Set) : Set₁ where
  field
    F : X → Y
    charn : (x : X) (y : Y) →
      F x ≡ y ⇔ P a x y


