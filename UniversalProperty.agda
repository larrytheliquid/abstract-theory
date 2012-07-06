module UniversalProperty where
open import Prelude
open import Equiv

record Universal {A X Y : Set} (a : A) (P : A → X → Y → Set) : Set₁ where
  field
    F : X → Y
    charn : (x : X) (y : Y) →
      F x ≡ y ⇔ P a x y

  record Fusion (Q : X → Y → Set) : Set₁ where
    field
      _∙_ : Y → Y → Y
      fusion₁ : ∀ {x y x′} → Q x′ y →
        F x ∙ y ≡ F x′
      fusion₂ : ∀ {x y x′} → Q x′ y →
        y ∙ F x ≡ F x′


