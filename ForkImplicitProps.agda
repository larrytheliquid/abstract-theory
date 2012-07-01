open import ForkImplicit
module ForkImplicitProps (F : Fork) where
open Fork F

π-eliminates-fork : {A B C : Set} (f : A → B) (g : A → C) (a : A) →
      (π₁ ∘ (fork f g)) a ≡ f a × (π₂ ∘ fork f g) a ≡ g a
π-eliminates-fork f g a =
  proof
    (π₁ ∘ (fork f g)) a ≡ f a × (π₂ ∘ fork f g) a ≡ g a
  ⇔⟨ charn f g (fork f g) a ⟩
    (fork f g) a ≡ (fork f g) a
  ∎
    
