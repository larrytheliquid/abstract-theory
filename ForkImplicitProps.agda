open import ForkImplicit
module ForkImplicitProps (F : Fork) where
open Fork F

π-eliminates-fork : {A B C : Set} (f : A → B) (g : A → C) (a : A) →
      (π₁ ∘ (fork f g)) a ≡ f a × (π₂ ∘ fork f g) a ≡ g a
π-eliminates-fork f g a =
  proof[ equal ]
    (π₁ ∘ (fork f g)) a ≡ f a × (π₂ ∘ fork f g) a ≡ g a
  ⇔⟨ sym $ charn f g (fork f g) a ⟩
    (fork f g) a ≡ (fork f g) a
  ∎
    
pair-former-is-a-fork : {A B C : Set} (h : A → B × C) (a : A) →
  h a ≡ (fork (π₁ ∘ h) (π₂ ∘ h)) a
pair-former-is-a-fork h a =
  proof[ equal , equal ]
    h a ≡ (fork (π₁ ∘ h) (π₂ ∘ h)) a
  ⇔⟨ charn (π₁ ∘ h) (π₂ ∘ h) h a ⟩
    (π₁ ∘ h) a ≡ (π₁ ∘ h) a × (π₂ ∘ h) a ≡ (π₂ ∘ h) a
  ∎

id-is-a-fork : {A B : Set} (ab : A × B) →
  id ab ≡ (fork π₁ π₂) ab
id-is-a-fork ab =
  proof[ equal , equal ]
    id ab ≡ (fork π₁ π₂) ab
  ⇔⟨ charn π₁ π₂ id ab ⟩
    (π₁ ∘ id) ab ≡ π₁ ab × (π₂ ∘ id) ab ≡ π₂ ab
  ∎
