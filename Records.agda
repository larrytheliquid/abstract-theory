module Records where
open import Data.Bool
open import Data.Nat

record Foo (A : Set) : Set where
  constructor [_]
  field foo : A

three : Foo ℕ
three = [ 3 ]

three′ : ℕ
three′ = Foo.foo three

ff : Foo Bool
ff = [ false ]

record Bar {A : Set} (f : A → A) : Set where
  constructor [_]

  access : A → A
  access = f
