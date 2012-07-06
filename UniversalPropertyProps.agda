open import UniversalProperty
module UniversalPropertyProps
  {A X Y : Set} (a : A) (P : A → X → Y → Set)
  (u : Universal a P)
where
open import Prelude
open import Equiv
open Universal u
open _⇔_

self : (x : X) → P a x (F x)
self x = to (charn x (F x)) equal

uniq : (x : X) (y z : Y) →
  P a x y × P a x z → y ≡ z
uniq x y z (p , q)
  with from (charn x y) p | from (charn x z) q
uniq x .(F x) .(F x) (p , q) | equal | equal = equal
