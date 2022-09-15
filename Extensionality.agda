module Extensionality where

open import Relation.Binary.PropositionalEquality hiding ([_])



postulate fun-ext : {X Y : Set} → {f g : X → Y} → ((x : X) → f x ≡ g x) → (f ≡ g)

postulate dep-ext : {X : Set} → {F : X → Set} → {f g : (x : X) → F x} → ((x : X) → f x ≡ g x) → f ≡ g
