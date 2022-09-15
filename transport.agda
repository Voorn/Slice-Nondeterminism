module transport where


open import Relation.Binary.PropositionalEquality hiding ([_])


transp : {X : Set} → (K : X → Set) → (x y : X) → (x ≡ y) → K x → K y
transp K x .x refl i = i


transp-eq : {X : Set} → (K : X → Set) → (x y : X) → (e e' : x ≡ y) → (i : K x)
  → transp K x y e i ≡ transp K x y e' i
transp-eq K x .x refl refl i = refl


transp-comp : {X : Set} → (K : X → Set) → (x y z : X) → (e : x ≡ y) → (e' : y ≡ z)
  → (i : K x) → transp K x z (trans e e') i ≡ transp K y z e' (transp K x y e i)
transp-comp K x .x .x refl refl i = refl
