module Trace-Monad where

open import Data.Unit
open import Data.Empty
open import Data.Sum renaming (map to map⊎)
open import Data.Nat hiding (_⊔_)
open import Data.Product renaming (map to map×)
open import Relation.Binary.PropositionalEquality hiding ([_])


open import Index-Nondeterminism
open import Monoidal
open import Free-Monad

SigT : Set → Sig
SigT A = A , (λ x → ⊤)



data Trace (A : Set) (X : Set) : Set where
  ret : X → Trace A X
  act : A → Trace A X → Trace A X



Trace-σ : (A X Y : Set) → Trace A X × Y → Trace A (X × Y)
Trace-σ A X Y (ret x , y) = ret (x , y)
Trace-σ A X Y (act a t , y) = act a (Trace-σ A X Y (t , y))

Trace-ε : {A X : Set} → Trace A X → X
Trace-ε (ret x) = x
Trace-ε (act a t) = Trace-ε t


PK-T : (A : Set) → {X Y : Set} → PK-Hom X Y → PK-Hom (Trace A X) (Trace A Y)
proj₁ (PK-T A f t) = proj₁ (f (Trace-ε t))
proj₂ (PK-T A f (ret x)) i = ret (proj₂ (f x) i)
proj₂ (PK-T A f (act a t)) i = act a (proj₂ (PK-T A f t) i)


Pow-act : {A : Set} → (a : A) → (X : Set) → Pow (Trace A X) → Pow (Trace A X)
Pow-act a X = Pow→ (act a)

Pow-act-< : {A : Set} → (a : A) → (X : Set) → (u v : Pow (Trace A X))
  → Pow-Γ≡ (Trace A X) u v → Pow-Γ≡ (Trace A X) (Pow-act a X u) (Pow-act a X v)
Pow-act-< a X u v u<v i = (proj₁ (u<v i)) , (cong (act a) (proj₂ (u<v i)))

PK-T-σ : (A X Y : Set) → PK-Hom (Trace A X × Y) (Trace A (X × Y))
PK-T-σ A X Y = PK-Fun (Trace-σ A X Y)


PK-T-σ-nat : (A : Set) → {X X' Y Y' : Set} → (f : PK-Hom X X') → (g : PK-Hom Y Y')
  → PK-≡ (PK-∘ ((PK-T A f) ⊗ g) (PK-T-σ A X' Y')) (PK-∘ (PK-T-σ A X Y) (PK-T A (f ⊗ g)))
proj₁ (PK-T-σ-nat A f g) (ret x , y) ((i , j) , tt) = (tt , (i , j)) , refl
proj₁ (PK-T-σ-nat A f g) (act a t , y) ((i , j) , tt)
  with proj₁ (PK-T-σ-nat A f g) (t , y) ((i , j) , tt)
... | u , eq = u , (cong (act a) eq)
proj₂ (PK-T-σ-nat A f g) (ret x , y) (tt , i , j) = ((i , j) , tt) , refl
proj₂ (PK-T-σ-nat A f g) (act a t , y) (tt , i , j)
  with  proj₂ (PK-T-σ-nat A f g) (t , y) (tt , i , j)
... | u , eq = u , cong (act a) eq




PK-T-η : (A : Set) → (X : Set) → PK-Hom X (Trace A X)
PK-T-η A X x = PK-Id (Trace A X) (ret x)

PK-T-η-nat : (A : Set) → {X Y : Set} → (f : PK-Hom X Y)
  → PK-≡ (PK-∘ f (PK-T-η A Y)) (PK-∘ (PK-T-η A X) (PK-T A f))
proj₁ (PK-T-η-nat A f) x (i , tt) = (tt , i) , refl
proj₂ (PK-T-η-nat A f) x (tt , i) = (i , tt) , refl



PK-T-μ : (A : Set) → (X : Set) → PK-Hom (Trace A (Trace A X)) (Trace A X)
PK-T-μ A X (ret t) = PK-Id (Trace A X) t
PK-T-μ A X (act a d) = Pow-act a X (PK-T-μ A X d)

PK-T-μ-nat : (A : Set) → {X Y : Set} → (f : PK-Hom X Y)
  → PK-≡ (PK-∘ (PK-T A (PK-T A f)) (PK-T-μ A Y)) (PK-∘ (PK-T-μ A X) (PK-T A f))
proj₁ (PK-T-μ-nat A f) (ret t) (i , tt) = (tt , i) , refl
proj₁ (PK-T-μ-nat A f) (act a t) i
  with proj₁ (PK-T-μ-nat A f) t i
... | u , eq = u , (cong (act a) eq)
proj₂ (PK-T-μ-nat A f) (ret x) (tt , j) = (j , tt) , refl
proj₂ (PK-T-μ-nat A f) (act a t) i
  with proj₂ (PK-T-μ-nat A f) t i
... | u , eq = u , (cong (act a) eq)


PK-T-ε : (A : Set) → (X : Set) → PK-Hom (Trace A X) X
PK-T-ε A X (ret x) = PK-Id X x
PK-T-ε A X (act x t) = ⊥ , (λ ())

PK-T-η<>ε : (A X : Set) → PK-≡ (PK-T-ε A X) (PK-rev (PK-T-η A X))
proj₁ (PK-T-η<>ε A X) (ret x) tt = (x , (tt , refl)) , refl
proj₂ (PK-T-η<>ε A X) (ret x) (.x , tt , refl) = tt , refl


PK-T-δ : (A : Set) → (X : Set) → PK-Hom (Trace A X) (Trace A (Trace A X))
PK-T-δ A X (ret x) = PK-Id (Trace A (Trace A X)) (ret (ret x))
PK-T-δ A X (act a t) = join (PK-Id (Trace A (Trace A X)) (ret (act a t)))
                            (Pow-act a (Trace A X) (PK-T-δ A X t))


PK-T-μ<>δ : (A X : Set) → PK-≡ (PK-T-δ A X) (PK-rev (PK-T-μ A X))
proj₁ (PK-T-μ<>δ A X) (ret x) tt = (ret (ret x) , tt , refl) , refl
proj₁ (PK-T-μ<>δ A X) (act a t) (inj₁ i) = ((ret (act a t)) , (tt , refl)) , refl
proj₁ (PK-T-μ<>δ A X) (act a t) (inj₂ i) with (proj₁ (PK-T-μ<>δ A X) t i)
... | (d , p , v) , eq = (act a d , (p , cong (act a) v)) , cong (act a) eq
proj₂ (PK-T-μ<>δ A X) (ret x) (ret .(ret x) , tt , refl) = tt , refl
proj₂ (PK-T-μ<>δ A X) (act a t) (ret .(act a t) , tt , refl) = (inj₁ tt) , refl
proj₂ (PK-T-μ<>δ A X) (act a .(proj₂ (PK-T-μ A X d) i)) (act .a d , i , refl)
  with proj₂ (PK-T-μ<>δ A X) (proj₂ (PK-T-μ A X d) i) (d , i , refl)
... | j , eq = (inj₂ j) , (cong (act a) eq)
