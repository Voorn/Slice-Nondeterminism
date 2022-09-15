module Slice-Nondeterminism where

open import Data.Unit
open import Data.Empty
open import Data.Sum renaming (map to map⊎)
open import Data.Nat hiding (_⊔_)
open import Data.Product renaming (map to map×)
open import Relation.Binary.PropositionalEquality hiding ([_])

open import Slice
open import Slice-Functions
open import Extensionality


Rel₁ : Set₁ → Set₁ → Set₁
Rel₁ X Y = X → Y → Set


Pow = SL


Pow→ : {X Y : Set} → (X → Y) → (Pow X → Pow Y)
Pow→ f (I , a) = I , (λ i → f (a i))

id : (X : Set) → X → X
id X x = x



-- A notion of function equality

--Pow-Γ : {X Y : Set} → (X → Y → Set) → Rel₁ (Pow X) (Pow Y)
--Pow-Γ R (I , a) (J , b) = (i : I) → Σ J λ j → R (a i) (b j)

Pow-Γ≡ : (X : Set) → Rel₁ (Pow X) (Pow X)
Pow-Γ≡ = SL→
-- = Pow-Γ (_ ≡ _)

Pow-< : {X Y : Set} → Rel₁ (X → Pow Y) (X → Pow Y)
Pow-< {X} {Y} f g  = (x : X) → SL→ Y (f x) (g x)



Pow-refl : {X Y : Set} → (f : X → Pow Y) → Pow-< f f
Pow-refl f x i = i , refl

Pow-trans : {X Y : Set} → {f g h : X → Pow Y} → Pow-< f g → Pow-< g h → Pow-< f h
Pow-trans f<g g<h x i = proj₁ (g<h x (proj₁ (f<g x i))) ,
  trans (proj₂ (f<g x i)) (proj₂ (g<h x (proj₁ (f<g x i))))

-- Membership
Pow-∈ : (X : Set) → X → SL X → Set
Pow-∈ X x (I , s) = Σ I λ i → s i ≡ x

Pow-⊂ : (X : Set) → SL X → SL X → Set
Pow-⊂ X A B = (x : X) → Pow-∈ X x A → Pow-∈ X x B

Pow-SL-1 : (X : Set) → (A B : SL X) → Pow-⊂ X A B → SL→ X A B
Pow-SL-1 X (I , F) (J , G) sub i with sub (F i) (i , refl)
... | (j , eq) = j , (sym eq)


Pow-SL-2 : (X : Set) → (A B : SL X) → SL→ X A B → Pow-⊂ X A B
Pow-SL-2 X (I , F) (J , G) map .(F i) (i , refl) with map i
... | (j , eq) = j , sym eq

-- Kleisli structure

-- Objects are Sets
-- Morphisms are:
PK-Hom : (X Y : Set) → Set₁
PK-Hom X Y = X → Pow Y

PK-≡ : {X Y : Set} → Rel₁ (PK-Hom X Y) (PK-Hom X Y)
PK-≡ f g = Pow-< f g × Pow-< g f


PK-≡-refl : {X Y : Set} → (f : PK-Hom X Y) → PK-≡ f f
PK-≡-refl f = Pow-refl f , Pow-refl f

PK-≡-sym : {X Y : Set} → {f g : PK-Hom X Y} → PK-≡ f g → PK-≡ g f
PK-≡-sym (f<g , g<f) = (g<f , f<g)

PK-≡-trans : {X Y : Set} → {f g h : PK-Hom X Y} → PK-≡ f g → PK-≡ g h → PK-≡ f h
PK-≡-trans f≡g g≡h = Pow-trans (proj₁ f≡g) (proj₁ g≡h)  , Pow-trans (proj₂ g≡h) (proj₂ f≡g)


PK-Id : (X : Set) → PK-Hom X X
PK-Id X x = ⊤ , (λ _ → x)


Pow-κ : (X Y : Set) → (X → Pow Y) → (Pow X → Pow Y)
Pow-κ X Y = SL-* {X} {Y}
--f (I , a) = (Σ I λ i → proj₁ (f (a i))) ,
--  (λ {(i , j) → proj₂ (f (a i)) j})



-- Directional spans:
-- Objects are sets
-- Morphisms X to Y are functions X to SL Y
-- Order is SL→


PK-∘ : {X Y Z : Set} → PK-Hom X Y → PK-Hom Y Z → PK-Hom X Z
PK-∘ {X} {Y} {Z} f g x = Pow-κ Y Z g (f x)

abstract
  PKA-∘ = PK-∘



PK-luni : {X Y : Set} → (f : PK-Hom X Y) → PK-≡ (PK-∘ (PK-Id X) f) f
proj₁ (PK-luni f) x (tt , j) = j , refl
proj₂ (PK-luni f) x j = (tt , j) , refl

PK-runi : {X Y : Set} → (f : PK-Hom X Y) → PK-≡ (PK-∘ f (PK-Id Y)) f
proj₁ (PK-runi f) x (i , tt) = i , refl
proj₂ (PK-runi f) x i = (i , tt) , refl

PK-asso : {X Y Z W : Set} → (f : PK-Hom X Y) → (g : PK-Hom Y Z) → (h : PK-Hom Z W)
  → PK-≡ (PK-∘ (PK-∘ f g) h) (PK-∘ f (PK-∘ g h))
proj₁ (PK-asso f g h) x ((i , j) , k) = (i , (j , k)) , refl
proj₂ (PK-asso f g h) x (i , (j , k)) = ((i , j) , k) , refl



PK-∘-l≡ :  {X Y Z : Set} → (f g : PK-Hom X Y) → (h : PK-Hom Y Z) → PK-≡ f g
  → PK-≡ (PK-∘ f h) (PK-∘ g h)
proj₁ (PK-∘-l≡ f g h (f<g , g<f)) x (i , j) with (f<g x i)
... | k , eq rewrite eq = (k , j) , refl
proj₂ (PK-∘-l≡ f g h (f<g , g<f)) x (i , j) with (g<f x i)
... | k , eq rewrite eq = (k , j) , refl

PK-∘-r≡ :  {X Y Z : Set} → (f : PK-Hom X Y) → (g h : PK-Hom Y Z) → PK-≡ g h
  → PK-≡ (PK-∘ f g) (PK-∘ f h)
proj₁ (PK-∘-r≡ f g h (g<h , h<f)) x (i , j) = (i , (proj₁ (g<h (proj₂ (f x) i) j))) ,
  (proj₂ (g<h (proj₂ (f x) i) j))
proj₂ (PK-∘-r≡ f g h (g<h , h<g)) x (i , j) = (i , proj₁ (h<g (proj₂ (f x) i) j)) ,
  proj₂ (h<g (proj₂ (f x) i) j)

PK-∘-≡ : {X Y Z : Set} → (f f' : PK-Hom X Y) → (g g' : PK-Hom Y Z)
  → PK-≡ f f' → PK-≡ g g' → PK-≡ (PK-∘ f g) (PK-∘ f' g')
PK-∘-≡ f f' g g' f≡f' g≡g' = PK-≡-trans (PK-∘-l≡ f f' g f≡f') (PK-∘-r≡ f' g g' g≡g')





-- Functor of Set into Rel
PK-Fun : {X Y : Set} → (X → Y) → PK-Hom X Y
PK-Fun f x = PK-Id _ (f x)


PK-Fun-id : (X : Set) → PK-≡ (PK-Fun {X} {X} (id X)) (PK-Id X)
proj₁ (PK-Fun-id X) x tt = tt , refl
proj₂ (PK-Fun-id X) x tt = tt , refl

PK-Fun-∘ : {X Y Z : Set} → (f : X → Y) → (g : Y → Z)
  → PK-≡ (PK-Fun (λ x → g (f x))) (PK-∘ (PK-Fun f) (PK-Fun g))
proj₁ (PK-Fun-∘ f g) x tt = (tt , tt) , refl
proj₂ (PK-Fun-∘ f g) x (tt , tt) = tt , refl


-- Reverse map: Dagger for Rel
PK-rev : {X Y : Set} → PK-Hom X Y → PK-Hom Y X
PK-rev {X} {Y} f y = (Σ X λ x → Σ (proj₁ (f x)) λ i → proj₂ (f x) i ≡ y) , proj₁


PK-rr : {X Y : Set} → (f : PK-Hom X Y) → PK-≡ (PK-rev (PK-rev f)) f
proj₁ (PK-rr f) x (y , (.x , i , eq') , refl) = i , (sym eq')
proj₂ (PK-rr f) x i = ((proj₂ (f x) i) , ((x , (i , refl)) , refl)) , refl


PK-rev-id : (X : Set) → PK-≡ (PK-rev (PK-Id X)) (PK-Id X)
proj₁ (PK-rev-id X) x (x' , i , eq) = tt , eq
proj₂ (PK-rev-id X) x i = (x , (tt , refl)) , refl


PK-rev-∘ : {X Y Z : Set} → (f : PK-Hom X Y) → (g : PK-Hom Y Z)
  → PK-≡ (PK-rev (PK-∘ f g)) (PK-∘ (PK-rev g) (PK-rev f))
proj₁ (PK-rev-∘ f g) z (x , (i , j) , g<fxi>j≡z ) =
  (((proj₂ (f x) i) , j , g<fxi>j≡z ) , (x , i , refl)) , refl
proj₂ (PK-rev-∘ f g) z ((.(proj₂ (f x) i) , j , gyj≡z) , x , i , refl) =
  (x , ((i , j) , gyj≡z)) , refl


PK-rev-≡ : {X Y : Set} → (f g : PK-Hom X Y) → PK-≡ f g → PK-≡ (PK-rev g) (PK-rev f)
proj₁ (PK-rev-≡ f g (f<g , g<f)) y (x , i , gxi≡y) =
  (x , ((proj₁ (g<f x i)) , (trans (sym (proj₂ (g<f x i))) gxi≡y))) , refl
proj₂ (PK-rev-≡ f g (f<g , g<f)) y (x , i , fxi≡y) =
  (x , (proj₁ (f<g x i) , trans (sym (proj₂ (f<g x i))) fxi≡y)) , refl




-- Structure of powerdomain
open import Slice-Lattice

PK-join : {X Y : Set} → PK-Hom X Y → PK-Hom X Y → PK-Hom X Y
PK-join f g x = join (f x) (g x)

PK-join-sym : {X Y : Set} → (f g : PK-Hom X Y) → PK-≡ (PK-join f g) (PK-join g f)
PK-join-sym f g = (λ x → proj₁ (join-symm (f x) (g x))) , λ x → proj₂ (join-symm (f x) (g x))


PK-join-l< : {X Y : Set} → (f g h : PK-Hom X Y)
  → Pow-< f g → Pow-< (PK-join f h) (PK-join g h)
PK-join-l< f g h f<g x = join-< (f<g x) (SL→id _ (h x))

PK-join-r< :  {X Y : Set} → (f g h : PK-Hom X Y)
  → Pow-< g h → Pow-< (PK-join f g) (PK-join f h)
PK-join-r< f g h g<h x = join-< (SL→id _ (f x)) (g<h x)

PK-join-≡ : {X Y : Set} → (f g h k : PK-Hom X Y) → PK-≡ f g → PK-≡ h k
  → PK-≡ (PK-join f h) (PK-join g k)
proj₁ (PK-join-≡ f g h k (f<g , g<f) (h<k , k<h)) =
  Pow-trans (PK-join-l< f g h f<g) (PK-join-r< g h k h<k)
proj₂ (PK-join-≡ f g h k (f<g , g<f) (h<k , k<h)) =
  Pow-trans (PK-join-l< g f k g<f) (PK-join-r< f k h k<h)

