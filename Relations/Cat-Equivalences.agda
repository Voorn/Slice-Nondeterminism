module Relations.Cat-Equivalences where

open import Data.Unit
open import Data.Empty
open import Data.Sum renaming (map to map⊎)
open import Data.Nat hiding (_⊔_)
open import Data.Product renaming (map to map×)
open import Relation.Binary.PropositionalEquality hiding ([_])

open import Slice.Base
open import Slice-Functions.Base
open import Relations.Span
open import Relations.Ext-Rel


-- All functors are idenities on object (sets)


-- Bicategories of spans and directional spans are equivalent


-- Functor from slice functions to spans
SF→Span : {X Y : Set} → SF X Y → Span X Y
SF→Span {X} {Y} f = (Σ X λ x → proj₁ (f x)) , λ {(x , i) → x , (proj₂ (f x) i)}

-- This is a functor
SF→Span-id : (X : Set) → Span≡ (SF→Span (SF-id X)) (Span-id X)
proj₁ (SF→Span-id X) (x , tt) = x , refl
proj₂ (SF→Span-id X) x = (x , tt) , refl

SF→Span-∘ : {X Y Z : Set} → (f : SF X Y) → (g : SF Y Z)
  → Span≡ (SF→Span (SF-∘ f g)) (Span-∘ (SF→Span f) (SF→Span g))
proj₁ (SF→Span-∘ f g) (x , i , j) = (((x , i) , proj₂ (f x) i , j) , refl) , refl
proj₂ (SF→Span-∘ f g) (((x , i) , .(proj₂ (f x) i) , j) , refl) = (x , i , j) , refl

SF→Span-≤ : {X Y : Set} → {f g : SF X Y} → SF≤ f g → Span≤ (SF→Span f) (SF→Span g)
SF→Span-≤ f<g (x , i) = (x , (proj₁ (f<g x i))) , (cong (λ u → (x , u)) (proj₂ (f<g x i)))


-- Functor from spans to slice functions
Span→SF : {X Y : Set} → Span X Y → SF X Y
Span→SF (I , a) x = (Σ I λ i → proj₁ (a i) ≡ x) , λ i → proj₂ (a (proj₁ i))

-- This is also a functor
Span→SF-id : (X : Set) → SF≡ (Span→SF (Span-id X)) (SF-id X)
proj₁ (Span→SF-id X) x (.x , refl) = tt , refl
proj₂ (Span→SF-id X) x tt = (x , refl) , refl

Span→SF-∘ : {X Y Z : Set} → (f : Span X Y) → (g : Span Y Z)
  → SF≡ (Span→SF (Span-∘ f g)) (SF-∘ (Span→SF f) (Span→SF g))
proj₁ (Span→SF-∘ f g) .(proj₁ (proj₂ f i)) (((i , j) , eq) , refl) =
  ((i , refl) , (j , (sym eq))) , refl
proj₂ (Span→SF-∘ f g) .(proj₁ (proj₂ f i)) ((i , refl) , j , eq) =
  (((i , j) , sym eq) , refl) , refl

Span→SF-≤ : {X Y : Set} → {f g : Span X Y} → Span≤ f g → SF≤ (Span→SF f) (Span→SF g)
Span→SF-≤ {X} {Y} {f} f<g .(proj₁ (proj₂ f i)) (i , refl) = ((proj₁ (f<g i)) ,
  (sym (cong proj₁ (proj₂ (f<g i))))) , (cong proj₂ (proj₂ (f<g i)))


-- Isomorphism 
Span→SF→Span : {X Y : Set} → (f : Span X Y) → Span≡ (SF→Span (Span→SF f)) f
proj₁ (Span→SF→Span f) (.(proj₁ (proj₂ f i)) , i , refl) = i , refl
proj₂ (Span→SF→Span f) i = ((proj₁ (proj₂ f i)) , (i , refl)) , refl


SF→Span→SF : {X Y : Set} → (f : SF X Y) → SF≡ (Span→SF (SF→Span f)) f
proj₁ (SF→Span→SF f) x ((.x , i) , refl) = i , refl
proj₂ (SF→Span→SF f) x i = ((x , i) , refl) , refl




-- Bicategories of extensional relations and directional spans are equivalent


-- Functor from slice functions to extensional relations
SF→ER : {X Y : Set} → SF X Y → ER X Y
SF→ER f x y = Σ (proj₁ (f x)) λ i → proj₂ (f x) i ≡ y


-- Yep, a functor
SF→ER-id : (X : Set) → ER≡ (SF→ER (SF-id X)) (ER-id X)
SF→ER-id X = (λ x x' a → proj₂ a) , λ x y eq → tt , eq


SF→ER-∘ : {X Y Z : Set} → (f : SF X Y) → (g : SF Y Z)
  → ER≡ (SF→ER (SF-∘ f g)) (ER-∘ (SF→ER f) (SF→ER g))
SF→ER-∘ f g = (λ {x z ((i , j) , eq) → (proj₂ (f x) i) , (i , refl) , j , eq}) ,
  λ { x z (.(proj₂ (f x) i) , (i , refl) , j , eq) → (i , j) , eq}


SF→ER-≤ : {X Y : Set} → {f g : SF X Y} → SF≤ f g → ER≤ (SF→ER f) (SF→ER g)
SF→ER-≤ {X} {Y} {f} f≤g x .(proj₂ (f x) i) (i , refl) = (proj₁ (f≤g x i)) , sym (proj₂ (f≤g x i))


-- Functor from extensional relations to slice functions
ER→SF : {X Y : Set} → ER X Y → SF X Y
ER→SF R x = (Σ _ λ y → R x y) , proj₁


-- It's a functor.
ER→SF-id : (X : Set) → SF≡ (ER→SF (ER-id X)) (SF-id X)
ER→SF-id X = (λ {x (.x , refl) → tt , refl}) , λ x i → (x , refl) , refl


ER→SF-∘ : {X Y Z : Set} → (R : ER X Y) → (S : ER Y Z)
  → SF≡ (ER→SF (ER-∘ R S)) (SF-∘ (ER→SF R) (ER→SF S))
ER→SF-∘ R S = (λ {x (z , y , xRy , ySz)  → ((y , xRy) , z , ySz) , refl}) ,
  λ {x ((y , xRy) , z , ySz) → (z , y , xRy , ySz) , refl}


ER→SF-≤ : {X Y : Set} → {R S : ER X Y} → ER≤ R S → SF≤ (ER→SF R) (ER→SF S)
ER→SF-≤ R≤S x (y , xRy) = (y , R≤S x y xRy) , refl


-- Isomorphism
ER→SF→ER : {X Y : Set} → (R : ER X Y) → ER≡ (SF→ER (ER→SF R)) R
ER→SF→ER R = (λ {x y ((.y , xRy) , refl) → xRy}) , λ {x y xRy → (y , xRy) , refl}


SF→ER→SF : {X Y : Set} → (f : SF X Y) → SF≡ (ER→SF (SF→ER f)) f
SF→ER→SF f = (λ { x (.(proj₂ (f x) i) , i , refl) → i , refl}) ,
  λ x i → (proj₂ (f x) i , i , refl) , refl
