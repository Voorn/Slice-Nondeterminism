module Slice-Functions.Dagger where

open import Data.Unit
open import Data.Empty
open import Data.Sum renaming (map to map⊎)
open import Data.Nat hiding (_⊔_)
open import Data.Product renaming (map to map×)
open import Relation.Binary.PropositionalEquality hiding ([_])

open import Slice.Base
open import Slice-Functions.Base
open import Extensionality




-- Reverse map: Dagger for Rel
SF-dag : {X Y : Set} → SF X Y → SF Y X
SF-dag {X} {Y} f y = (Σ X λ x → Σ (proj₁ (f x)) λ i → proj₂ (f x) i ≡ y) , proj₁


SF-rr : {X Y : Set} → (f : SF X Y) → SF≡ (SF-dag (SF-dag f)) f
proj₁ (SF-rr f) x (y , (.x , i , eq') , refl) = i , (sym eq')
proj₂ (SF-rr f) x i = ((proj₂ (f x) i) , ((x , (i , refl)) , refl)) , refl


SF-dag-id : (X : Set) → SF≡ (SF-dag (SF-id X)) (SF-id X)
proj₁ (SF-dag-id X) x (x' , i , eq) = tt , eq
proj₂ (SF-dag-id X) x i = (x , (tt , refl)) , refl


SF-dag-∘ : {X Y Z : Set} → (f : SF X Y) → (g : SF Y Z)
  → SF≡ (SF-dag (SF-∘ f g)) (SF-∘ (SF-dag g) (SF-dag f))
proj₁ (SF-dag-∘ f g) z (x , (i , j) , g<fxi>j≡z ) =
  (((proj₂ (f x) i) , j , g<fxi>j≡z ) , (x , i , refl)) , refl
proj₂ (SF-dag-∘ f g) z ((.(proj₂ (f x) i) , j , gyj≡z) , x , i , refl) =
  (x , ((i , j) , gyj≡z)) , refl


SF-dag-≡ : {X Y : Set} → (f g : SF X Y) → SF≡ f g → SF≡ (SF-dag g) (SF-dag f)
proj₁ (SF-dag-≡ f g (f<g , g<f)) y (x , i , gxi≡y) =
  (x , ((proj₁ (g<f x i)) , (trans (sym (proj₂ (g<f x i))) gxi≡y))) , refl
proj₂ (SF-dag-≡ f g (f<g , g<f)) y (x , i , fxi≡y) =
  (x , (proj₁ (f<g x i) , trans (sym (proj₂ (f<g x i))) fxi≡y)) , refl




-- Structure of powerdomain
open import Slice.Lattice

SF-join : {X Y : Set} → SF X Y → SF X Y → SF X Y
SF-join f g x = join (f x) (g x)

SF-join-sym : {X Y : Set} → (f g : SF X Y) → SF≡ (SF-join f g) (SF-join g f)
SF-join-sym f g = (λ x → proj₁ (join-symm (f x) (g x))) , λ x → proj₂ (join-symm (f x) (g x))


SF-join-l< : {X Y : Set} → (f g h : SF X Y)
  → SF≤ f g → SF≤ (SF-join f h) (SF-join g h)
SF-join-l< f g h f<g x = join-< (f<g x) (SL→id _ (h x))

SF-join-r< :  {X Y : Set} → (f g h : SF X Y)
  → SF≤ g h → SF≤ (SF-join f g) (SF-join f h)
SF-join-r< f g h g<h x = join-< (SL→id _ (f x)) (g<h x)

SF-join-≡ : {X Y : Set} → (f g h k : SF X Y) → SF≡ f g → SF≡ h k
  → SF≡ (SF-join f h) (SF-join g k)
proj₁ (SF-join-≡ f g h k (f<g , g<f) (h<k , k<h)) =
  SF≤-Tran _ _ _ (SF-join-l< f g h f<g) (SF-join-r< g h k h<k)
proj₂ (SF-join-≡ f g h k (f<g , g<f) (h<k , k<h)) =
  SF≤-Tran _ _ _ (SF-join-l< g f k g<f) (SF-join-r< f k h k<h)

