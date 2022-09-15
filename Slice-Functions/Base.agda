module Slice-Functions.Base where

open import Data.Unit
open import Data.Empty
open import Data.Sum renaming (map to map⊎)
open import Data.Nat hiding (_⊔_)
open import Data.Product renaming (map to map×)
open import Relation.Binary.PropositionalEquality hiding ([_])

open import Slice.Base


-- Bicategory of Slice functions

-- Objects are sets


-- Morphisms (Directional spans)
SF : (X Y : Set) → Set₁
SF X Y = X → SL Y

-- Identity morphism
SF-id : (X : Set) → SF X X
SF-id = SL-η

-- Morphism composition
SF-∘ : {X Y Z : Set} → SF X Y → SF Y Z → SF X Z
SF-∘ f g x = SL-* g (f x)

-- Order on morphisms (2-morphisms if truncated)
SF≤ : {X Y : Set} → SF X Y → SF X Y → Set
SF≤ {X} {Y} f g = (x : X) → SL→ Y (f x) (g x) 

-- Equivalence of morphisms (Quotient to create category of relations)
SF≡ : {X Y : Set} → SF X Y → SF X Y → Set
SF≡ f g  = SF≤ f g × SF≤ g f



-- Morphism order properties

-- Order reflexivity
SF≤-Refl : {X Y : Set} → (f : SF X Y) → SF≤ f f
SF≤-Refl f x i = i , refl

-- Order transitivity
SF≤-Tran : {X Y : Set} → (f g h : SF X Y) → SF≤ f g → SF≤ g h → SF≤ f h
SF≤-Tran f g h f≤g g≤h x i = proj₁ (g≤h x (proj₁ (f≤g x i))) ,
  trans (proj₂ (f≤g x i)) (proj₂ (g≤h x (proj₁ (f≤g x i))))

-- Equivalence reflexivity
SF≡-Refl : {X Y : Set} → (f : SF X Y) → SF≡ f f
SF≡-Refl f = SF≤-Refl f , SF≤-Refl f

-- Equivalence transitivity
SF≡-Tran : {X Y : Set} → (R S T : SF X Y) → SF≡ R S → SF≡ S T → SF≡ R T
SF≡-Tran R S T (R≤S , S≤R) (S≤T , T≤S) = SF≤-Tran R S T R≤S S≤T , SF≤-Tran T S R T≤S S≤R

-- Equivalence symmetry
SF≡-Symm : {X Y : Set} → (R S : SF X Y) → SF≡ R S → SF≡ S R
SF≡-Symm R S (R≤S , S≤R) = S≤R , R≤S



-- Categorical properties

-- Composition preserves order
SF≤-∘ : {X Y Z : Set} → (f f' : SF X Y) → (g g' : SF Y Z)
  → (SF≤ f f') → (SF≤ g g') → SF≤ (SF-∘ f g) (SF-∘ f' g') 
SF≤-∘ f f' g g' f≤f' g≤g' x (i , j) with (f≤f' x i)
... | k , eq rewrite eq = (k , (proj₁ (g≤g' (proj₂ (f' x) k) j))) ,
  (proj₂ (g≤g' (proj₂ (f' x) k) j))

-- Left unitality
SF-luni : {X Y : Set} → (f : SF X Y) → SF≡ (SF-∘ (SF-id X) f) f
proj₁ (SF-luni f) x (tt , j) = j , refl
proj₂ (SF-luni f) x j = (tt , j) , refl

-- Right unitality
SF-runi : {X Y : Set} → (f : SF X Y) → SF≡ (SF-∘ f (SF-id Y)) f
proj₁ (SF-runi f) x (i , tt) = i , refl
proj₂ (SF-runi f) x i = (i , tt) , refl

-- Associativity
SF-asso : {X Y Z W : Set} → (f : SF X Y) → (g : SF Y Z) → (h : SF Z W)
  → SF≡ (SF-∘ (SF-∘ f g) h) (SF-∘ f (SF-∘ g h))
proj₁ (SF-asso f g h) x ((i , j) , k) = (i , (j , k)) , refl
proj₂ (SF-asso f g h) x (i , (j , k)) = ((i , j) , k) , refl


-- Auxiliary
SF-∘-l≡ :  {X Y Z : Set} → (f g : SF X Y) → (h : SF Y Z) → SF≡ f g
  → SF≡ (SF-∘ f h) (SF-∘ g h)
proj₁ (SF-∘-l≡ f g h (f<g , g<f)) x (i , j) with (f<g x i)
... | k , eq rewrite eq = (k , j) , refl
proj₂ (SF-∘-l≡ f g h (f<g , g<f)) x (i , j) with (g<f x i)
... | k , eq rewrite eq = (k , j) , refl

SF-∘-r≡ :  {X Y Z : Set} → (f : SF X Y) → (g h : SF Y Z) → SF≡ g h
  → SF≡ (SF-∘ f g) (SF-∘ f h)
proj₁ (SF-∘-r≡ f g h (g<h , h<f)) x (i , j) = (i , (proj₁ (g<h (proj₂ (f x) i) j))) ,
  (proj₂ (g<h (proj₂ (f x) i) j))
proj₂ (SF-∘-r≡ f g h (g<h , h<g)) x (i , j) = (i , proj₁ (h<g (proj₂ (f x) i) j)) ,
  proj₂ (h<g (proj₂ (f x) i) j)


-- Functor of Set into Rel
SF-Fun : {X Y : Set} → (X → Y) → SF X Y
SF-Fun f x = SF-id _ (f x)


SF-Fun-id : (X : Set) → SF≡ (SF-Fun {X} {X} (λ x → x)) (SF-id X)
proj₁ (SF-Fun-id X) x tt = tt , refl
proj₂ (SF-Fun-id X) x tt = tt , refl

SF-Fun-∘ : {X Y Z : Set} → (f : X → Y) → (g : Y → Z)
  → SF≡ (SF-Fun (λ x → g (f x))) (SF-∘ (SF-Fun f) (SF-Fun g))
proj₁ (SF-Fun-∘ f g) x tt = (tt , tt) , refl
proj₂ (SF-Fun-∘ f g) x (tt , tt) = tt , refl
