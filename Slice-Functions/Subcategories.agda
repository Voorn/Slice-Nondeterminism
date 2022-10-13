module Slice-Functions.Subcategories where

open import Data.Unit
open import Data.Empty
open import Data.Sum renaming (map to map⊎)
open import Data.Nat hiding (_⊔_)
open import Data.Product renaming (map to map×)
open import Relation.Binary.PropositionalEquality hiding ([_])


open import Slice-Functions.Base
open import Slice-Functions.Dagger


-- Subcategories
-- Total relations
SF-Total : {X Y : Set} → SF X Y → Set
SF-Total {X} f = (x : X) → proj₁ (f x)

SF-Total-Id : (X : Set) → SF-Total (SF-id X)
SF-Total-Id X x = tt

SF-Total-∘ : {X Y Z : Set} → (f : SF X Y) → (g : SF Y Z)
  → SF-Total f → SF-Total g → SF-Total (SF-∘ f g)
SF-Total-∘ f g if ig x = (if x) , (ig (proj₂ (f x) (if x)))



-- One or less valued
SF-Onele : {X Y : Set} → SF X Y → Set
SF-Onele {X} f = (x : X) → (i j : proj₁ (f x)) → proj₂ (f x) i ≡ proj₂ (f x) j

SF-Onele-Id : (X : Set) → SF-Onele (SF-id X)
SF-Onele-Id X x i j = refl

SF-Onele-∘ : {X Y Z : Set} → (f : SF X Y) → (g : SF Y Z)
  → SF-Onele f → SF-Onele g → SF-Onele (SF-∘ f g)
SF-Onele-∘ f g lf lg x (i , j) (i' , j') rewrite lf x i i' = lg (proj₂ (f x) i') j j'



-- Injective
SF-Injec : {X Y : Set} → SF X Y → Set
SF-Injec {X} f = (x y : X) → (i : proj₁ (f x)) → (j : proj₁ (f y))
  → proj₂ (f x) i ≡ proj₂ (f y) j → x ≡ y

SF-Injec-Id : (X : Set) → SF-Injec (SF-id X)
SF-Injec-Id X x y i j eq = eq

SF-Injec-∘ : {X Y Z : Set} → (f : SF X Y) → (g : SF Y Z)
  → SF-Injec f → SF-Injec g → SF-Injec (SF-∘ f g)
SF-Injec-∘ f g of og x y (i , j) (i' , j') eq =
  of x y i i' (og (proj₂ (f x) i) (proj₂ (f y) i') j j' eq)


-- Surjective
SF-Surje : {X Y : Set} → SF X Y → Set
SF-Surje {X} {Y} f = (y : Y) → Σ X λ x → Σ (proj₁ (f x)) λ i → proj₂ (f x) i ≡ y

SF-Surje-Id : (X : Set) → SF-Surje (SF-id X)
SF-Surje-Id X x = x , (tt , refl)

SF-Surje-∘ : {X Y Z : Set} → (f : SF X Y) → (g : SF Y Z)
  → SF-Surje f → SF-Surje g → SF-Surje (SF-∘ f g)
SF-Surje-∘ f g sf sg z with sg z
... | y , j , refl with sf y
... | x , i , refl = x , ((i , j) , refl)




-- Reversing swaps properties
SF-dag-Total : {X Y : Set} → (f : SF X Y) → SF-Total f → SF-Surje (SF-dag f)
SF-dag-Total f tf x = (proj₂ (f x) (tf x)) , ((x , ((tf x) , refl)) , refl)

SF-dag-Surje : {X Y : Set} → (f : SF X Y) → SF-Surje f → SF-Total (SF-dag f)
SF-dag-Surje f sf y = (proj₁ (sf y)) , ((proj₁ (proj₂ (sf y))) , (proj₂ (proj₂ (sf y))))

SF-dag-Lone : {X Y : Set} → (f : SF X Y) → SF-Onele f → SF-Injec (SF-dag f)
SF-dag-Lone f of x y (x₀ , i , eq₀) (.x₀ , j , eq₁) refl =
  trans (sym eq₀) (trans (of x₀ i j) eq₁)

SF-dag-Injec : {X Y : Set} → (f : SF X Y) → SF-Injec f → SF-Onele (SF-dag f)
SF-dag-Injec f if y (x , i , eq) (x' , j , eq') = if x x' i j (trans eq (sym eq'))

-- Inverse existence
SF-postinverse : {X Y : Set} → (f : SF X Y) → (SF-Total f) → (SF-Injec f)
  → SF≡ (SF-∘ f (SF-dag f)) (SF-id X)
proj₁ (SF-postinverse f f-tot f-injec) x (i , x' , j , eq) = tt ,
  (sym (f-injec x x' i j (sym eq)))
proj₂ (SF-postinverse f f-tot f-injec) x tt = ((f-tot x) , (x , ((f-tot x) , refl))) , refl


SF-preinverse : {X Y : Set} → (f : SF X Y) → (SF-Onele f) → (SF-Surje f)
  → SF≡ (SF-∘ (SF-dag f) f) (SF-id Y) 
proj₁ (SF-preinverse f fone fsur) y ((x , i , eq) , j) = tt , trans (sym (fone x i j)) eq
proj₂ (SF-preinverse f fone fsur) y tt with fsur y
... | x , i , refl = ((x , (i , refl)) , i) , refl


-- Set is the subcategory of Onele and Total relations
SF-Fun-Onele : {X Y : Set} → (f : X → Y) → SF-Onele (SF-Fun f)
SF-Fun-Onele f x i j = refl

SF-Fun-Total : {X Y : Set} → (f : X → Y) → SF-Total (SF-Fun f)
SF-Fun-Total f x = tt

--Note: Since Set's notion of equality is the eternal equivalence of Agda,
--SF-Fun trivially preserves equivalence


--Showing that the Functor SF-Fun is bijective on morphisms (function extensionality)
open import Extensionality

SF-Fun-inv≡ : {X Y : Set} → (f g : X → Y) → SF≡ (SF-Fun f) (SF-Fun g) → (f ≡ g)
SF-Fun-inv≡ f g (f<g , g<f) = fun-ext λ x → proj₂ (f<g x tt)

SF-Fun-inv : {X Y : Set} → (f : SF X Y) → SF-Onele f → SF-Total f
  → Σ (X → Y) λ h → SF≡ (SF-Fun h) f
proj₁ (SF-Fun-inv f fone ftot) x = proj₂ (f x) (ftot x)
proj₂ (SF-Fun-inv f fone ftot) = (λ x i → (ftot x) , refl) ,
                                  λ x i → tt , (fone x i (ftot x))

