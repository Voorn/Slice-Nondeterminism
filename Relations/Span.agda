module Relations.Span where

open import Data.Unit
open import Data.Empty
open import Data.Sum renaming (map to map⊎)
open import Data.Nat hiding (_⊔_)
open import Data.Product renaming (map to map×)
open import Relation.Binary.PropositionalEquality hiding ([_])

open import Slice.Base


-- Bicategory of Spans


-- Objects are sets

-- Morphisms (Spans)
Span : (X Y : Set) → Set₁
Span X Y = SL (X × Y)

-- Identity morphism
Span-id : (X : Set) → Span X X
Span-id X = X , (λ x → x , x)

-- Morphism composition
Span-∘ : {X Y Z : Set} → Span X Y → Span Y Z → Span X Z
Span-∘ (I , A) (J , B) = (Σ (I × J) λ {(i , j) → proj₂ (A i) ≡ proj₁ (B j)}) ,
  λ {((i , j) , eq) → proj₁ (A i) , proj₂ (B j)}

-- Order on morphisms (2-morphisms if truncated)
Span≤ : {X Y : Set} → (S S' : Span X Y) → Set
Span≤  {X} {Y} = SL→ (X × Y)

-- Equivalence of morphisms (Quotient to create category of relations)
Span≡ : {X Y : Set} → (Span X Y) → (Span X Y) → Set
Span≡ S S' = Span≤ S S' × Span≤ S' S



-- Morphism order properties

-- Order reflexivity
Span≤-Refl : {X Y : Set} → (f : Span X Y) → Span≤ f f
Span≤-Refl f i = i , refl

-- Order transitivity
Span≤-Tran : {X Y : Set} → (f g h : Span X Y) → Span≤ f g → Span≤ g h → Span≤ f h
Span≤-Tran f g h f≤g g≤h i = (proj₁ (g≤h (proj₁ (f≤g i)))) ,
  (trans (proj₂ (f≤g i)) (proj₂ (g≤h (proj₁ (f≤g i)))))

-- Equivalence reflexivity
Span≡-Refl : {X Y : Set} → (f : Span X Y) → Span≡ f f
Span≡-Refl f = Span≤-Refl f , Span≤-Refl f

-- Equivalence transitivity
Span≡-Tran : {X Y : Set} → (R S T : Span X Y) → Span≡ R S → Span≡ S T → Span≡ R T
Span≡-Tran R S T (R≤S , S≤R) (S≤T , T≤S) = Span≤-Tran R S T R≤S S≤T , Span≤-Tran T S R T≤S S≤R

-- Equivalence symmetry
Span≡-Symm : {X Y : Set} → (R S : Span X Y) → Span≡ R S → Span≡ S R
Span≡-Symm R S (R≤S , S≤R) = S≤R , R≤S



-- Categorical properties

-- Composition preserves order
Span≤-∘ : {X Y Z : Set} → (f f' : Span X Y) → (g g' : Span Y Z)
  → (Span≤ f f') → (Span≤ g g') → Span≤ (Span-∘ f g) (Span-∘ f' g') 
Span≤-∘ f f' g g' f≤f' g≤g' ((i , j) , eq) with (f≤f' i) , (g≤g' j)
... | ((a , e) , (b , e')) rewrite e | e' = ((a , b) , eq) , refl

-- Left unitality
Span-luni : {X Y : Set} → (f : Span X Y) → Span≡ (Span-∘ (Span-id X) f) f
proj₁ (Span-luni f) ((.(proj₁ (proj₂ f i)) , i) , refl) = i , refl
proj₂ (Span-luni (I , f)) i = ((proj₁ (f i) , i) , refl) , refl

-- Right unitality
Span-runi : {X Y : Set} → (f : Span X Y) → Span≡ (Span-∘ f (Span-id Y)) f
proj₁ (Span-runi (I , f)) ((i , .(proj₂ (f i))) , refl) = i , refl
proj₂ (Span-runi (I , f)) i = ((i , (proj₂ (f i))) , refl) , refl

-- Associativity
Span-asso : {X Y Z W : Set} → (f : Span X Y) → (g : Span Y Z) → (h : Span Z W)
  → Span≡ (Span-∘ (Span-∘ f g) h) (Span-∘ f (Span-∘ g h))
proj₁ (Span-asso f g h) ((((i , j) , e) , k) , e') = ((i , ((j , k) , e')) , e) , refl
proj₂ (Span-asso f g h) ((i , ((j , k) , e')) , e) = ((((i , j) , e) , k) , e') , refl
