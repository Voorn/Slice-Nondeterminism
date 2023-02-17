module Relations.Ext-Rel where

open import Data.Unit
open import Data.Empty
open import Data.Sum renaming (map to map⊎)
open import Data.Nat hiding (_⊔_)
open import Data.Product renaming (map to map×)
open import Relation.Binary.PropositionalEquality hiding ([_])

-- Extensional bicategory of relations

-- Objects are sets

-- Morphisms (Relations)
ER : (X Y : Set) → Set₁
ER X Y = X → Y → Set

-- Identity morphism
ER-id : (X : Set) → ER X X
ER-id X x y = x ≡ y

-- Morphism composition
ER-∘ : {X Y Z : Set} → ER X Y → ER Y Z → ER X Z
ER-∘ R S x z = Σ _ λ y → R x y × S y z

-- Order on morphism (2-morphisms truncated informally)
ER≤ : {X Y : Set} → ER X Y → ER X Y → Set
ER≤ R S = (x : _) → (y : _) → R x y → S x y

-- Equivalence of morphisms (Quotient to create category of relations)
ER≡ : {X Y : Set} → ER X Y → ER X Y → Set
ER≡ R S = ER≤ R S × ER≤ S R



-- Morphism order properties

-- Order reflexivity
ER≤-Refl : {X Y : Set} → (R : ER X Y) → ER≤ R R
ER≤-Refl R x y xRy = xRy

-- Order transitivity
ER≤-Tran : {X Y : Set} → (R S T : ER X Y) → ER≤ R S → ER≤ S T → ER≤ R T
ER≤-Tran R S T R≤S S≤T x y xRy = S≤T x y (R≤S x y xRy)

-- Equivalence reflexivity
ER≡-Refl : {X Y : Set} → (R : ER X Y) → ER≡ R R
ER≡-Refl R = ER≤-Refl R , ER≤-Refl R

-- Equivalence transitivity
ER≡-Tran : {X Y : Set} → (R S T : ER X Y) → ER≡ R S → ER≡ S T → ER≡ R T
ER≡-Tran R S T (R≤S , S≤R) (S≤T , T≤S) = (ER≤-Tran R S T R≤S S≤T) , (ER≤-Tran T S R T≤S S≤R)

-- Equivalence symmetry
ER≡-Symm : {X Y : Set} → (R S : ER X Y) → ER≡ R S → ER≡ S R
ER≡-Symm R S (R≤S , S≤R) = S≤R , R≤S



-- Categorical properties

-- Composition preserves order
ER≤-∘ : {X Y Z : Set} → (R R' : ER X Y) → (S S' : ER Y Z)
  → (ER≤ R R') → (ER≤ S S') → ER≤ (ER-∘ R S) (ER-∘ R' S')
ER≤-∘ R R' S S' R<R' S<S' x z (y , xRy , ySz) = y , R<R' x y xRy , S<S' y z ySz

ER-∘≡ : {X Y Z : Set} → {S S' : ER Y Z} → {R R' : ER X Y}
  → (ER≡ S S') → (ER≡ R R') → ER≡ (ER-∘ R S) (ER-∘ R' S')
ER-∘≡ (S≤S' , S'≤S) (R≤R' , R'≤R) = (ER≤-∘ _ _ _ _ R≤R' S≤S') , ER≤-∘ _ _ _ _ R'≤R S'≤S

-- Left unitality
ER-luni : {X Y : Set} → (R : ER X Y) → ER≡ (ER-∘ (ER-id _) R) R
ER-luni R = (λ {x y (.x , refl , xRy) → xRy}) , λ x y xRy → x , refl , xRy

-- Right unitality
ER-runi : {X Y : Set} → (R : ER X Y) → ER≡ (ER-∘ R (ER-id _)) R
ER-runi R = (λ {x y (.y , xRy , refl) → xRy}) , λ x y xRy → y , xRy , refl

-- Associativity
ER-asso : {X Y Z W : Set} → (R : ER X Y) → (S : ER Y Z) → (T : ER Z W)
  → ER≡ (ER-∘ (ER-∘ R S) T) (ER-∘ R (ER-∘ S T))
ER-asso R S T = (λ {x w (z , (y , xRy , ySz) , zTw) → y , xRy , z , ySz , zTw}) ,
                λ {x w (y , xRy , z , ySz , zTw) → z , (y , xRy , ySz) , zTw}



