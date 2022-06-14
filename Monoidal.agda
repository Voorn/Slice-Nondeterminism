module Monoidal where

open import Data.Unit
open import Data.Empty
open import Data.Sum renaming (map to map⊎)
open import Data.Nat hiding (_⊔_)
open import Data.Product renaming (map to map×)
open import Relation.Binary.PropositionalEquality hiding ([_])


open import Index-Nondeterminism


-- The Monoidal closed structure of the category


_⊗_ : {X Y X' Y' : Set} → PK-Hom X Y → PK-Hom X' Y' → PK-Hom (X × X') (Y × Y')
(f ⊗ g) (x , x') = ((proj₁ (f x)) × (proj₁ (g x'))) ,
                   (λ (i , j) → (proj₂ (f x) i) , (proj₂ (g x') j))

⊗-< : {X Y X' Y' : Set} → {f f' : PK-Hom X Y} → {g g' : PK-Hom X' Y'}
  → Pow-< f f' → Pow-< g g' → Pow-< (f ⊗ g) (f' ⊗ g')
⊗-< f<f' g<g' (x , x') (i , j) = ((proj₁ (f<f' x i)) , (proj₁ (g<g' x' j))) ,
  (cong₂ (λ l r → l , r) (proj₂ (f<f' x i)) (proj₂ (g<g' x' j)))

⊗-≡ : {X Y X' Y' : Set} → {f f' : PK-Hom X Y} → {g g' : PK-Hom X' Y'}
  → PK-≡ f f' → PK-≡ g g' → PK-≡ (f ⊗ g) (f' ⊗ g')
⊗-≡ (f<f' , f'<f) (g<g' , g'<g) = (⊗-< f<f' g<g') , (⊗-< f'<f g'<g)



⊗-id : (X Y : Set) → PK-≡ ((PK-Id X) ⊗ (PK-Id Y)) (PK-Id (X × Y)) 
proj₁ (⊗-id X Y) (x , y) (tt , tt) = tt , refl
proj₂ (⊗-id X Y) (x , y) tt = (tt , tt) , refl


⊗-∘ : {X Y Z X' Y' Z' : Set}
  → (f : PK-Hom X Y) → (g : PK-Hom Y Z) → (f' : PK-Hom X' Y') → (g' : PK-Hom Y' Z')
  → PK-≡ (PK-∘ f g ⊗ PK-∘ f' g') (PK-∘ (f ⊗ f') (g ⊗ g'))
proj₁ (⊗-∘ f g f' g') (x , x') ((i , j) , (i' , j')) = ((i , i') , (j , j')) , refl
proj₂ (⊗-∘ f g f' g') (x , x') ((i , i') , (j , j')) = ((i , j) , (i' , j')) , refl



⊗-γ : (X Y : Set) → PK-Hom (X × Y) (Y × X)
⊗-γ X Y (x , y) = PK-Id _ (y , x)


⊗-γγ : (X Y : Set) → PK-≡ (PK-∘ (⊗-γ X Y) (⊗-γ Y X)) (PK-Id (X × Y))
proj₁ (⊗-γγ X Y) (x , y) (tt , tt) = tt , refl
proj₂ (⊗-γγ X Y) (x , y) tt = (tt , tt) , refl

⊗-γ-rev : (X Y : Set) → PK-≡ (PK-rev (⊗-γ X Y)) (⊗-γ Y X)
proj₁ (⊗-γ-rev X Y) (y , x) ((.x , .y) , tt , refl) = tt , refl
proj₂ (⊗-γ-rev X Y) (y , x) tt = ((x , y) , (tt , refl)) , refl

⊗-γ-nat : {X Y X' Y' : Set} → (f : PK-Hom X X') → (g : PK-Hom Y Y')
  → PK-≡ (PK-∘ (⊗-γ X Y) (g ⊗ f)) (PK-∘ (f ⊗ g) (⊗-γ X' Y'))
proj₁ (⊗-γ-nat f g) (x , y) (tt , (j , i)) = ((i , j) , tt) , refl
proj₂ (⊗-γ-nat f g) (x , y) ((i , j) , tt) = (tt , (j , i)) , refl



⊗-α : (X Y Z : Set) → PK-Hom ((X × Y) × Z) (X × (Y × Z))
⊗-α X Y Z ((x , y) , z) = PK-Id _ (x , (y , z))

⊗-α' : (X Y Z : Set) → PK-Hom (X × (Y × Z)) ((X × Y) × Z)
⊗-α' X Y Z (x , (y , z)) = PK-Id _ ((x , y) , z)

⊗-αα' : (X Y Z : Set) → PK-≡ (PK-∘ (⊗-α X Y Z) (⊗-α' X Y Z)) (PK-Id _)
⊗-αα' X Y Z = (λ x i → tt , refl) , (λ x i → (tt , tt) , refl)

⊗-α'α : (X Y Z : Set) → PK-≡ (PK-∘ (⊗-α' X Y Z) (⊗-α X Y Z)) (PK-Id _)
⊗-α'α X Y Z = (λ x i → tt , refl) , (λ x i → (tt , tt) , refl)

⊗-α-rev : (X Y Z : Set) → PK-≡ (PK-rev (⊗-α X Y Z)) (⊗-α' X Y Z)
proj₁ (⊗-α-rev X Y Z) (x , y , z) (((.x , .y) , .z) , tt , refl) = tt , refl
proj₂ (⊗-α-rev X Y Z) (x , y , z) tt = (((x , y) , z) , (tt , refl)) , refl

⊗-α-nat : {X Y Z X' Y' Z' : Set} → (f : PK-Hom X X') → (g : PK-Hom Y Y') → (h : PK-Hom Z Z')
  → PK-≡ (PK-∘ (⊗-α X Y Z) (f ⊗ (g ⊗ h))) (PK-∘ ((f ⊗ g) ⊗ h) (⊗-α X' Y' Z'))
proj₁ (⊗-α-nat f g h) ((x , y) , z) (tt , i , j , k) = (((i , j) , k) , tt) , refl
proj₂ (⊗-α-nat f g h) ((x , y) , z) (((i , j) , k) , tt) = (tt , i , j , k) , refl



-- Monoidal unit
⊗-I : PK-Hom ⊤ ⊤
⊗-I tt = ⊤ , (λ i → tt)


⊗-proj₁ : (X Y : Set) → PK-Hom (X × Y) X
⊗-proj₁ X Y = PK-Fun proj₁


-- Monoidal Closed
_⇒_ : {X X' Y Y' : Set} → (PK-Hom X' X) → (PK-Hom Y Y') → (PK-Hom (X × Y) (X' × Y'))
f ⇒ g = PK-rev f ⊗ g


⊗-closed-r : (X Y Z : Set) → PK-Hom (X × Y) Z → PK-Hom X (Y × Z)
⊗-closed-r X Y Z f x = (Σ Y λ y → proj₁ (f (x , y))) ,
  λ { (y , i) → y , (proj₂ (f (x , y)) i)}

⊗-closed-l : (X Y Z : Set) → PK-Hom X (Y × Z) → PK-Hom (X × Y) Z
⊗-closed-l X Y Z f (x , y) = (Σ (proj₁ (f x)) λ i → proj₁ (proj₂ (f x) i) ≡ y) ,
  (λ i → proj₂ (proj₂ (f x) (proj₁ i)))

⊗-closed-rl : (X Y Z : Set) → (f : PK-Hom (X × Y) Z)
  → PK-≡ (⊗-closed-l X Y Z (⊗-closed-r X Y Z f)) f
proj₁ (⊗-closed-rl X Y Z f) (x , y) ((.y , i) , refl) = i , refl
proj₂ (⊗-closed-rl X Y Z f) (x , y) i = ((y , i) , refl) , refl

⊗-closed-lr : (X Y Z : Set) → (f : PK-Hom X (Y × Z))
  → PK-≡ (⊗-closed-r X Y Z (⊗-closed-l X Y Z f)) f
proj₁ (⊗-closed-lr X Y Z f) x (.(proj₁ (proj₂ (f x) i)) , i , refl) = i , refl
proj₂ (⊗-closed-lr X Y Z f) x i = ((proj₁ (proj₂ (f x) i)) , i , refl) , refl


⊗-closed-r-nat : {X X' Y Y' Z Z' : Set} → (F : PK-Hom (X × Y) Z)
  → (a : PK-Hom X' X) → (b : PK-Hom Y' Y) → (c : PK-Hom Z Z')
  → PK-≡ (⊗-closed-r X' Y' Z' (PK-∘ (a ⊗ b) (PK-∘ F c)))
         (PK-∘ a (PK-∘ (⊗-closed-r X Y Z F) (b ⇒ c)))
proj₁ (⊗-closed-r-nat F a b c) x' (y' , (i , j) , u , v) =
  (i , (((proj₂ (b y') j) , u) , ((y' , (j , refl)) , v))) , refl
proj₂ (⊗-closed-r-nat F a b c) x' (i , (.(proj₂ (b y') j) , u) , (y' , j , refl) , v) =
  (y' , ((i , j) , (u , v))) , refl


⊗-closed-l-nat : {X X' Y Y' Z Z' : Set} → (F : PK-Hom X (Y × Z))
  → (a : PK-Hom X' X) → (b : PK-Hom Y' Y) → (c : PK-Hom Z Z')
  → PK-≡ (⊗-closed-l X' Y' Z' (PK-∘ a (PK-∘ F (b ⇒ c))))
         (PK-∘ (a ⊗ b) (PK-∘ (⊗-closed-l X Y Z F) c))
proj₁ (⊗-closed-l-nat F a b c) (x' , y') ((i , u , (.y' , j , eq) , v) , refl) =
  ((i , j) , ((u , (sym eq)) , v)) , refl
proj₂ (⊗-closed-l-nat F a b c) (x' , y') ((i , j) , (u , eq) , v) =
  ((i , (u , ((y' , (j , (sym eq))) , v))) , refl) , refl


