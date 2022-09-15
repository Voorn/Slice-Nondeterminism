module Slice-Functions.Monoidal where

open import Data.Unit
open import Data.Empty
open import Data.Sum renaming (map to map⊎)
open import Data.Nat hiding (_⊔_)
open import Data.Product renaming (map to map×)
open import Relation.Binary.PropositionalEquality hiding ([_])


open import Slice-Functions.Base
open import Slice-Functions.Dagger

-- The Monoidal closed structure of the category


_⊗_ : {X Y X' Y' : Set} → SF X Y → SF X' Y' → SF (X × X') (Y × Y')
(f ⊗ g) (x , x') = ((proj₁ (f x)) × (proj₁ (g x'))) ,
                   (λ (i , j) → (proj₂ (f x) i) , (proj₂ (g x') j))

⊗-< : {X Y X' Y' : Set} → {f f' : SF X Y} → {g g' : SF X' Y'}
  → SF≤ f f' → SF≤ g g' → SF≤ (f ⊗ g) (f' ⊗ g')
⊗-< f<f' g<g' (x , x') (i , j) = ((proj₁ (f<f' x i)) , (proj₁ (g<g' x' j))) ,
  (cong₂ (λ l r → l , r) (proj₂ (f<f' x i)) (proj₂ (g<g' x' j)))

⊗-≡ : {X Y X' Y' : Set} → {f f' : SF X Y} → {g g' : SF X' Y'}
  → SF≡ f f' → SF≡ g g' → SF≡ (f ⊗ g) (f' ⊗ g')
⊗-≡ (f<f' , f'<f) (g<g' , g'<g) = (⊗-< f<f' g<g') , (⊗-< f'<f g'<g)

⊗-≡-right : {X Y X' Y' : Set} → (f  : SF X Y) → {g g' : SF X' Y'}
  → SF≡ g g' → SF≡ (f ⊗ g) (f ⊗ g')
⊗-≡-right f g≡g' = ⊗-≡ (SF≡-Refl f) g≡g'


⊗-id : (X Y : Set) → SF≡ ((SF-id X) ⊗ (SF-id Y)) (SF-id (X × Y)) 
proj₁ (⊗-id X Y) (x , y) (tt , tt) = tt , refl
proj₂ (⊗-id X Y) (x , y) tt = (tt , tt) , refl


⊗-∘ : {X Y Z X' Y' Z' : Set}
  → (f : SF X Y) → (g : SF Y Z) → (f' : SF X' Y') → (g' : SF Y' Z')
  → SF≡ (SF-∘ f g ⊗ SF-∘ f' g') (SF-∘ (f ⊗ f') (g ⊗ g'))
proj₁ (⊗-∘ f g f' g') (x , x') ((i , j) , (i' , j')) = ((i , i') , (j , j')) , refl
proj₂ (⊗-∘ f g f' g') (x , x') ((i , i') , (j , j')) = ((i , j) , (i' , j')) , refl


⊗-01-split : {X Y Z W : Set} → (f : SF X Y) → (g : SF Z W)
  → SF≡ (f ⊗ g) (SF-∘ (f ⊗ SF-id _) (SF-id _ ⊗ g))
proj₁ (⊗-01-split f g) (x , y) (i , j) = ((i , tt) , tt , j) , refl
proj₂ (⊗-01-split f g) (x , y) ((i , tt) , (tt , j)) = (i , j) , refl

⊗-10-split : {X Y Z W : Set} → (f : SF X Y) → (g : SF Z W)
  → SF≡ (f ⊗ g) (SF-∘ (SF-id _ ⊗ g) (f ⊗ SF-id _))
proj₁ (⊗-10-split f g) (x , y) (i , j) = ((tt , j) , (i , tt)) , refl
proj₂ (⊗-10-split f g) (x , y) ((tt , i) , (j , tt)) = (j , i) , refl

⊗-trade :  {X Y Z W : Set} → (f : SF X Y) → (g : SF Z W)
  → SF≡ (SF-∘ (f ⊗ SF-id _) (SF-id _ ⊗ g)) (SF-∘ (SF-id _ ⊗ g) (f ⊗ SF-id _))
⊗-trade f g = SF≡-Tran _ _ _ (SF≡-Symm _ _ (⊗-01-split f g)) (⊗-10-split f g)

⊗-γ : (X Y : Set) → SF (X × Y) (Y × X)
⊗-γ X Y (x , y) = SF-id _ (y , x)


⊗-γγ : (X Y : Set) → SF≡ (SF-∘ (⊗-γ X Y) (⊗-γ Y X)) (SF-id (X × Y))
proj₁ (⊗-γγ X Y) (x , y) (tt , tt) = tt , refl
proj₂ (⊗-γγ X Y) (x , y) tt = (tt , tt) , refl

⊗-γ-dag : (X Y : Set) → SF≡ (SF-dag (⊗-γ X Y)) (⊗-γ Y X)
proj₁ (⊗-γ-dag X Y) (y , x) ((.x , .y) , tt , refl) = tt , refl
proj₂ (⊗-γ-dag X Y) (y , x) tt = ((x , y) , (tt , refl)) , refl

⊗-γ-nat : {X Y X' Y' : Set} → (f : SF X X') → (g : SF Y Y')
  → SF≡ (SF-∘ (⊗-γ X Y) (g ⊗ f)) (SF-∘ (f ⊗ g) (⊗-γ X' Y'))
proj₁ (⊗-γ-nat f g) (x , y) (tt , (j , i)) = ((i , j) , tt) , refl
proj₂ (⊗-γ-nat f g) (x , y) ((i , j) , tt) = (tt , (j , i)) , refl



⊗-α : (X Y Z : Set) → SF ((X × Y) × Z) (X × (Y × Z))
⊗-α X Y Z ((x , y) , z) = SF-id _ (x , (y , z))

⊗-α' : (X Y Z : Set) → SF (X × (Y × Z)) ((X × Y) × Z)
⊗-α' X Y Z (x , (y , z)) = SF-id _ ((x , y) , z)

⊗-αα' : (X Y Z : Set) → SF≡ (SF-∘ (⊗-α X Y Z) (⊗-α' X Y Z)) (SF-id _)
⊗-αα' X Y Z = (λ x i → tt , refl) , (λ x i → (tt , tt) , refl)

⊗-α'α : (X Y Z : Set) → SF≡ (SF-∘ (⊗-α' X Y Z) (⊗-α X Y Z)) (SF-id _)
⊗-α'α X Y Z = (λ x i → tt , refl) , (λ x i → (tt , tt) , refl)

⊗-α-dag : (X Y Z : Set) → SF≡ (SF-dag (⊗-α X Y Z)) (⊗-α' X Y Z)
proj₁ (⊗-α-dag X Y Z) (x , y , z) (((.x , .y) , .z) , tt , refl) = tt , refl
proj₂ (⊗-α-dag X Y Z) (x , y , z) tt = (((x , y) , z) , (tt , refl)) , refl

⊗-α-nat : {X Y Z X' Y' Z' : Set} → (f : SF X X') → (g : SF Y Y') → (h : SF Z Z')
  → SF≡ (SF-∘ (⊗-α X Y Z) (f ⊗ (g ⊗ h))) (SF-∘ ((f ⊗ g) ⊗ h) (⊗-α X' Y' Z'))
proj₁ (⊗-α-nat f g h) ((x , y) , z) (tt , i , j , k) = (((i , j) , k) , tt) , refl
proj₂ (⊗-α-nat f g h) ((x , y) , z) (((i , j) , k) , tt) = (tt , i , j , k) , refl



-- Monoidal unit
⊗-I : SF ⊤ ⊤
⊗-I tt = ⊤ , (λ i → tt)


⊗-proj₁ : (X Y : Set) → SF (X × Y) X
⊗-proj₁ X Y = SF-Fun proj₁


-- Monoidal Closed
_⇒_ : {X X' Y Y' : Set} → (SF X' X) → (SF Y Y') → (SF (X × Y) (X' × Y'))
f ⇒ g = SF-dag f ⊗ g


⊗-closed-r : (X Y Z : Set) → SF (X × Y) Z → SF X (Y × Z)
⊗-closed-r X Y Z f x = (Σ Y λ y → proj₁ (f (x , y))) ,
  λ { (y , i) → y , (proj₂ (f (x , y)) i)}

⊗-closed-l : (X Y Z : Set) → SF X (Y × Z) → SF (X × Y) Z
⊗-closed-l X Y Z f (x , y) = (Σ (proj₁ (f x)) λ i → proj₁ (proj₂ (f x) i) ≡ y) ,
  (λ i → proj₂ (proj₂ (f x) (proj₁ i)))

⊗-closed-rl : (X Y Z : Set) → (f : SF (X × Y) Z)
  → SF≡ (⊗-closed-l X Y Z (⊗-closed-r X Y Z f)) f
proj₁ (⊗-closed-rl X Y Z f) (x , y) ((.y , i) , refl) = i , refl
proj₂ (⊗-closed-rl X Y Z f) (x , y) i = ((y , i) , refl) , refl

⊗-closed-lr : (X Y Z : Set) → (f : SF X (Y × Z))
  → SF≡ (⊗-closed-r X Y Z (⊗-closed-l X Y Z f)) f
proj₁ (⊗-closed-lr X Y Z f) x (.(proj₁ (proj₂ (f x) i)) , i , refl) = i , refl
proj₂ (⊗-closed-lr X Y Z f) x i = ((proj₁ (proj₂ (f x) i)) , i , refl) , refl


⊗-closed-r-nat : {X X' Y Y' Z Z' : Set} → (F : SF (X × Y) Z)
  → (a : SF X' X) → (b : SF Y' Y) → (c : SF Z Z')
  → SF≡ (⊗-closed-r X' Y' Z' (SF-∘ (a ⊗ b) (SF-∘ F c)))
         (SF-∘ a (SF-∘ (⊗-closed-r X Y Z F) (b ⇒ c)))
proj₁ (⊗-closed-r-nat F a b c) x' (y' , (i , j) , u , v) =
  (i , (((proj₂ (b y') j) , u) , ((y' , (j , refl)) , v))) , refl
proj₂ (⊗-closed-r-nat F a b c) x' (i , (.(proj₂ (b y') j) , u) , (y' , j , refl) , v) =
  (y' , ((i , j) , (u , v))) , refl


⊗-closed-l-nat : {X X' Y Y' Z Z' : Set} → (F : SF X (Y × Z))
  → (a : SF X' X) → (b : SF Y' Y) → (c : SF Z Z')
  → SF≡ (⊗-closed-l X' Y' Z' (SF-∘ a (SF-∘ F (b ⇒ c))))
         (SF-∘ (a ⊗ b) (SF-∘ (⊗-closed-l X Y Z F) c))
proj₁ (⊗-closed-l-nat F a b c) (x' , y') ((i , u , (.y' , j , eq) , v) , refl) =
  ((i , j) , ((u , (sym eq)) , v)) , refl
proj₂ (⊗-closed-l-nat F a b c) (x' , y') ((i , j) , (u , eq) , v) =
  ((i , (u , ((y' , (j , (sym eq))) , v))) , refl) , refl


