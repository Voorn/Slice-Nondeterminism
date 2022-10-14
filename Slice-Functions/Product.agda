module Slice-Functions.Product where

open import Data.Unit
open import Data.Empty
open import Data.Sum renaming (map to map⊎)
open import Data.Nat hiding (_⊔_)
open import Data.Product renaming (map to map×)
open import Relation.Binary.PropositionalEquality hiding ([_])


open import Slice-Functions.Base


-- The product and coproduct of the category (they coincide)


-- Product and coproduct is given by disjoint union on objects ⊎
_⊕_ : {X Y X' Y' : Set} → SF X Y → SF X' Y' → SF (X ⊎ X') (Y ⊎ Y')
(f ⊕ g) (inj₁ x) = (proj₁ (f x)) , (λ i → inj₁ (proj₂ (f x) i))
(f ⊕ g) (inj₂ x') = (proj₁ (g x')) , (λ i → inj₂ (proj₂ (g x') i))



⊕-< : {X Y X' Y' : Set} → {f f' : SF X Y} → {g g' : SF X' Y'}
  → SF≤ f f' → SF≤ g g' → SF≤ (f ⊕ g) (f' ⊕ g')
⊕-< f<f' g<g' (inj₁ x) i = proj₁ (f<f' x i) , cong inj₁ (proj₂ (f<f' x i))
⊕-< f<f' g<g' (inj₂ y) i = proj₁ (g<g' y i) , cong inj₂ (proj₂ (g<g' y i))

⊕-≡ : {X Y X' Y' : Set} → {f f' : SF X Y} → {g g' : SF X' Y'}
  → SF≡ f f' → SF≡ g g' → SF≡ (f ⊕ g) (f' ⊕ g')
⊕-≡ (f<f' , f'<f) (g<g' , g'<g) = (⊕-< f<f' g<g') , (⊕-< f'<f g'<g)



⊕-id : (X Y : Set) → SF≡ ((SF-id X) ⊕ (SF-id Y)) (SF-id (X ⊎ Y)) 
proj₁ (⊕-id X Y) (inj₁ x) tt = tt , refl
proj₁ (⊕-id X Y) (inj₂ y) tt = tt , refl
proj₂ (⊕-id X Y) (inj₁ x) tt = tt , refl
proj₂ (⊕-id X Y) (inj₂ y) tt = tt , refl


⊕-∘ : {X Y Z X' Y' Z' : Set}
  → (f : SF X Y) → (g : SF Y Z) → (f' : SF X' Y') → (g' : SF Y' Z')
  → SF≡ (SF-∘ f g ⊕ SF-∘ f' g') (SF-∘ (f ⊕ f') (g ⊕ g'))
proj₁ (⊕-∘ f g f' g') (inj₁ x) ij = ij , refl
proj₁ (⊕-∘ f g f' g') (inj₂ y) ij = ij , refl
proj₂ (⊕-∘ f g f' g') (inj₁ x) ij = ij , refl
proj₂ (⊕-∘ f g f' g') (inj₂ y) ij = ij , refl


-- Unit
⊗-O : SF ⊥ ⊥
⊗-O ()




-- product structure of ⊎
⊕-proj₁ : (X Y : Set) → SF (X ⊎ Y) X
⊕-proj₁ X Y (inj₁ x) = SF-id _ x
⊕-proj₁ X Y (inj₂ y) = ⊥ , (λ {()})

⊕-proj₂ : (X Y : Set) → SF (X ⊎ Y) Y
⊕-proj₂ X Y (inj₁ x) = ⊥ , (λ {()})
⊕-proj₂ X Y (inj₂ y) = SF-id _ y

⊕-proj₁-nat : {X Y X' Y' : Set} → (f : SF X X') → (g : SF Y Y')
  → SF≡ (SF-∘ (⊕-proj₁ X Y) f) (SF-∘ (f ⊕ g) (⊕-proj₁ X' Y'))
proj₁ (⊕-proj₁-nat f g) (inj₁ x) (tt , i) = (i , tt) , refl
proj₂ (⊕-proj₁-nat f g) (inj₁ x) (i , tt) = (tt , i) , refl

⊕-proj₂-nat : {X Y X' Y' : Set} → (f : SF X X') → (g : SF Y Y')
  → SF≡ (SF-∘ (⊕-proj₂ X Y) g) (SF-∘ (f ⊕ g) (⊕-proj₂ X' Y'))
proj₁ (⊕-proj₂-nat f g) (inj₂ x) (tt , i) = (i , tt) , refl
proj₂ (⊕-proj₂-nat f g) (inj₂ x) (i , tt) = (tt , i) , refl


⊎-deceq : {X Y : Set} → (a : X ⊎ Y) → (Σ X λ x → a ≡ inj₁ x) ⊎ Σ Y λ y → a ≡ inj₂ y
⊎-deceq (inj₁ x) = inj₁ (x , refl)
⊎-deceq (inj₂ y) = inj₂ (y , refl)


-- We start working towards explicitly showing that ⊎ is the categorical product
⊕-sew : {X Y Z : Set} → SF X Y → SF X Z → SF X (Y ⊎ Z)
⊕-sew f g x = (proj₁ (f x) ⊎ proj₁ (g x)) ,
  (λ { (inj₁ i) → inj₁ (proj₂ (f x) i) ; (inj₂ j) → inj₂ (proj₂ (g x) j)})

⊕-sew-l : {X Y Z : Set} → (f : SF X Y) → (g : SF X Z)
  → SF≡ (SF-∘ (⊕-sew f g) (⊕-proj₁ Y Z)) f 
proj₁ (⊕-sew-l f g) x (inj₁ i , tt) = i , refl
proj₂ (⊕-sew-l f g) x i = ((inj₁ i) , tt) , refl


⊕-sew-r : {X Y Z : Set} → (f : SF X Y) → (g : SF X Z)
  → SF≡ (SF-∘ (⊕-sew f g) (⊕-proj₂ Y Z)) g 
proj₁ (⊕-sew-r f g) x (inj₂ i , tt) = i , refl
proj₂ (⊕-sew-r f g) x i = ((inj₂ i) , tt) , refl



⊕-krab₁ : {X Y Z : Set} → (f : SF X (Y ⊎ Z)) → (x : X)
  → (i : proj₁ (f x)) → (y : Y) → (proj₂ (f x) i ≡ inj₁ y) → 
  Σ (proj₁ (f x)) (λ i₁ → proj₁ (⊕-proj₁ Y Z (proj₂ (f x) i₁)))
proj₁ (⊕-krab₁ f x i y eq) = i
proj₂ (⊕-krab₁ f x i y eq) with (proj₂ (f x) i)
... | inj₁ x₁ = tt

⊕-krab₂ : {X Y Z : Set} → (f : SF X (Y ⊎ Z)) → (x : X)
  → (i : proj₁ (f x)) → (y : Z) → (proj₂ (f x) i ≡ inj₂ y) → 
  Σ (proj₁ (f x)) (λ i₁ → proj₁ (⊕-proj₂ Y Z (proj₂ (f x) i₁)))
proj₁ (⊕-krab₂ f x i y eq) = i
proj₂ (⊕-krab₂ f x i y eq) with (proj₂ (f x) i)
... | inj₂ x₁ = tt


⊕-sew-p : {X Y Z : Set} → (f : SF X (Y ⊎ Z))
  → SF≡ (⊕-sew (SF-∘ f (⊕-proj₁ Y Z)) (SF-∘ f (⊕-proj₂ Y Z))) f
proj₁ (proj₁ (⊕-sew-p f) x (inj₁ (i , j))) = i
proj₂ (proj₁ (⊕-sew-p f) x (inj₁ (i , j))) with proj₂ (f x) i
... | inj₁ y = refl
proj₁ (proj₁ (⊕-sew-p f) x (inj₂ (i , j))) = i
proj₂ (proj₁ (⊕-sew-p f) x (inj₂ (i , j))) with proj₂ (f x) i
... | inj₂ z = refl

proj₁ (proj₂ (⊕-sew-p f) x i) with ⊎-deceq (proj₂ (f x) i) 
... | inj₁ (y , eq) = (inj₁ (⊕-krab₁ f x i y eq))
... | inj₂ (z , eq) = (inj₂ (⊕-krab₂ f x i z eq))
proj₂ (proj₂ (⊕-sew-p f) x i) with ⊎-deceq (proj₂ (f x) i)
proj₂ (proj₂ (⊕-sew-p f) x i) | inj₁ (y , eq) with proj₂ (f x) i
... | inj₁ x₁ = refl
proj₂ (proj₂ (⊕-sew-p f) x i) | inj₂ (z , eq) with proj₂ (f x) i
... | inj₂ y₁ = refl


⊕-sew-< : {X Y Z : Set} → (f f' : SF X Y) → (g g' : SF X Z)
  → SF≤ f f' → SF≤ g g' → SF≤ (⊕-sew f g) (⊕-sew f' g') 
⊕-sew-< f f' g g' f<f' g<g' x (inj₁ i) = (inj₁ (proj₁ (f<f' x i))) ,
  (cong inj₁ (proj₂ (f<f' x i)))
⊕-sew-< f f' g g' f<f' g<g' x (inj₂ i) = (inj₂ (proj₁ (g<g' x i))) ,
  (cong inj₂ (proj₂ (g<g' x i)))

⊕-sew-≡ : {X Y Z : Set} → (f f' : SF X Y) → (g g' : SF X Z)
  → SF≡ f f' → SF≡ g g' → SF≡ (⊕-sew f g) (⊕-sew f' g') 
⊕-sew-≡ f f' g g' f≡f' g≡g' = (⊕-sew-< f f' g g' (proj₁ f≡f') (proj₁ g≡g')) ,
  ⊕-sew-< f' f g' g (proj₂ f≡f') (proj₂ g≡g')


-- ⊎ is the categorical product
⊕-product : (X Y Z : Set) → (f : SF Z X) → (g : SF Z Y)
  → Σ (SF Z (X ⊎ Y)) λ u →
      (SF≡ (SF-∘ u (⊕-proj₁ _ _)) f × SF≡ (SF-∘ u (⊕-proj₂ _ _)) g)
      × ((w : SF Z (X ⊎ Y)) →
          (SF≡ (SF-∘ w (⊕-proj₁ _ _)) f × SF≡ (SF-∘ w (⊕-proj₂ _ _)) g)
          → SF≡ u w)
proj₁ (⊕-product X Y Z f g) = ⊕-sew f g
proj₁ (proj₂ (⊕-product X Y Z f g)) = (⊕-sew-l f g) , (⊕-sew-r f g)
proj₂ (proj₂ (⊕-product X Y Z f g)) w (eq₁ , eq₂) =
  SF≡-Tran _ _ _
    (⊕-sew-≡ f (SF-∘ w (⊕-proj₁ X Y)) g (SF-∘ w (⊕-proj₂ X Y)) (SF≡-Symm _ _ eq₁)
             (SF≡-Symm _ _ eq₂))
    (⊕-sew-p w)




-- Coproduct structure of ⊎
⊕-inj₁ : (X Y : Set) → SF X (X ⊎ Y)
⊕-inj₁ X Y x = SF-id _ (inj₁ x)

⊕-inj₂ : (X Y : Set) → SF Y (X ⊎ Y)
⊕-inj₂ X Y y = SF-id _ (inj₂ y)


-- Working towards a proof that ⊎ is the categorical coproduct
open import Slice-Functions.Dagger
⊕-inj₁-dag : (X Y : Set) → SF≡ (SF-dag (⊕-inj₁ X Y)) (⊕-proj₁ X Y)
proj₁ (⊕-inj₁-dag X Y) (inj₁ x) (.x , tt , refl) = tt , refl
proj₂ (⊕-inj₁-dag X Y) (inj₁ x) tt = (x , (tt , refl)) , refl

⊕-inj₂-dag : (X Y : Set) → SF≡ (SF-dag (⊕-inj₂ X Y)) (⊕-proj₂ X Y)
proj₁ (⊕-inj₂-dag X Y) (inj₂ y) (.y , tt , refl) = tt , refl
proj₂ (⊕-inj₂-dag X Y) (inj₂ y) tt = (y , (tt , refl)) , refl


⊕-inj₁-proj₁ : (X Y : Set) → SF≡ (SF-∘ (⊕-inj₁ X Y) (⊕-proj₁ X Y)) (SF-id _)
proj₁ (⊕-inj₁-proj₁ X Y) x i = tt , refl
proj₂ (⊕-inj₁-proj₁ X Y) x i = (tt , tt) , refl

⊕-inj₂-proj₂ : (X Y : Set) → SF≡ (SF-∘ (⊕-inj₂ X Y) (⊕-proj₂ X Y)) (SF-id _)
proj₁ (⊕-inj₂-proj₂ X Y) y i = tt , refl
proj₂ (⊕-inj₂-proj₂ X Y) y i = (tt , tt) , refl


⊕-cosew : {X Y Z : Set} → SF X Z → SF Y Z → SF (X ⊎ Y) Z
⊕-cosew f g (inj₁ x) = f x
⊕-cosew f g (inj₂ y) = g y


-- ⊎ is the Categorical coproduct
⊕-coproduct : {X Y Z : Set} → (f : SF X Z) → (g : SF Y Z)
  → Σ (SF (X ⊎ Y) Z) λ u →
      (SF≡ (SF-∘ (⊕-inj₁ _ _) u) f × SF≡ (SF-∘ (⊕-inj₂ _ _) u) g)
      × ((w : SF (X ⊎ Y) Z) →
          (SF≡ (SF-∘ (⊕-inj₁ _ _) w) f × SF≡ (SF-∘ (⊕-inj₂ _ _) w) g)
          → SF≡ u w)
proj₁ (⊕-coproduct f g) = (⊕-cosew f g)
proj₁ (proj₂ (⊕-coproduct f g)) =
  (((λ x i → (proj₂ i) , refl) , (λ x i → (tt , i) , refl)) ,
     (λ x i → (proj₂ i) , refl) , (λ x i → (tt , i) , refl))
proj₁ (proj₂ (proj₂ (⊕-coproduct f g)) w ((₁w<f , f<₁w) , ₂w<g , g<₂w)) (inj₁ x) i =
  (proj₂ (proj₁ (f<₁w x i))) , (proj₂ (f<₁w x i))
proj₁ (proj₂ (proj₂ (⊕-coproduct f g)) w ((₁w<f , f<₁w) , ₂w<g , g<₂w)) (inj₂ y) i =
  (proj₂ (proj₁ (g<₂w y i))) , (proj₂ (g<₂w y i))
proj₂ (proj₂ (proj₂ (⊕-coproduct f g)) w ((₁w<f , f<₁w) , ₂w<g , g<₂w)) (inj₁ x) i =
  (₁w<f x (tt , i))
proj₂ (proj₂ (proj₂ (⊕-coproduct f g)) w ((₁w<f , f<₁w) , ₂w<g , g<₂w)) (inj₂ y) i =
  (₂w<g y (tt , i))
