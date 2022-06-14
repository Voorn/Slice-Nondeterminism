module Product where

open import Data.Unit
open import Data.Empty
open import Data.Sum renaming (map to map⊎)
open import Data.Nat hiding (_⊔_)
open import Data.Product renaming (map to map×)
open import Relation.Binary.PropositionalEquality hiding ([_])


open import Index-Nondeterminism


-- The product and coproduct of the category (they coincide)


-- Product and coproduct is given by disjoint union on objects ⊎
_⊕_ : {X Y X' Y' : Set} → PK-Hom X Y → PK-Hom X' Y' → PK-Hom (X ⊎ X') (Y ⊎ Y')
(f ⊕ g) (inj₁ x) = (proj₁ (f x)) , (λ i → inj₁ (proj₂ (f x) i))
(f ⊕ g) (inj₂ x') = (proj₁ (g x')) , (λ i → inj₂ (proj₂ (g x') i))



⊕-< : {X Y X' Y' : Set} → {f f' : PK-Hom X Y} → {g g' : PK-Hom X' Y'}
  → Pow-< f f' → Pow-< g g' → Pow-< (f ⊕ g) (f' ⊕ g')
⊕-< f<f' g<g' (inj₁ x) i = proj₁ (f<f' x i) , cong inj₁ (proj₂ (f<f' x i))
⊕-< f<f' g<g' (inj₂ y) i = proj₁ (g<g' y i) , cong inj₂ (proj₂ (g<g' y i))

⊕-≡ : {X Y X' Y' : Set} → {f f' : PK-Hom X Y} → {g g' : PK-Hom X' Y'}
  → PK-≡ f f' → PK-≡ g g' → PK-≡ (f ⊕ g) (f' ⊕ g')
⊕-≡ (f<f' , f'<f) (g<g' , g'<g) = (⊕-< f<f' g<g') , (⊕-< f'<f g'<g)



⊕-id : (X Y : Set) → PK-≡ ((PK-Id X) ⊕ (PK-Id Y)) (PK-Id (X ⊎ Y)) 
proj₁ (⊕-id X Y) (inj₁ x) tt = tt , refl
proj₁ (⊕-id X Y) (inj₂ y) tt = tt , refl
proj₂ (⊕-id X Y) (inj₁ x) tt = tt , refl
proj₂ (⊕-id X Y) (inj₂ y) tt = tt , refl


⊕-∘ : {X Y Z X' Y' Z' : Set}
  → (f : PK-Hom X Y) → (g : PK-Hom Y Z) → (f' : PK-Hom X' Y') → (g' : PK-Hom Y' Z')
  → PK-≡ (PK-∘ f g ⊕ PK-∘ f' g') (PK-∘ (f ⊕ f') (g ⊕ g'))
proj₁ (⊕-∘ f g f' g') (inj₁ x) ij = ij , refl
proj₁ (⊕-∘ f g f' g') (inj₂ y) ij = ij , refl
proj₂ (⊕-∘ f g f' g') (inj₁ x) ij = ij , refl
proj₂ (⊕-∘ f g f' g') (inj₂ y) ij = ij , refl


-- Unit
⊗-O : PK-Hom ⊥ ⊥
⊗-O ()






-- ⊕ is the product of the category
⊕-proj₁ : (X Y : Set) → PK-Hom (X ⊎ Y) X
⊕-proj₁ X Y (inj₁ x) = PK-Id _ x
⊕-proj₁ X Y (inj₂ y) = ⊥ , (λ {()})

⊕-proj₂ : (X Y : Set) → PK-Hom (X ⊎ Y) Y
⊕-proj₂ X Y (inj₁ x) = ⊥ , (λ {()})
⊕-proj₂ X Y (inj₂ y) = PK-Id _ y

⊕-proj₁-nat : {X Y X' Y' : Set} → (f : PK-Hom X X') → (g : PK-Hom Y Y')
  → PK-≡ (PK-∘ (⊕-proj₁ X Y) f) (PK-∘ (f ⊕ g) (⊕-proj₁ X' Y'))
proj₁ (⊕-proj₁-nat f g) (inj₁ x) (tt , i) = (i , tt) , refl
proj₂ (⊕-proj₁-nat f g) (inj₁ x) (i , tt) = (tt , i) , refl

⊕-proj₂-nat : {X Y X' Y' : Set} → (f : PK-Hom X X') → (g : PK-Hom Y Y')
  → PK-≡ (PK-∘ (⊕-proj₂ X Y) g) (PK-∘ (f ⊕ g) (⊕-proj₂ X' Y'))
proj₁ (⊕-proj₂-nat f g) (inj₂ x) (tt , i) = (i , tt) , refl
proj₂ (⊕-proj₂-nat f g) (inj₂ x) (i , tt) = (tt , i) , refl


⊎-deceq : {X Y : Set} → (a : X ⊎ Y) → (Σ X λ x → a ≡ inj₁ x) ⊎ Σ Y λ y → a ≡ inj₂ y
⊎-deceq (inj₁ x) = inj₁ (x , refl)
⊎-deceq (inj₂ y) = inj₂ (y , refl)


⊕-sew : {X Y Z : Set} → PK-Hom X Y → PK-Hom X Z → PK-Hom X (Y ⊎ Z)
⊕-sew f g x = (proj₁ (f x) ⊎ proj₁ (g x)) ,
  (λ { (inj₁ i) → inj₁ (proj₂ (f x) i) ; (inj₂ j) → inj₂ (proj₂ (g x) j)})

⊕-sew-l : {X Y Z : Set} → (f : PK-Hom X Y) → (g : PK-Hom X Z)
  → PK-≡ (PK-∘ (⊕-sew f g) (⊕-proj₁ Y Z)) f 
proj₁ (⊕-sew-l f g) x (inj₁ i , tt) = i , refl
proj₂ (⊕-sew-l f g) x i = ((inj₁ i) , tt) , refl


⊕-sew-r : {X Y Z : Set} → (f : PK-Hom X Y) → (g : PK-Hom X Z)
  → PK-≡ (PK-∘ (⊕-sew f g) (⊕-proj₂ Y Z)) g 
proj₁ (⊕-sew-r f g) x (inj₂ i , tt) = i , refl
proj₂ (⊕-sew-r f g) x i = ((inj₂ i) , tt) , refl



⊕-krab₁ : {X Y Z : Set} → (f : PK-Hom X (Y ⊎ Z)) → (x : X)
  → (i : proj₁ (f x)) → (y : Y) → (proj₂ (f x) i ≡ inj₁ y) → 
  Σ (proj₁ (f x)) (λ i₁ → proj₁ (⊕-proj₁ Y Z (proj₂ (f x) i₁)))
proj₁ (⊕-krab₁ f x i y eq) = i
proj₂ (⊕-krab₁ f x i y eq) with (proj₂ (f x) i)
... | inj₁ x₁ = tt

⊕-krab₂ : {X Y Z : Set} → (f : PK-Hom X (Y ⊎ Z)) → (x : X)
  → (i : proj₁ (f x)) → (y : Z) → (proj₂ (f x) i ≡ inj₂ y) → 
  Σ (proj₁ (f x)) (λ i₁ → proj₁ (⊕-proj₂ Y Z (proj₂ (f x) i₁)))
proj₁ (⊕-krab₂ f x i y eq) = i
proj₂ (⊕-krab₂ f x i y eq) with (proj₂ (f x) i)
... | inj₂ x₁ = tt


⊕-sew-p : {X Y Z : Set} → (f : PK-Hom X (Y ⊎ Z))
  → PK-≡ (⊕-sew (PK-∘ f (⊕-proj₁ Y Z)) (PK-∘ f (⊕-proj₂ Y Z))) f
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


⊕-sew-< : {X Y Z : Set} → (f f' : PK-Hom X Y) → (g g' : PK-Hom X Z)
  → Pow-< f f' → Pow-< g g' → Pow-< (⊕-sew f g) (⊕-sew f' g') 
⊕-sew-< f f' g g' f<f' g<g' x (inj₁ i) = (inj₁ (proj₁ (f<f' x i))) ,
  (cong inj₁ (proj₂ (f<f' x i)))
⊕-sew-< f f' g g' f<f' g<g' x (inj₂ i) = (inj₂ (proj₁ (g<g' x i))) ,
  (cong inj₂ (proj₂ (g<g' x i)))

⊕-sew-≡ : {X Y Z : Set} → (f f' : PK-Hom X Y) → (g g' : PK-Hom X Z)
  → PK-≡ f f' → PK-≡ g g' → PK-≡ (⊕-sew f g) (⊕-sew f' g') 
⊕-sew-≡ f f' g g' f≡f' g≡g' = (⊕-sew-< f f' g g' (proj₁ f≡f') (proj₁ g≡g')) ,
  ⊕-sew-< f' f g' g (proj₂ f≡f') (proj₂ g≡g')


⊕-product : (X Y Z : Set) → (f : PK-Hom Z X) → (g : PK-Hom Z Y)
  → Σ (PK-Hom Z (X ⊎ Y)) λ u →
      (PK-≡ (PK-∘ u (⊕-proj₁ _ _)) f × PK-≡ (PK-∘ u (⊕-proj₂ _ _)) g)
      × ((w : PK-Hom Z (X ⊎ Y)) →
          (PK-≡ (PK-∘ w (⊕-proj₁ _ _)) f × PK-≡ (PK-∘ w (⊕-proj₂ _ _)) g)
          → PK-≡ u w)
proj₁ (⊕-product X Y Z f g) = ⊕-sew f g
proj₁ (proj₂ (⊕-product X Y Z f g)) = (⊕-sew-l f g) , (⊕-sew-r f g)
proj₂ (proj₂ (⊕-product X Y Z f g)) w (eq₁ , eq₂) =
  PK-≡-trans
    (⊕-sew-≡ f (PK-∘ w (⊕-proj₁ X Y)) g (PK-∘ w (⊕-proj₂ X Y)) (PK-≡-sym eq₁) (PK-≡-sym eq₂))
    (⊕-sew-p w)

-- coproduct
⊕-inj₁ : (X Y : Set) → PK-Hom X (X ⊎ Y)
⊕-inj₁ X Y x = PK-Id _ (inj₁ x)

⊕-inj₂ : (X Y : Set) → PK-Hom Y (X ⊎ Y)
⊕-inj₂ X Y y = PK-Id _ (inj₂ y)


⊕-inj₁-rev : (X Y : Set) → PK-≡ (PK-rev (⊕-inj₁ X Y)) (⊕-proj₁ X Y)
proj₁ (⊕-inj₁-rev X Y) (inj₁ x) (.x , tt , refl) = tt , refl
proj₂ (⊕-inj₁-rev X Y) (inj₁ x) tt = (x , (tt , refl)) , refl

⊕-inj₂-rev : (X Y : Set) → PK-≡ (PK-rev (⊕-inj₂ X Y)) (⊕-proj₂ X Y)
proj₁ (⊕-inj₂-rev X Y) (inj₂ y) (.y , tt , refl) = tt , refl
proj₂ (⊕-inj₂-rev X Y) (inj₂ y) tt = (y , (tt , refl)) , refl


⊕-inj₁-proj₁ : (X Y : Set) → PK-≡ (PK-∘ (⊕-inj₁ X Y) (⊕-proj₁ X Y)) (PK-Id _)
proj₁ (⊕-inj₁-proj₁ X Y) x i = tt , refl
proj₂ (⊕-inj₁-proj₁ X Y) x i = (tt , tt) , refl

⊕-inj₂-proj₂ : (X Y : Set) → PK-≡ (PK-∘ (⊕-inj₂ X Y) (⊕-proj₂ X Y)) (PK-Id _)
proj₁ (⊕-inj₂-proj₂ X Y) y i = tt , refl
proj₂ (⊕-inj₂-proj₂ X Y) y i = (tt , tt) , refl


⊕-cosew : {X Y Z : Set} → PK-Hom X Z → PK-Hom Y Z → PK-Hom (X ⊎ Y) Z
⊕-cosew f g (inj₁ x) = f x
⊕-cosew f g (inj₂ y) = g y


⊕-coproduct : {X Y Z : Set} → (f : PK-Hom X Z) → (g : PK-Hom Y Z)
  → Σ (PK-Hom (X ⊎ Y) Z) λ u →
      (PK-≡ (PK-∘ (⊕-inj₁ _ _) u) f × PK-≡ (PK-∘ (⊕-inj₂ _ _) u) g)
      × ((w : PK-Hom (X ⊎ Y) Z) →
          (PK-≡ (PK-∘ (⊕-inj₁ _ _) w) f × PK-≡ (PK-∘ (⊕-inj₂ _ _) w) g)
          → PK-≡ u w)
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
