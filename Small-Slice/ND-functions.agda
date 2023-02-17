module Small-Slice.ND-functions where

open import Data.Unit
open import Data.Empty
open import Data.Sum renaming (map to map⊎)
open import Data.Nat hiding (_⊔_)
open import Data.Product renaming (map to map×)
open import Relation.Binary.Core

open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Binary.Structures
open import Relation.Binary.Definitions

open import Small-Slice.Univ


-- Morphisms in the Kleisli category over 𝕌SL
𝕌Hom : Set → Set → Set
𝕌Hom X Y = X → 𝕌SL Y

𝕌Hom-⊂ : {X Y : Set} → 𝕌Hom X Y → 𝕌Hom X Y → Set
𝕌Hom-⊂ {X} {Y} f g = (x : X) → 𝕌SL→ Y (f x) (g x)

𝕌Hom-≡ : {X Y : Set} → 𝕌Hom X Y → 𝕌Hom X Y → Set
𝕌Hom-≡ f g = 𝕌Hom-⊂ f g × 𝕌Hom-⊂ g f

𝕌Hom-id : (X : Set) → 𝕌Hom X X
𝕌Hom-id X x = 𝕌SL-η x

𝕌Hom-∘ : {X Y Z : Set} → 𝕌Hom Y Z → 𝕌Hom X Y → 𝕌Hom X Z
𝕌Hom-∘ g f x = 𝕌SL-κ g (f x)

-- Properties
𝕌Hom-⊂-Refl : {X Y : Set} → {f : 𝕌Hom X Y} → Reflexive (𝕌Hom-⊂ {X} {Y})
𝕌Hom-⊂-Refl x i = i , refl

𝕌Hom-≡-Refl : {X Y : Set} → {f : 𝕌Hom X Y} → Reflexive (𝕌Hom-≡ {X} {Y})
𝕌Hom-≡-Refl {X} {Y} {f} = 𝕌Hom-⊂-Refl {X} {Y} {f} , 𝕌Hom-⊂-Refl {X} {Y} {f}

𝕌Hom-≡-Symm : {X Y : Set} → Symmetric (𝕌Hom-≡ {X} {Y})
𝕌Hom-≡-Symm (a , b) = (b , a)

𝕌Hom-⊂-Trans : {X Y : Set} → Transitive (𝕌Hom-⊂ {X} {Y})
𝕌Hom-⊂-Trans {X} {Y} {f} {g} {h} f⊂g g⊂h x i with (f⊂g x i)
...| (j , eq) = proj₁ (g⊂h x j) , trans eq (proj₂ (g⊂h x j))

𝕌Hom-≡-Trans : {X Y : Set} → Transitive (𝕌Hom-≡ {X} {Y})
𝕌Hom-≡-Trans (f⊂g , g⊂f) (g⊂h , h⊂g) =
  (𝕌Hom-⊂-Trans f⊂g g⊂h) , (𝕌Hom-⊂-Trans h⊂g g⊂f)



𝕌Hom-≡-equiv : {X Y : Set} → IsEquivalence (𝕌Hom-≡ {X} {Y})
𝕌Hom-≡-equiv {X} {Y} = record
  { refl = λ {f} → 𝕌Hom-≡-Refl {X} {Y} {f}
  ; sym = 𝕌Hom-≡-Symm
  ; trans = 𝕌Hom-≡-Trans
  }


--
𝕌Hom-∘⊂ : {X Y Z : Set} → {f f' : 𝕌Hom X Y} → {g g' : 𝕌Hom Y Z}
  → 𝕌Hom-⊂ f f' → 𝕌Hom-⊂ g g' → 𝕌Hom-⊂ (𝕌Hom-∘ g f) (𝕌Hom-∘ g' f')
𝕌Hom-∘⊂ {_} {_} {_} {f} {f'} f⊂f' g⊂g' x (i , j) with (f⊂f' x i)
...| (i' , eq) rewrite eq = (i' , (proj₁ (g⊂g' (proj₂ (f' x) i') j))) ,
                            (proj₂ (g⊂g' (proj₂ (f' x) i') j))

𝕌Hom-∘≡ : {X Y Z : Set} → {f f' : 𝕌Hom X Y} → {g g' : 𝕌Hom Y Z}
  → 𝕌Hom-≡ f f' → 𝕌Hom-≡ g g' → 𝕌Hom-≡ (𝕌Hom-∘ g f) (𝕌Hom-∘ g' f')
𝕌Hom-∘≡ (f⊂f' , f'⊂f) (g⊂g' , g'⊂g) = (𝕌Hom-∘⊂ f⊂f' g⊂g') , (𝕌Hom-∘⊂ f'⊂f g'⊂g)

--extra
𝕌Hom-∘r≡ : {X Y Z : Set} → {f f' : 𝕌Hom X Y} → (g : 𝕌Hom Y Z)
  → 𝕌Hom-≡ f f' → 𝕌Hom-≡ (𝕌Hom-∘ g f) (𝕌Hom-∘ g f')
𝕌Hom-∘r≡ g f≡f' =
  𝕌Hom-∘≡ {_} {_} {_} {_} {_} {g} {g} f≡f' (𝕌Hom-≡-Refl {_} {_} {g})

𝕌Hom-∘l≡ : {X Y Z : Set} → (f : 𝕌Hom X Y) → {g g' : 𝕌Hom Y Z}
  → 𝕌Hom-≡ g g' → 𝕌Hom-≡ (𝕌Hom-∘ g f) (𝕌Hom-∘ g' f)
𝕌Hom-∘l≡ f g≡g' =
  𝕌Hom-∘≡ {_} {_} {_} {f} {f} (𝕌Hom-≡-Refl {_} {_} {f}) g≡g' 

𝕌Hom-asso : {X Y Z W : Set} → (f : 𝕌Hom X Y) → (g : 𝕌Hom Y Z) → (h : 𝕌Hom Z W)
  → 𝕌Hom-≡ (𝕌Hom-∘ (𝕌Hom-∘ h g) f) (𝕌Hom-∘ h (𝕌Hom-∘ g f))
𝕌Hom-asso _ _ _ =
  (λ {x (i , (j , k)) → ((i , j) , k) , refl}) ,
  (λ {x ((i , j) , k) → (i , (j , k)) , refl})

𝕌Hom-sym-asso : {X Y Z W : Set} → (f : 𝕌Hom X Y) → (g : 𝕌Hom Y Z) → (h : 𝕌Hom Z W)
  → 𝕌Hom-≡ (𝕌Hom-∘ h (𝕌Hom-∘ g f)) (𝕌Hom-∘ (𝕌Hom-∘ h g) f)
𝕌Hom-sym-asso f g h = 𝕌Hom-≡-Symm
  {_} {_} {(𝕌Hom-∘ (𝕌Hom-∘ h g) f)} {(𝕌Hom-∘ h (𝕌Hom-∘ g f)) } (𝕌Hom-asso f g h)

𝕌Hom-rid : {X Y : Set} → (f : 𝕌Hom X Y) → 𝕌Hom-≡ (𝕌Hom-∘ f (𝕌Hom-id X)) f
𝕌Hom-rid f = (λ {x (tt , i) → i , refl}) , λ x i → (tt , i) , refl

𝕌Hom-lid : {X Y : Set} → (f : 𝕌Hom X Y) → 𝕌Hom-≡ (𝕌Hom-∘ (𝕌Hom-id Y) f) f
𝕌Hom-lid f = (λ {x (i , tt) → i , refl}) , λ x i → (i , tt) , refl

𝕌Hom-did : {X : Set} → 𝕌Hom-≡ (𝕌Hom-∘ (𝕌Hom-id X) (𝕌Hom-id X)) (𝕌Hom-id X)
𝕌Hom-did = (λ x i → tt , refl) , (λ x i → (tt , tt) , refl)




-- Set functor
𝕌Hom-fun : {X Y : Set} → (X → Y) → 𝕌Hom X Y
𝕌Hom-fun f x = 𝕌SL-η (f x)

