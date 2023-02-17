module Relations.Category where

-- Agda standard library
open import Data.Unit
open import Data.Empty
open import Data.Sum renaming (map to map⊎)
open import Data.Product renaming (map to map×)
open import Relation.Binary.PropositionalEquality hiding ([_])

-- Categories library
open import Categories.Category.Instance.Rels
open import Categories.Category.Equivalence hiding (refl ; sym )
open import Categories.NaturalTransformation.Core
open import Categories.NaturalTransformation.NaturalIsomorphism hiding (refl ; sym)
open import Categories.Category
open import Categories.Functor

-- Development library
open import Relations.Cat-Equivalences
open import Relations.Ext-Rel
open import Slice-Functions.Base
open import Slice-Functions.Category
open import Relations.Ext-Rel


ER-Cat : Category _ _ _
ER-Cat = record
  { Obj = Set
  ; _⇒_ = ER
  ; _≈_ = ER≡
  ; id = ER-id _
  ; _∘_ = λ g f → ER-∘ f g
  ; assoc = λ {_ _ _ _ f g h} → ER≡-Symm _ _ (ER-asso f g h)
  ; sym-assoc = λ {_ _ _ _ f g h} → ER-asso f g h
  ; identityˡ = λ {_ _ f} → ER-runi f
  ; identityʳ = λ {_ _ f} → ER-luni f
  ; identity² = (λ { a .a (.a , refl , refl) → refl}) , λ { a .a refl → a , (refl , refl)}
  ; equiv = record
    { refl = ER≡-Refl _
    ; sym = λ f → ER≡-Symm _ _ f
    ; trans = λ f g → ER≡-Tran _ _ _ f g
    }
  ; ∘-resp-≈ = ER-∘≡ 
  }




SF→ER-Func : Functor SF-Cat ER-Cat
SF→ER-Func = record
   { F₀ = λ X → X
   ; F₁ = SF→ER
   ; identity = SF→ER-id _
   ; homomorphism = SF→ER-∘ _ _
   ; F-resp-≈ = λ { (x , y) → (SF→ER-≤ x) , (SF→ER-≤ y)}
   }

ER→SF-Func : Functor ER-Cat SF-Cat
ER→SF-Func = record
   { F₀ = λ X → X
   ; F₁ = ER→SF
   ; identity = ER→SF-id _
   ; homomorphism = ER→SF-∘ _ _
   ; F-resp-≈ = λ {(x , y) → (ER→SF-≤ x) , (ER→SF-≤ y)}
   }

SF≡ER : StrongEquivalence SF-Cat ER-Cat
SF≡ER = record
  { F = SF→ER-Func
  ; G = ER→SF-Func
  ; weak-inverse = record
    { F∘G≈id = niHelper (record
      { η = λ X → ER-id X
      ; η⁻¹ =  λ X → ER-id X
      ; commute = λ f → (λ { x y (.y , ((.y , k) , refl) , refl) → x , (refl , k)}) ,
                        (λ { x y (.x , refl , k) → y , (((y , k) , refl) , refl)})
      ; iso = λ X → record
         { isoˡ = (λ { x x (.x , refl , refl) → refl}) , λ {x .x refl → x , (refl , refl)}
         ; isoʳ = (λ { x .x (.x , refl , refl) → refl}) , λ { x .x refl → x , (refl , refl)}
         }
      })
    ; G∘F≈id = niHelper (record
      { η = λ X → SF-id X
      ; η⁻¹ = λ X → SF-id X
      ; commute = λ f → (λ { x ((y , i , rel) , tt) → (tt , i) , sym rel}) ,
                λ { x (tt , i) → (((proj₂ (f x) i) , (i , refl)) , tt) , refl}
      ; iso = λ X → record
        { isoˡ = (λ x i → tt , refl) , (λ x i → (tt , tt) , refl)
        ; isoʳ = (λ x i → tt , refl) , (λ x i → (tt , tt) , refl)
        }
      })
    }
  }



