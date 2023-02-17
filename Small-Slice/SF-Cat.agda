module Small-Slice.SF-Cat where

open import Data.Unit
open import Data.Empty
open import Data.Sum renaming (map to map⊎)
open import Data.Nat hiding (_⊔_)
open import Data.Product renaming (map to map×)
open import Relation.Binary.PropositionalEquality hiding ([_])

open import Categories.Category

open import Small-Slice.Univ
open import Small-Slice.ND-functions


SSF-Cat : Category _ _ _
SSF-Cat = record
   { Obj = Set
   ; _⇒_ = 𝕌Hom
   ; _≈_ = 𝕌Hom-≡
   ; id = 𝕌Hom-id _
   ; _∘_ = 𝕌Hom-∘
   ; assoc = λ {_ _ _ _ f g h} → 𝕌Hom-asso f g h
   ; sym-assoc = λ {_ _ _ _ f g h} → 𝕌Hom-sym-asso f g h 
   ; identityˡ = 𝕌Hom-lid _
   ; identityʳ = 𝕌Hom-rid _
   ; identity² = 𝕌Hom-did
   ; equiv = 𝕌Hom-≡-equiv
   ; ∘-resp-≈ = λ f≡f' g≡g' → 𝕌Hom-∘≡ g≡g' f≡f'
   }


open import Small-Slice.Monoidal

open import Categories.Functor.Bifunctor

⊗-Bifunctor : Bifunctor SSF-Cat SSF-Cat SSF-Cat
⊗-Bifunctor = record
  { F₀ = λ {(A , B) → A × B}
  ; F₁ = 𝕌Hom-⊗
  ; identity = 𝕌Hom-⊗-id
  ; homomorphism = λ {A} {B} {C} {f} {g} → 𝕌Hom-⊗-∘ {A} {B} {C} {f} {g}
  ; F-resp-≈ = 𝕌Hom-⊗-≡
  }

open import Categories.Morphism
open import Categories.Category.Monoidal

⊗-left-unitor : {X : Set} → (SSF-Cat ≅ (⊤ × X)) X
⊗-left-unitor = record
  { from = 𝕌Hom-⊗-luni
  ; to = 𝕌Hom-⊗-luni-rev
  ; iso = record
    { isoˡ = 𝕌Hom-⊗-luni-liso
    ; isoʳ = 𝕌Hom-⊗-luni-riso
    }
  }

⊗-right-unitor : {X : Set} → (SSF-Cat ≅ (X × ⊤)) X
⊗-right-unitor = record
  { from = 𝕌Hom-⊗-runi
  ; to = 𝕌Hom-⊗-runi-rev
  ; iso = record
    { isoˡ = 𝕌Hom-⊗-runi-liso
    ; isoʳ = 𝕌Hom-⊗-runi-riso
    }
  }

⊗-associator : {X Y Z : Set} → (SSF-Cat ≅ ((X × Y) × Z)) (X × (Y × Z))
⊗-associator = record
  { from = 𝕌Hom-⊗-asso
  ; to = 𝕌Hom-⊗-asso-rev
  ; iso = record
    { isoˡ = (λ x i → tt , refl) , (λ x i → (tt , tt) , refl)
    ; isoʳ = (λ x i → tt , refl) , (λ x i → (tt , tt) , refl)
    }
  }

-- Note: most extra proofs are just inherited from monoidal structure on set.
⊗-Monoidal : Monoidal SSF-Cat
⊗-Monoidal = record
  { ⊗ = ⊗-Bifunctor
  ; unit = ⊤
  ; unitorˡ = ⊗-left-unitor
  ; unitorʳ = ⊗-right-unitor
  ; associator = ⊗-associator
  ; unitorˡ-commute-from =
    (λ x i → (tt , proj₂ (proj₁ i)) , refl ) , λ x i → ((tt , (proj₂ i)) , tt) , refl
  ; unitorˡ-commute-to =
    (λ x i → (tt , (tt , (proj₁ i))) , refl) , (λ x i → (proj₂ (proj₂ i) , tt) , refl)
  ; unitorʳ-commute-from =
    (λ x i → (tt , (proj₁ (proj₁ i))) , refl) , (λ x i → (((proj₂ i) , tt) , tt) , refl)
  ; unitorʳ-commute-to =
    (λ x i → (tt , ((proj₁ i) , tt)) , refl) , (λ x i → (proj₁ (proj₂ i) , tt) , refl)
  ; assoc-commute-from =
    (λ {x (((i , j) , k) , tt) → (tt , i , j , k) , refl}) ,
    λ {x (tt , i , j , k) → (((i , j) , k) , tt) , refl} 
  ; assoc-commute-to =
    (λ { x ((i , j , k) , tt) → (tt , ((i , j) , k)) , refl}) ,
    λ {x ((tt , (i , j) , k)) → ((i , j , k) , tt) , refl}
  ; triangle =
    (λ x i → (tt , tt) , refl) , (λ x i → (tt , (tt , tt)) , refl)
  ; pentagon = (λ x i → (tt , tt) , refl) , (λ x i → (((tt , tt) , tt) , (tt , tt)) , refl)
  }

open import Categories.NaturalTransformation.NaturalIsomorphism hiding (refl)
open import Categories.Category.Monoidal.Braided

⊗-braided : Braided ⊗-Monoidal
⊗-braided = record
  { braiding = niHelper (record
    { η = λ {XY (x , y) → 𝕌SL-η (y , x)}
    ; η⁻¹ = λ {XY (y , x) → 𝕌SL-η (x , y)}
    ; commute = λ f → (λ x i → (tt , ((proj₂ (proj₁ i)) , (proj₁ (proj₁ i)))) , refl) ,
              (λ x i → (((proj₂ (proj₂ i)) , (proj₁ (proj₂ i))) , tt) , refl)
    ; iso = λ X → record { isoˡ = (λ x i → tt , refl) , (λ x i → (tt , tt) , refl)
                         ; isoʳ = (λ x i → tt , refl) , (λ x i → (tt , tt) , refl) }
    })
  ; hexagon₁ = (λ x i → ((tt , tt) , tt) , refl) ,
               (λ x i → (((tt , tt) , tt) , (tt , tt)) , refl)
  ; hexagon₂ = (λ x i → (tt , (tt , tt)) , refl) ,
               (λ x i → ((tt , tt) , (tt , (tt , tt))) , refl)
  }


⊎-left-unitor : {X : Set} → (SSF-Cat ≅ (⊥ ⊎ X)) X
⊎-left-unitor = record
  { from = 𝕌Hom-⊎-luni
  ; to = 𝕌Hom-⊎-luni-rev
  ; iso = record
    { isoˡ = (λ {(inj₂ x) i → tt , refl}) , λ {(inj₂ x) i → (tt , tt) , refl}
    ; isoʳ = (λ x i → tt , refl) , (λ x i → (tt , tt) , refl)
    }
  }

⊎-right-unitor : {X : Set} → (SSF-Cat ≅ (X ⊎ ⊥)) X
⊎-right-unitor = record
  { from = 𝕌Hom-⊎-runi
  ; to = 𝕌Hom-⊎-runi-rev
  ; iso = record
    { isoˡ = (λ {(inj₁ x) i → tt , refl}) , λ {(inj₁ x) i → (tt , tt) , refl}
    ; isoʳ = (λ x i → tt , refl) , (λ x i → (tt , tt) , refl)
    }
  }

⊎-associator : {X Y Z : Set} → (SSF-Cat ≅ ((X ⊎ Y) ⊎ Z)) (X ⊎ (Y ⊎ Z))
⊎-associator = record
  { from = 𝕌Hom-⊎-asso
  ; to = 𝕌Hom-⊎-asso-rev
  ; iso = record
    { isoˡ = (λ { (inj₁ (inj₁ x)) i → tt , refl ;
                  (inj₁ (inj₂ y)) i → tt , refl ;
                  (inj₂ y) i → tt , refl}) ,
              λ { (inj₁ (inj₁ x)) i → (tt , tt) , refl ;
                  (inj₁ (inj₂ y)) i → (tt , tt) , refl ;
                  (inj₂ y) i → (tt , tt) , refl}
    ; isoʳ = (λ { (inj₁ x) i → tt , refl ;
                  (inj₂ (inj₁ x)) i → tt , refl ;
                  (inj₂ (inj₂ y)) i → tt , refl}) ,
              λ { (inj₁ x) i → (tt , tt) , refl ;
                  (inj₂ (inj₁ x)) i → (tt , tt) , refl ;
                  (inj₂ (inj₂ y)) i → (tt , tt) , refl}
    }
  }


⊎-Bifunctor : Bifunctor SSF-Cat SSF-Cat SSF-Cat
⊎-Bifunctor = record
  { F₀ = λ {(A , B) → A ⊎ B}
  ; F₁ = 𝕌Hom-⊎
  ; identity = 𝕌Hom-⊎-id _ _
  ; homomorphism = 𝕌Hom-⊎-∘ _ _
  ; F-resp-≈ = 𝕌Hom-⊎-≡ _ _
  }

⊎-Monoidal : Monoidal SSF-Cat
⊎-Monoidal = monoidalHelper SSF-Cat (record
  { ⊗ = ⊎-Bifunctor
  ; unit = ⊥
  ; unitorˡ = ⊎-left-unitor
  ; unitorʳ = ⊎-right-unitor
  ; associator = ⊎-associator
  ; unitorˡ-commute = (λ {(inj₂ y) (i , tt) → (tt , i) , refl}) ,
                       λ {(inj₂ y) (tt , i) → (i , tt) , refl}
  ; unitorʳ-commute = (λ {(inj₁ y) (i , tt) → (tt , i) , refl}) ,
                       λ {(inj₁ y) (tt , i) → (i , tt) , refl}
  ; assoc-commute = (λ {(inj₁ (inj₁ x)) i → (tt , (proj₁ i)) , refl ;
                        (inj₁ (inj₂ y)) i → (tt , (proj₁ i)) , refl ;
                        (inj₂ y) i → (tt , (proj₁ i)) , refl}) ,
                     λ {(inj₁ (inj₁ x)) i → ((proj₂ i) , tt) , refl ;
                        (inj₁ (inj₂ y)) i → ((proj₂ i) , tt) , refl ;
                        (inj₂ y) i → ((proj₂ i) , tt) , refl}
  ; triangle = (λ {(inj₁ (inj₁ x)) i → tt , refl ; (inj₂ y) i → tt , refl}) ,
                λ {(inj₁ (inj₁ x)) i → (tt , tt) , refl ; (inj₂ y) i → (tt , tt) , refl}
  ; pentagon = (λ {(inj₁ (inj₁ (inj₁ x))) i → (tt , tt) , refl ;
                   (inj₁ (inj₁ (inj₂ y))) i → (tt , tt) , refl ;
                   (inj₁ (inj₂ z)) i → (tt , tt) , refl ;
                   (inj₂ w) i → (tt , tt) , refl}) ,
                λ {(inj₁ (inj₁ (inj₁ x))) i → ((tt , tt) , tt) , refl ;
                   (inj₁ (inj₁ (inj₂ y))) i → ((tt , tt) , tt) , refl ;
                   (inj₁ (inj₂ z)) i → ((tt , tt) , tt) , refl ;
                   (inj₂ w) i → ((tt , tt) , tt) , refl}
  })

open import Small-Slice.Cartesian

open import Categories.Object.Terminal

SSF-Terminal : Terminal SSF-Cat
SSF-Terminal = record
  { ⊤ = ⊥
  ; ⊤-is-terminal = record
    { ! = 𝕌-termin
    ; !-unique = 𝕌-termin-unique
    }
  }

open import Categories.Object.Initial

SSF-Initial : Initial SSF-Cat
SSF-Initial = record
  { ⊥ = ⊥
  ; ⊥-is-initial = record
    { ! = 𝕌-initia
    ; !-unique = 𝕌-initia-unique
    }
  }


open import Categories.Category.BinaryProducts

SSF-Product : BinaryProducts SSF-Cat
SSF-Product = record
  { product = λ {A} {B} → record
    { A×B = A ⊎ B
    ; π₁ = 𝕌-prod-proj₁
    ; π₂ = 𝕌-prod-proj₂
    ; ⟨_,_⟩ = 𝕌-prod-glue
    ; project₁ = 𝕌-prod-glue-proj₁ 
    ; project₂ = 𝕌-prod-glue-proj₂
    ; unique = 𝕌-prod-glue-unique _
    }
  }


open import Categories.Category.Cocartesian

SSF-Coproduct : BinaryCoproducts SSF-Cat
SSF-Coproduct = record { coproduct = λ {A} {B} → record
  { A+B = A ⊎ B
  ; i₁ = 𝕌-copr-inj₁
  ; i₂ = 𝕌-copr-inj₂
  ; [_,_] = 𝕌-copr-glue
  ; inject₁ = λ {_} {f} {g} → 𝕌-copr-glue-inj₁ {_} {_} {_} {f} {g}
  ; inject₂ = λ {_} {f} {g} → 𝕌-copr-glue-inj₂ {_} {_} {_} {f} {g}
  ; unique = 𝕌-copr-glue-unique _
  }}


open import Categories.Category.Cartesian

SSF-Cartesian : Cartesian SSF-Cat
SSF-Cartesian = record
  { terminal = SSF-Terminal
  ; products = SSF-Product
  }


SSF-Cocartesian : Cocartesian SSF-Cat
SSF-Cocartesian = record
  { initial = SSF-Initial
  ; coproducts = SSF-Coproduct }

