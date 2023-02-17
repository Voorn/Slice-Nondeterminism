module Small-Slice.Setoid where

-- Agda standard library
open import Data.Unit
open import Data.Empty
open import Data.Sum renaming (map to map⊎)
open import Data.Product renaming (map to map×)
open import Level
open import Relation.Binary.Bundles
open import Relation.Binary.Structures
open import Function.Equality

-- Categories library
open import Categories.Category.Instance.Setoids
open import Categories.Functor

-- Development library
open import Small-Slice.Univ


Pow₀ : Setoid zero zero → Setoid zero zero
Pow₀ record { Carrier = X ; _≈_ = R ; isEquivalence = Requiv } = record
  { Carrier = 𝕌SL X
  ; _≈_ = 𝕌Rel R
  ; isEquivalence = 𝕌Rel-equiv R Requiv
  }


Pow : Functor (Setoids zero zero) (Setoids zero zero)
Pow = record
   { F₀ = Pow₀
   ; F₁ = λ {A} {B} → λ { record { _⟨$⟩_ = f ; cong = cong } → record
     { _⟨$⟩_ = 𝕌SL-fun f
     ; cong = 𝕌SL-fun-cong (Setoid._≈_ A) (Setoid._≈_ B) f cong
     }}
   ; identity = λ x → x
   ; homomorphism = λ {A} {B} {C} {f} {g} → λ {(a<b , b<a) →
       (λ i → (proj₁ (a<b i)) , cong g (cong f (proj₂ (a<b i)))) ,
        λ i → (proj₁ (b<a i)) , (cong g (cong f (proj₂ (b<a i))))}
   ; F-resp-≈ = λ {A} {B} {f} {g} →
     λ {f≈g (a<b , b<a) → (λ i → (proj₁ (a<b i)) , f≈g (proj₂ (a<b i))) ,
     λ i → (proj₁ (b<a i)) ,
         IsEquivalence.sym (Setoid.isEquivalence (A ⇨ B)) {f} {g} f≈g (proj₂ (b<a i))}
   }


open import Categories.Monad
open import Categories.NaturalTransformation

Pow-η : NaturalTransformation Categories.Functor.id Pow
Pow-η = ntHelper (record
  { η = λ {record { Carrier = A ; _≈_ = R ; isEquivalence = Requiv } → record
    { _⟨$⟩_ = 𝕌SL-η 
    ; cong = λ {x} {y} xRy → (λ i → tt , xRy) ,
             (λ i → tt , IsEquivalence.sym Requiv {x} {y} xRy)
    }}
  ; commute = λ {A} {B} → λ {record { _⟨$⟩_ = _⟨$⟩_ ; cong = cong } x≈y →
       (λ i → tt , (cong x≈y)) , (λ i → tt , IsEquivalence.sym (Setoid.isEquivalence B) (cong x≈y))}
  })

Pow-μ : NaturalTransformation (Pow ∘F Pow) Pow
Pow-μ = ntHelper (record
  { η = λ {record { Carrier = A ; _≈_ = R ; isEquivalence = Requiv } → record
    { _⟨$⟩_ = 𝕌SL-μ
    ; cong = λ { {d} {e} (dΓΓRe , eΓΓRd) →
           (λ { (i , j) → (proj₁ (dΓΓRe i) , proj₁ (proj₁ (proj₂ (dΓΓRe i)) j)) , proj₂ (proj₁ (proj₂ (dΓΓRe i)) j)}) ,
            λ { (i , j) → (proj₁ (eΓΓRd i) , proj₁ (proj₁ (proj₂ (eΓΓRd i)) j)) , proj₂ (proj₁ (proj₂ (eΓΓRd i)) j)}}
    }}
  ; commute = λ {A} {B} → λ {record { _⟨$⟩_ = _⟨$⟩_ ; cong = cong } {d} {e} (dΓΓe , eΓΓd) →
            (λ { (i , j) → (proj₁ (dΓΓe i) , proj₁ (proj₁ (proj₂ (dΓΓe i)) j)) , cong (proj₂ (proj₁ (proj₂ (dΓΓe i)) j))}) ,
             λ { (i , j) → (proj₁ (eΓΓd i) , proj₁ (proj₁ (proj₂ (eΓΓd i)) j)) , cong (proj₂ (proj₁ (proj₂ (eΓΓd i)) j))}}
  })

Pow-Monad : Monad (Setoids zero zero)
Pow-Monad = record
   { F = Pow
   ; η = Pow-η
   ; μ = Pow-μ
   ; assoc = 
     λ {(aΓb , bΓa) → (λ {(i , j , k) → ((proj₁ (aΓb i) , proj₁ (proj₁ (proj₂ (aΓb i)) j)) ,
                      proj₁ (proj₁ (proj₂ (proj₁ (proj₂ (aΓb i)) j)) k)) , proj₂ (proj₁ (proj₂ (proj₁ (proj₂ (aΓb i)) j)) k)}) ,
                       λ { ((i , j) , k) → (proj₁ (bΓa i) , (proj₁ (proj₁ (proj₂ (bΓa i)) j)) ,
                      (proj₁ (proj₁ (proj₂ (proj₁ (proj₂ (bΓa i)) j)) k))) , proj₂ (proj₁ (proj₂ (proj₁ (proj₂ (bΓa i)) j)) k)}}
   ; sym-assoc =  λ {(aΓb , bΓa) → (λ {((i , j) , k) → (proj₁ (aΓb i) , proj₁ (proj₁ (proj₂ (aΓb i)) j) ,
                      proj₁ (proj₁ (proj₂ (proj₁ (proj₂ (aΓb i)) j)) k)) , proj₂ (proj₁ (proj₂ (proj₁ (proj₂ (aΓb i)) j)) k)}) ,
                       λ { (i , j , k) → ((proj₁ (bΓa i) , (proj₁ (proj₁ (proj₂ (bΓa i)) j))) ,
                      (proj₁ (proj₁ (proj₂ (proj₁ (proj₂ (bΓa i)) j)) k))) , proj₂ (proj₁ (proj₂ (proj₁ (proj₂ (bΓa i)) j)) k)}}
   ; identityˡ = λ {(aΓb , bΓa) → (λ {(i , tt) → proj₁ (aΓb i) , proj₂ (aΓb i)}) , λ i → (proj₁ (bΓa i) , tt) , proj₂ (bΓa i) }
   ; identityʳ = λ {(aΓb , bΓa) → (λ {(tt , i) → proj₁ (aΓb i) , proj₂ (aΓb i)}) , λ i → (tt , proj₁ (bΓa i)) , proj₂ (bΓa i)}
   }
