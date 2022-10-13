module Small-Slice.Marbles where

open import Data.Unit
open import Data.Empty
open import Data.Sum renaming (map to map⊎)
open import Data.Nat hiding (_⊔_)
open import Data.Product renaming (map to map×)
open import Relation.Binary.PropositionalEquality hiding ([_])

open import Small-Slice.Univ


data 𝕃 (X : Set) : Set where
  end : 𝕃 X
  app : X → 𝕃 X → 𝕃 X 


𝕃-conc : {X : Set} → 𝕃 X → 𝕃 X → 𝕃 X
𝕃-conc end b = b
𝕃-conc (app x a) b = app x (𝕃-conc a b)


𝕃-μ : (X : Set) → 𝕌Hom ((𝕃 X) × (𝕃 X)) (𝕃 X)
𝕃-μ X (a , b) = 𝕌SL-η (𝕃-conc a b)


𝕃-δ : (X : Set) → 𝕌Hom (𝕃 X) ((𝕃 X) × (𝕃 X))
proj₁ (𝕃-δ X end) = 𝕌⊤
proj₁ (𝕃-δ X (app x a)) = 𝕌⊎ 𝕌⊤ (proj₁ (𝕃-δ X a))
proj₂ (𝕃-δ X end) tt = end , end
proj₂ (𝕃-δ X (app x a)) (inj₁ tt) = end , (app x a)
proj₂ (𝕃-δ X (app x a)) (inj₂ i) with proj₂ (𝕃-δ X a) i
... | a' , b' = (app x a') , b'


𝕃-δμ⊂id : (X : Set) → 𝕌Hom-⊂ (𝕌Hom-∘ (𝕃-δ X) (𝕃-μ X)) (𝕌Hom-id (𝕃 X))
𝕃-δμ⊂id X end = (λ i → tt) , (λ i → refl)
𝕃-δμ⊂id X (app x a) = (λ i → tt) , (λ {(inj₁ tt , tt) → refl ;
          (inj₂ i , tt) → cong (app x) (proj₂ (𝕃-δμ⊂id X a) (i , tt) )})

𝕃-id⊂δμ : (X : Set) → 𝕌Hom-⊂ (𝕌Hom-id (𝕃 X)) (𝕌Hom-∘ (𝕃-δ X) (𝕃-μ X))
𝕃-id⊂δμ X end = (λ i → tt , tt) , (λ i → refl)
𝕃-id⊂δμ X (app x a) = (λ i → inj₁ tt , tt) , λ i → refl


𝕃-id⊂μδ : (X : Set) → 𝕌Hom-⊂ (𝕌Hom-id ((𝕃 X) × (𝕃 X))) (𝕌Hom-∘ (𝕃-μ X) (𝕃-δ X))
𝕃-id⊂μδ X (end , end) = (λ i → tt , tt) , λ i → refl
𝕃-id⊂μδ X (end , app y b) = (λ i → tt , inj₁ tt) , λ i → refl
𝕃-id⊂μδ X (app x a , b) with 𝕃-id⊂μδ X (a , b)
... | f , k = (λ i → tt , (inj₂ (proj₂ (f tt)))) ,
    λ i → cong (λ u → app x (proj₁ u) , (proj₂ u)) (k tt)




𝕃-η : (X : Set) → 𝕌Hom ⊤ (𝕃 X)
𝕃-η X tt = 𝕌SL-η end


𝕃-ε : (X : Set) → 𝕌Hom (𝕃 X) ⊤
𝕃-ε X end = 𝕌⊤ , (λ i → tt)
𝕃-ε X (app x a) = 𝕌⊥ , (λ {()})


𝕃-id⊂ηε : (X : Set) → 𝕌Hom-⊂ (𝕌Hom-id ⊤) (𝕌Hom-∘ (𝕃-η X) (𝕃-ε X))
𝕃-id⊂ηε X tt = (λ i → tt , tt) , λ i → refl


𝕃-ηε⊂id : (X : Set) → 𝕌Hom-⊂ (𝕌Hom-∘ (𝕃-η X) (𝕃-ε X)) (𝕌Hom-id ⊤)
𝕃-ηε⊂id X tt = (λ i → tt) , λ i → refl


𝕃-εη⊂id : (X : Set) → 𝕌Hom-⊂ (𝕌Hom-∘ (𝕃-ε X) (𝕃-η X)) (𝕌Hom-id (𝕃 X))
𝕃-εη⊂id X end = (λ i → tt) , λ i → refl
𝕃-εη⊂id X (app x a) = (λ i → tt) , λ {()}
