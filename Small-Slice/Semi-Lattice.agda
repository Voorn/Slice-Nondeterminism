module Small-Slice.Semi-Lattice where

open import Data.Unit
open import Data.Empty
open import Data.Sum renaming (map to map⊎)
open import Data.Nat hiding (_⊔_)
open import Data.Product renaming (map to map×)

open import Relation.Binary.PropositionalEquality hiding ([_])
 
open import Small-Slice.Univ
open import Small-Slice.ND-functions




𝕌SL-∨ : {X : Set} → 𝕌SL X → 𝕌SL X → 𝕌SL X
𝕌SL-∨ (I , f) (J , g) = (𝕌⊎ I J) , (λ {(inj₁ i) → f i ; (inj₂ j) → g j})

𝕌SL-ℕ : {X : Set} → (X → 𝕌SL X) → ℕ → X → 𝕌SL X
𝕌SL-ℕ f zero x = 𝕌⊤ , λ i → x
𝕌SL-ℕ f (suc n) x = (𝕌Σ (proj₁ (f x) , λ i → proj₁ (𝕌SL-ℕ f n (proj₂ (f x) i)))) ,
  λ {(i , j) → proj₂ (𝕌SL-ℕ f n (proj₂ (f x) i)) j}

𝕌SL-ω : {X : Set} → (X → 𝕌SL X) → (X → 𝕌SL X)
𝕌SL-ω f x = (𝕌Σ (𝕌ℕ , (λ n → proj₁ (𝕌SL-ℕ f n x)))) , λ {(n , i) → proj₂ (𝕌SL-ℕ f n x) i}


-- Monoid
𝕌SL-∨-⊂ : {X : Set} → {a₀ a₁ b₀ b₁ : 𝕌SL X} → (𝕌SL→ X a₀ a₁) → (𝕌SL→ X b₀ b₁)
  → (𝕌SL→ X (𝕌SL-∨ a₀ b₀) (𝕌SL-∨ a₁ b₁))
𝕌SL-∨-⊂ a⊂ b⊂ (inj₁ i) = (inj₁ (proj₁ (a⊂ i))) , proj₂ (a⊂ i)
𝕌SL-∨-⊂ a⊂ b⊂ (inj₂ j) = (inj₂ (proj₁ (b⊂ j))) , proj₂ (b⊂ j)

𝕌SL-∨-luni : {X : Set} → (a : 𝕌SL X) → 𝕌SL→ X (𝕌SL-∨ 𝕌SL-⊥ a) a
𝕌SL-∨-luni a (inj₂ i) = i , refl

𝕌SL-∨-runi : {X : Set} → (a : 𝕌SL X) → 𝕌SL→ X (𝕌SL-∨ a 𝕌SL-⊥) a
𝕌SL-∨-runi a (inj₁ i) = i , refl

𝕌SL-∨-left : {X : Set} → (a b : 𝕌SL X) → 𝕌SL→ X a (𝕌SL-∨ a b)
𝕌SL-∨-left a b i = (inj₁ i) , refl

𝕌SL-∨-right : {X : Set} → (a b : 𝕌SL X) → 𝕌SL→ X b (𝕌SL-∨ a b)
𝕌SL-∨-right a b i = (inj₂ i) , refl

𝕌SL-∨-idem : {X : Set} → (a : 𝕌SL X) → 𝕌SL→ X (𝕌SL-∨ a a) a
𝕌SL-∨-idem a (inj₁ i) = i , refl
𝕌SL-∨-idem a (inj₂ i) = i , refl

𝕌SL-∨-comm : {X : Set} → (a b : 𝕌SL X) → 𝕌SL→ X (𝕌SL-∨ a b) (𝕌SL-∨ b a)
𝕌SL-∨-comm a b (inj₁ i) = inj₂ i , refl
𝕌SL-∨-comm a b (inj₂ j) = inj₁ j , refl

𝕌SL-∨-asso : {X : Set} → (a b c : 𝕌SL X)
  → 𝕌SL→ X (𝕌SL-∨ (𝕌SL-∨ a b) c) (𝕌SL-∨ a (𝕌SL-∨ b c))
𝕌SL-∨-asso a b c (inj₁ (inj₁ i)) = (inj₁ i) , refl
𝕌SL-∨-asso a b c (inj₁ (inj₂ j)) = inj₂ (inj₁ j) , refl
𝕌SL-∨-asso a b c (inj₂ k) = inj₂ (inj₂ k) , refl

𝕌SL-∨-asso' : {X : Set} → (a b c : 𝕌SL X)
  → 𝕌SL→ X (𝕌SL-∨ a (𝕌SL-∨ b c)) (𝕌SL-∨ (𝕌SL-∨ a b) c)
𝕌SL-∨-asso' a b c (inj₁ i) = (inj₁ (inj₁ i)) , refl
𝕌SL-∨-asso' a b c (inj₂ (inj₁ j)) = (inj₁ (inj₂ j)), refl
𝕌SL-∨-asso' a b c (inj₂ (inj₂ k)) = (inj₂ k) , refl


𝕌SL-∨-supremum : {X : Set} → (a b c : 𝕌SL X)
  → (𝕌SL→ X a c) → (𝕌SL→ X b c) → (𝕌SL→ X (𝕌SL-∨ a b) c)
𝕌SL-∨-supremum a b c a⊂c b⊂c (inj₁ i) = a⊂c i
𝕌SL-∨-supremum a b c a⊂c b⊂c (inj₂ j) = b⊂c j


-- powertheory axioms
𝕌SL-∨-idem≡ : {X : Set} → (a : 𝕌SL X) → 𝕌SL≡ (𝕌SL-∨ a a) a
𝕌SL-∨-idem≡ (I , a) =
  𝕌SL-∨-idem (I , a) ,
  (λ i → (inj₁ i) , refl)

𝕌SL-∨-comm≡ : {X : Set} → (a b : 𝕌SL X) → 𝕌SL≡ (𝕌SL-∨ a b) (𝕌SL-∨ b a)
𝕌SL-∨-comm≡ a b = 𝕌SL-∨-comm a b , 𝕌SL-∨-comm b a 

𝕌SL-∨-asso≡ : {X : Set} → (a b c : 𝕌SL X)
  → 𝕌SL≡ (𝕌SL-∨ (𝕌SL-∨ a b) c) (𝕌SL-∨ a (𝕌SL-∨ b c))
𝕌SL-∨-asso≡ a b c = 𝕌SL-∨-asso a b c , 𝕌SL-∨-asso' a b c

𝕌SL-∨-lower : {X : Set} → (a b : 𝕌SL X) → 𝕌SL→ _ a (𝕌SL-∨ a b)
𝕌SL-∨-lower a b = 𝕌SL-∨-left a b



-- Enriched by structure
𝕌Hom-⊥ : {X Y : Set} → 𝕌Hom X Y
𝕌Hom-⊥ x = 𝕌SL-⊥

𝕌Hom-∨ : {X Y : Set} → (f f' : 𝕌Hom X Y) → 𝕌Hom X Y
𝕌Hom-∨ f f' x = 𝕌SL-∨ (f x) (f' x)


𝕌Hom-∨-left : {X Y : Set} → (f f' : 𝕌Hom X Y) → 𝕌Hom-⊂ f (𝕌Hom-∨ f f')
𝕌Hom-∨-left f f' x = 𝕌SL-∨-left (f x) (f' x)

𝕌Hom-∨-right : {X Y : Set} → (f f' : 𝕌Hom X Y) → 𝕌Hom-⊂ f' (𝕌Hom-∨ f f')
𝕌Hom-∨-right f f' x = 𝕌SL-∨-right (f x) (f' x)

𝕌Hom-∨-supremum : {X Y : Set} → (f f' g : 𝕌Hom X Y)
  → (𝕌Hom-⊂ f g) → (𝕌Hom-⊂ f' g) → (𝕌Hom-⊂ (𝕌Hom-∨ f f') g)
𝕌Hom-∨-supremum f f' g p q x = 𝕌SL-∨-supremum (f x) (f' x) (g x) (p x) (q x)


