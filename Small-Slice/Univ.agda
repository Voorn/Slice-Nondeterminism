module Small-Slice.Univ where

open import Data.Unit
open import Data.Empty
open import Data.Sum renaming (map to map⊎)
open import Data.Nat hiding (_⊔_)
open import Data.Product renaming (map to map×)
open import Relation.Binary.Core

open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Binary.Structures
open import Relation.Binary.Definitions


-- Simultaneous definition of universes as names and their corresponding sets
data 𝕌 : Set
𝕌S : 𝕌 → Set

data 𝕌 where
  𝕌⊥ : 𝕌
  𝕌⊤ : 𝕌
  𝕌ℕ : 𝕌
  𝕌→ : 𝕌 → 𝕌 → 𝕌
  𝕌⊎ : 𝕌 → 𝕌 → 𝕌
  𝕌× : 𝕌 → 𝕌 → 𝕌
  𝕌Σ : (Σ 𝕌 λ S → 𝕌S S → 𝕌) → 𝕌
  𝕌Π : (Σ 𝕌 λ S → 𝕌S S → 𝕌) → 𝕌

𝕌S 𝕌⊥ = ⊥
𝕌S 𝕌⊤ = ⊤
𝕌S 𝕌ℕ = ℕ
𝕌S (𝕌→ t t₁) = 𝕌S t → 𝕌S t₁
𝕌S (𝕌⊎ t t₁) = 𝕌S t ⊎ 𝕌S t₁
𝕌S (𝕌× t t₁) = 𝕌S t × 𝕌S t₁
𝕌S (𝕌Σ (I , A)) = Σ (𝕌S I) (λ i → 𝕌S (A i))
𝕌S (𝕌Π (I , A)) = (i : 𝕌S I) → 𝕌S (A i)



-- Main use: slices using 𝕌 don't go up a universe level
𝕌SL : Set → Set
𝕌SL X = Σ 𝕌 (λ S → 𝕌S S → X)

𝕌Γ : {X Y : Set} → (R : X → Y → Set) → (𝕌SL X → 𝕌SL Y → Set)
𝕌Γ R (I , f) (J , g) = (i : 𝕌S I) → Σ (𝕌S J) (λ j → R (f i) (g j))

𝕌SL→ : (X : Set) → 𝕌SL X → 𝕌SL X → Set
𝕌SL→ X = 𝕌Γ {X} {X} _≡_

𝕌SL≡ : {X : Set} → 𝕌SL X → 𝕌SL X → Set
𝕌SL≡ a b = 𝕌SL→ _ a b × 𝕌SL→ _ b a

-- as powerset
𝕌SL-∈ : {X : Set} → X → 𝕌SL X → Set
𝕌SL-∈ x (I , a) = Σ (𝕌S I) λ i → a i ≡ x

𝕌SL-⊂ : {X : Set} → 𝕌SL X → 𝕌SL X → Set
𝕌SL-⊂ {X} U V = (x : X) → 𝕌SL-∈ x U → 𝕌SL-∈ x V

𝕌SL-⊂⇒map : {X : Set} → (U V : 𝕌SL X) → 𝕌SL-⊂ U V → 𝕌SL→ X U V 
𝕌SL-⊂⇒map (I , a) (J , b) U⊂V i with U⊂V (a i) (i , refl)
...| (j , eq) = j , sym eq

𝕌SL-map⇒⊂ : {X : Set} → (U V : 𝕌SL X) → 𝕌SL→ X U V → 𝕌SL-⊂ U V 
𝕌SL-map⇒⊂ (I , a) (J , b) U→V x (i , eq) with U→V i
...| (j , eq') = j , (trans (sym eq') eq)

-- Relator properties
𝕌Γ-refl : {X : Set} → (R : REL X X _ ) → Reflexive R → Reflexive (𝕌Γ R)
𝕌Γ-refl R Rrefl {I , a} i = i , (Rrefl {a i})

𝕌Γ-tran : {X : Set} → (R : REL X X _) → Transitive R → Transitive (𝕌Γ R) 
𝕌Γ-tran R Rtran {I , a} {J , b} {K , c} aRb bRc i = (proj₁ (bRc (proj₁ (aRb i)))) ,
  Rtran (proj₂ (aRb i)) (proj₂ (bRc (proj₁ (aRb i))))

𝕌Γ-⊂ : {X Y : Set} → {R S : REL X Y _} → R ⇒ S → 𝕌Γ R ⇒ 𝕌Γ S
𝕌Γ-⊂ R⊂S a<b i = (proj₁ (a<b i)) , (R⊂S (proj₂ (a<b i)))




-- Setoid
𝕌Rel : {X : Set} → (R : Rel X _) → (Rel (𝕌SL X) _) 
𝕌Rel R a b = 𝕌Γ R a b × 𝕌Γ R b a

𝕌Rel-refl : {X : Set} → (R : Rel X _) → Reflexive R → Reflexive (𝕌Rel R)
𝕌Rel-refl R Rrefl = (𝕌Γ-refl R Rrefl) , 𝕌Γ-refl R Rrefl

𝕌Rel-tran : {X : Set} → (R : Rel X _) → Transitive R → Transitive (𝕌Rel R)
𝕌Rel-tran R Rtran (a<b , b<a) (b<c , c<b) =
  𝕌Γ-tran R Rtran a<b b<c , 𝕌Γ-tran R Rtran c<b b<a

𝕌Rel-⊂ : {X : Set} → {R S : Rel X _} → (R ⇒ S) → 𝕌Rel R ⇒ 𝕌Rel S
𝕌Rel-⊂ {X} {R} {S} R⊂S (a<b , b<a) =
  𝕌Γ-⊂ {X} {X} {R} {S} R⊂S a<b , 𝕌Γ-⊂ {X} {X} {R} {S} R⊂S b<a

𝕌Rel-symm : {X : Set} → (R : Rel X _) → Symmetric R → Symmetric (𝕌Rel R)
𝕌Rel-symm R Rsymm (a<b , b<a) = b<a , a<b

𝕌Rel-equiv : {X : Set} → (R : Rel X _) → IsEquivalence R → IsEquivalence (𝕌Rel R)
𝕌Rel-equiv R record { refl = Rrefl ; sym = Rsymm ; trans = Rtran } = record
  { refl =  𝕌Rel-refl R Rrefl
  ; sym =   𝕌Rel-symm R Rsymm
  ; trans = 𝕌Rel-tran R Rtran
  }

-- homomorphisms
𝕌SL-fun : {X Y : Set} → (X → Y) → (𝕌SL X → 𝕌SL Y)
𝕌SL-fun f (I , a) = I , (λ x → f (a x))

𝕌SL-fun-cong : {X Y : Set} → (R : Rel X _) → (S : Rel Y _) → (f : X → Y)
  → f Preserves R ⟶ S → (𝕌SL-fun f) Preserves (𝕌Rel R) ⟶ (𝕌Rel S)
𝕌SL-fun-cong R S f f-pres {I , a} {J , b} (a<b , b<a) =
  (λ i → proj₁ (a<b i) , f-pres (proj₂ (a<b i)) ) ,
  (λ i → proj₁ (b<a i) , f-pres (proj₂ (b<a i)) )

-- Monad
𝕌SL-η : {X : Set} → X → 𝕌SL X
𝕌SL-η x = 𝕌⊤ , (λ i → x)

𝕌SL-μ : {X : Set} → 𝕌SL (𝕌SL X) → 𝕌SL X
𝕌SL-μ (I , f) = (𝕌Σ (I , (λ i → proj₁ (f i)))) , λ {(i , j) → proj₂ (f i) j}

𝕌SL-κ : {X Y : Set} → (X → 𝕌SL Y) → (𝕌SL X → 𝕌SL Y)
𝕌SL-κ f (I , A) = 𝕌Σ (I , (λ i → proj₁ (f (A i)))) , λ {(i , j) → proj₂ (f (A i)) j}

𝕌SL-μ≡ : {X : Set} → (d d' : 𝕌SL (𝕌SL X)) → 𝕌Γ (𝕌Γ _≡_) d d'
  → 𝕌Γ _≡_ (𝕌SL-μ d) (𝕌SL-μ d')
𝕌SL-μ≡ (I , f) (J , g) H (i , x) =
  (proj₁ (H i) , proj₁ (proj₂ (H i) x)) , proj₂ (proj₂ (H i) x)
  

𝕌SL-⊥ : {X : Set} → 𝕌SL X
𝕌SL-⊥ = 𝕌⊥ , (λ {()})

𝕌SL-⊥-⊂ : {X : Set} → (a : 𝕌SL X) → 𝕌SL→ X 𝕌SL-⊥ a
𝕌SL-⊥-⊂ a ()

