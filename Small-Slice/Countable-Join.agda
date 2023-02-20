module Small-Slice.Countable-Join where

open import Data.Unit
open import Data.Empty
open import Data.Sum renaming (map to map⊎)
open import Data.Nat
open import Data.Product renaming (map to map×)

open import Relation.Binary.PropositionalEquality hiding ([_])
 
open import Small-Slice.Univ
open import Small-Slice.ND-functions
open import Small-Slice.Semi-Lattice



𝕌SL-⋁ : {X : Set} → (U : 𝕌) → (𝕌S U → 𝕌SL X) → 𝕌SL X
𝕌SL-⋁ U f = (𝕌Σ (U , (λ n → proj₁ (f n)))) , λ {(n , i) → proj₂ (f n) i}

𝕌SL-chain : {X : Set} → ((ℕ → 𝕌SL X) → Set)
𝕌SL-chain S = (n : ℕ) → 𝕌SL→ _ (S n) (S (suc n))


𝕌SL-⋁-upper : {X : Set} → (U : 𝕌) → (C : 𝕌S U → 𝕌SL X)
  → (i : 𝕌S U) → 𝕌SL→ X (C i) (𝕌SL-⋁ U C)
𝕌SL-⋁-upper U C i j = (i , j) , refl

𝕌SL-⋁-supremum : {X : Set} → (U : 𝕌) → (C : 𝕌S U → 𝕌SL X)
  → (S : 𝕌SL X) → ((i : 𝕌S U) → 𝕌SL→ X (C i) S) → 𝕌SL→ X (𝕌SL-⋁ U C) S
𝕌SL-⋁-supremum U C S C<S (i , j) = C<S i j


𝕌Hom-⋁ : {X Y : Set} → (U : 𝕌) → (𝕌S U → 𝕌Hom X Y) → 𝕌Hom X Y
𝕌Hom-⋁ U S x = 𝕌SL-⋁ U (λ n → S n x)

𝕌Hom-⋁-≡ : {X Y : Set} → (U : 𝕌) → (C D : 𝕌S U → 𝕌Hom X Y)
  → ((n : 𝕌S U) → 𝕌Hom-≡ (C n) (D n))
  → 𝕌Hom-≡ (𝕌Hom-⋁ U C) (𝕌Hom-⋁ U D)
𝕌Hom-⋁-≡ U C D C≡D =
  (λ { x (n , i) → (n , (proj₁ (proj₁ (C≡D n) x i))) , (proj₂ (proj₁ (C≡D n) x i))}) ,
   λ { x (n , i) → (n , (proj₁ (proj₂ (C≡D n) x i))) , (proj₂ (proj₂ (C≡D n) x i))}

𝕌Hom-⋁-l∘ : {X Y Z : Set} → (f : 𝕌Hom X Y) → (U : 𝕌) → (S : 𝕌S U → 𝕌Hom Y Z)
  → 𝕌Hom-≡ (𝕌Hom-∘ (𝕌Hom-⋁ U S) f) (𝕌Hom-⋁ U (λ n → 𝕌Hom-∘ (S n) f))
proj₁ (𝕌Hom-⋁-l∘ U f S) x (i , n , j) = (n , i , j) , refl
proj₂ (𝕌Hom-⋁-l∘ U f S) x (n , i , j) = (i , n , j) , refl

𝕌Hom-⋁-r∘ : {X Y Z : Set} → (U : 𝕌) → (S : 𝕌S U → 𝕌Hom X Y) → (f : 𝕌Hom Y Z) 
  → 𝕌Hom-≡ (𝕌Hom-∘ f (𝕌Hom-⋁ U S)) (𝕌Hom-⋁ U (λ n → 𝕌Hom-∘ f (S n)))
proj₁ (𝕌Hom-⋁-r∘ U S f) x ((n , i) , j) = (n , i , j) , refl
proj₂ (𝕌Hom-⋁-r∘ U S f) x (n , i , j) = ((n , i) , j) , refl




-- just proving what I need for feedback to work

open import Small-Slice.Cartesian

𝕌Hom-⋁-copr-glue-r : {X Y Z : Set} → (f : 𝕌Hom X Z) → (C : ℕ → 𝕌Hom Y Z)
  → 𝕌Hom-≡ (𝕌-copr-glue f (𝕌Hom-⋁ 𝕌ℕ C)) (𝕌Hom-⋁ 𝕌ℕ (λ n → 𝕌-copr-glue f (C n)))
proj₁ (𝕌Hom-⋁-copr-glue-r f C) (inj₁ x) i = (zero , i) , refl
proj₁ (𝕌Hom-⋁-copr-glue-r f C) (inj₂ y) (n , i) = (n , i) , refl
proj₂ (𝕌Hom-⋁-copr-glue-r f C) (inj₁ x) (n , i) = i , refl
proj₂ (𝕌Hom-⋁-copr-glue-r f C) (inj₂ y) (n , i) = (n , i) , refl


-- chains

𝕌Hom-chain : {X Y : Set} → ((ℕ → 𝕌Hom X Y) → Set)
𝕌Hom-chain S = (n : ℕ) → 𝕌Hom-⊂ (S n) (S (suc n))

𝕌Hom-chain-plus : {X Y : Set} → (C : ℕ → 𝕌Hom X Y) → 𝕌Hom-chain C → (n m : ℕ)
  → 𝕌Hom-⊂ (C n) (C (m + n))
𝕌Hom-chain-plus C C-chain n zero = 𝕌Hom-⊂-Refl {_} {_} {C n}
𝕌Hom-chain-plus C C-chain n (suc m) = 𝕌Hom-⊂-Trans {_} {_}
  {C n} {C (m + n)} {C (suc m + n)}
    (𝕌Hom-chain-plus C C-chain n m)
    (C-chain (m + n))

ℕ+0 : (n : ℕ) → (n + zero ≡ n)
ℕ+0 zero = refl
ℕ+0 (suc n) = cong suc (ℕ+0 n)

ℕ+suc : (n m : ℕ) → (n + suc m ≡ suc (n + m))
ℕ+suc zero m = refl
ℕ+suc (suc n) m = cong suc (ℕ+suc n m)

ℕ-max+ : (n m : ℕ) → Σ ℕ λ k → (k + n ≡ n ⊔ m)
ℕ-max+ zero m = m , ℕ+0 m
ℕ-max+ (suc n) zero = zero , refl
ℕ-max+ (suc n) (suc m) = proj₁ (ℕ-max+ n m) ,
                    trans (ℕ+suc (proj₁ (ℕ-max+ n m)) n) (cong suc (proj₂ (ℕ-max+ n m)))

ℕ-max-sym : (n m : ℕ) → (n ⊔ m ≡ m ⊔ n)
ℕ-max-sym zero zero = refl
ℕ-max-sym zero (suc m) = refl
ℕ-max-sym (suc n) zero = refl
ℕ-max-sym (suc n) (suc m) = cong suc (ℕ-max-sym n m)

𝕌Hom-chain-lmax : {X Y : Set} → (C : ℕ → 𝕌Hom X Y) → 𝕌Hom-chain C → (n m : ℕ)
  → 𝕌Hom-⊂ (C n) (C (n ⊔ m))
𝕌Hom-chain-lmax C C-chain n m with ℕ-max+ n m
... | k , eq = subst (λ z → 𝕌Hom-⊂ (C n) (C z)) eq (𝕌Hom-chain-plus C C-chain n k)

𝕌Hom-chain-rmax : {X Y : Set} → (C : ℕ → 𝕌Hom X Y) → 𝕌Hom-chain C → (n m : ℕ)
  → 𝕌Hom-⊂ (C m) (C (n ⊔ m))
𝕌Hom-chain-rmax C C-chain n m with ℕ-max+ m n
... | k , eq = subst (λ z → 𝕌Hom-⊂ (C m) (C z)) (trans eq (ℕ-max-sym m n))
  (𝕌Hom-chain-plus C C-chain m k)



𝕌Hom-chain-∘ : {X Y Z : Set} → (F : ℕ → 𝕌Hom X Y) → (G : ℕ → 𝕌Hom Y Z)
  → 𝕌Hom-chain F → 𝕌Hom-chain G → 𝕌Hom-chain (λ n → 𝕌Hom-∘ (G n) (F n))
𝕌Hom-chain-∘ F G F-chain G-chain n = 𝕌Hom-∘⊂ (F-chain n) (G-chain n)


𝕌Hom-⋁-∘ : {X Y Z : Set} → (F : ℕ → 𝕌Hom X Y) → (G : ℕ → 𝕌Hom Y Z)
  → 𝕌Hom-chain F → 𝕌Hom-chain G
  → 𝕌Hom-≡ (𝕌Hom-∘ (𝕌Hom-⋁ 𝕌ℕ G) (𝕌Hom-⋁ 𝕌ℕ F)) (𝕌Hom-⋁ 𝕌ℕ (λ n → 𝕌Hom-∘ (G n) (F n)))
proj₁ (𝕌Hom-⋁-∘ F G F-chain G-chain) x ((n , i) , (m , j))
  with 𝕌Hom-∘⊂ {_} {_} {_} {F n} {F (n ⊔ m)} {G m} {G (n ⊔ m)}
               (𝕌Hom-chain-lmax F F-chain n m) (𝕌Hom-chain-rmax G G-chain n m) x (i , j)
... | (u , v) , eq = ((n ⊔ m) , (u , v)) , eq
proj₂ (𝕌Hom-⋁-∘ F G F-chain G-chain) x (n , i , j) = ((n , i) , (n , j)) , refl


open import Small-Slice.Monoidal

𝕌Hom-chain-⊎ : {X Y Z W : Set} → (F : ℕ → 𝕌Hom X Y) → (G : ℕ → 𝕌Hom Z W)
  → 𝕌Hom-chain F → 𝕌Hom-chain G → 𝕌Hom-chain (λ n → 𝕌Hom-⊎ (F n , G n))
𝕌Hom-chain-⊎ F G F-chain G-chain n (inj₁ x) i =
  (proj₁ (F-chain n x i)) , (cong inj₁ (proj₂ (F-chain n x i)))
𝕌Hom-chain-⊎ F G F-chain G-chain n (inj₂ z) i =
  (proj₁ (G-chain n z i)) , (cong inj₂ (proj₂ (G-chain n z i)))


𝕌Hom-⋁-⊎ : {X Y Z W : Set} → (F : ℕ → 𝕌Hom X Y) → (G : ℕ → 𝕌Hom Z W)
  → 𝕌Hom-chain F → 𝕌Hom-chain G
  → 𝕌Hom-≡ (𝕌Hom-⊎ (𝕌Hom-⋁ 𝕌ℕ F , 𝕌Hom-⋁ 𝕌ℕ G)) (𝕌Hom-⋁ 𝕌ℕ (λ n → 𝕌Hom-⊎ (F n , G n)))
proj₁ (𝕌Hom-⋁-⊎ F G F-chain G-chain) (inj₁ x) i = i , refl
proj₁ (𝕌Hom-⋁-⊎ F G F-chain G-chain) (inj₂ z) i = i , refl
proj₂ (𝕌Hom-⋁-⊎ F G F-chain G-chain) (inj₁ x) i = i , refl
proj₂ (𝕌Hom-⋁-⊎ F G F-chain G-chain) (inj₂ z) i = i , refl


𝕌Hom-chain-⊗ : {X Y Z W : Set} → (F : ℕ → 𝕌Hom X Y) → (G : ℕ → 𝕌Hom Z W)
  → 𝕌Hom-chain F → 𝕌Hom-chain G → 𝕌Hom-chain (λ n → 𝕌Hom-⊗ (F n , G n))
𝕌Hom-chain-⊗ F G F-chain G-chain n (x , z) (i , j) =
  ((proj₁ (F-chain n x i)) , (proj₁ (G-chain n z j))) ,
  (cong₂ (λ a b → a , b) (proj₂ (F-chain n x i)) (proj₂ (G-chain n z j)))


𝕌Hom-⋁-⊗ : {X Y Z W : Set} → (F : ℕ → 𝕌Hom X Y) → (G : ℕ → 𝕌Hom Z W)
  → 𝕌Hom-chain F → 𝕌Hom-chain G
  → 𝕌Hom-≡ (𝕌Hom-⊗ (𝕌Hom-⋁ 𝕌ℕ F , 𝕌Hom-⋁ 𝕌ℕ G)) (𝕌Hom-⋁ 𝕌ℕ (λ n → 𝕌Hom-⊗ (F n , G n)))
proj₁ (𝕌Hom-⋁-⊗ F G F-chain G-chain) xz ((n , i) , (m , j))
  with 𝕌Hom-⊗-⊂  {_} {_} {F n , G m} {F (n ⊔ m) , G (n ⊔ m)}
       ((𝕌Hom-chain-lmax F F-chain n m) , (𝕌Hom-chain-rmax G G-chain n m)) xz (i , j)
... | (u , eq) = ((n ⊔ m) , u) , eq
proj₂ (𝕌Hom-⋁-⊗ F G F-chain G-chain) (x , z) (n , i , j) = ((n , i) , n , j) , refl

