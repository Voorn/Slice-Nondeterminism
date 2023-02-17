module Small-Slice.Marbles where

open import Data.Unit
open import Data.Empty
open import Data.Sum renaming (map to map⊎)
open import Data.Nat hiding (_⊔_)
open import Data.Product renaming (map to map×)
open import Relation.Binary.PropositionalEquality hiding ([_])


open import Small-Slice.Univ
open import Small-Slice.ND-functions


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


𝕃-δμ⊂id : (X : Set) → 𝕌Hom-⊂ (𝕌Hom-∘ (𝕃-μ X) (𝕃-δ X)) (𝕌Hom-id (𝕃 X))
𝕃-δμ⊂id X end i = tt , refl
𝕃-δμ⊂id X (app x l) (inj₁ tt , tt) = tt , refl
𝕃-δμ⊂id X (app x l) (inj₂ i , tt) = tt , (cong (app x) (proj₂ (𝕃-δμ⊂id X l (i , tt))))

𝕃-id⊂δμ : (X : Set) → 𝕌Hom-⊂ (𝕌Hom-id (𝕃 X)) (𝕌Hom-∘ (𝕃-μ X) (𝕃-δ X))
𝕃-id⊂δμ X end i = (tt , tt) , refl
𝕃-id⊂δμ X (app x a) i = (inj₁ tt , tt) , refl


-- adjoint property
𝕃-id⊂μδ : (X : Set) → 𝕌Hom-⊂ (𝕌Hom-id ((𝕃 X) × (𝕃 X))) (𝕌Hom-∘ (𝕃-δ X) (𝕃-μ X))
𝕃-id⊂μδ X (end , end) i = (tt , tt) , refl
𝕃-id⊂μδ X (end , app y b) i = (tt , inj₁ tt) , refl
𝕃-id⊂μδ X (app x a , b) tt with 𝕃-id⊂μδ X (a , b) tt
... | (tt , i) , eq = (tt , (inj₂ i)) , (cong (λ v → app x (proj₁ v) , (proj₂ v)) eq)





𝕃-η : (X : Set) → 𝕌Hom ⊤ (𝕃 X)
𝕃-η X tt = 𝕌SL-η end


𝕃-ε : (X : Set) → 𝕌Hom (𝕃 X) ⊤
𝕃-ε X end = 𝕌⊤ , (λ i → tt)
𝕃-ε X (app x a) = 𝕌⊥ , (λ {()})


𝕃-id⊂ηε : (X : Set) → 𝕌Hom-⊂ (𝕌Hom-id ⊤) (𝕌Hom-∘ (𝕃-ε X) (𝕃-η X))
𝕃-id⊂ηε X tt i = (tt , tt) , refl


𝕃-ηε⊂id : (X : Set) → 𝕌Hom-⊂ (𝕌Hom-∘ (𝕃-ε X) (𝕃-η X)) (𝕌Hom-id ⊤)
𝕃-ηε⊂id X tt i = tt , refl

-- adjoint property
𝕃-εη⊂id : (X : Set) → 𝕌Hom-⊂ (𝕌Hom-∘ (𝕃-η X) (𝕃-ε X)) (𝕌Hom-id (𝕃 X))
𝕃-εη⊂id X end i = tt , refl


open import Small-Slice.Monoidal
open import Small-Slice.Semi-Lattice

Prop-⊗ : (X : Set) → ℕ → Set
Prop-⊗ X zero = ⊤
Prop-⊗ X (suc n) = X × Prop-⊗ X n

Prop-α : (X : Set) → {n m : ℕ} → (Prop-⊗ X n) × (Prop-⊗ X m) → Prop-⊗ X (n + m)
Prop-α X {zero} {m} (tt , v) = v
Prop-α X {suc n} {m} ((x , u) , v) = x , Prop-α X {n} {m} (u , v)

Prop-β : (X : Set) → {n m : ℕ} → Prop-⊗ X (n + m) → (Prop-⊗ X n) × (Prop-⊗ X m)
Prop-β X {zero} {m} u = tt , u
Prop-β X {suc n} {m} (x , u) with Prop-β X {n} {m} u
...| (v , w) = (x , v) , w

--Prop-place : (X : Set) → {n m : ℕ} → (f : 𝕌Hom (Prop-⊗ X n) (Prop-⊗ X m)) → (a b : ℕ)
--  → 𝕌Hom (Prop-⊗ X (a + (n + b))) (Prop-⊗ X (a + (m + b)))

α-map : {X : Set} → (X × (X × X)) → ((X × X) × X)
α-map (a , b , c) = (a , b) , c

β-map : {X : Set} → ((X × X) × X) → (X × (X × X))
β-map ((a , b) , c) = a , b , c


-- sharing property
𝕃-share : (X : Set) → 𝕌Hom-≡ (𝕌Hom-∘ (𝕃-δ X) (𝕃-μ X))
  (𝕌Hom-∨ (𝕌Hom-∘ (λ z → (𝕌Hom-⊗ ((𝕃-μ X) , 𝕌Hom-id (𝕃 X))) (α-map z))
                  (𝕌Hom-⊗ ((𝕌Hom-id (𝕃 X)) , 𝕃-δ X)))
          (𝕌Hom-∘ (λ z → 𝕌Hom-⊗ (𝕌Hom-id (𝕃 X) , 𝕃-μ X) (β-map z))
                  (𝕌Hom-⊗ (𝕃-δ X , 𝕌Hom-id (𝕃 X)))))
proj₁ (𝕃-share X) (end , b) (tt , i) = (inj₁ ((tt , i) , (tt , tt))) , refl
proj₁ (𝕃-share X) (app x a , b) (tt , inj₁ tt) = (inj₂ (((inj₁ tt) , tt) , (tt , tt))) , refl
proj₁ (𝕃-share X) (app x a , b) (tt , inj₂ i) with proj₁ (𝕃-share X) (a , b) (tt , i)
... | inj₁ ((tt , j) , tt , tt) , eq = (inj₁ ((tt , j) , (tt , tt))) ,
  (cong (λ u → app x (proj₁ u) , proj₂ u) eq)
... | inj₂ ((j , tt) , tt , tt) , eq = (inj₂ (((inj₂ j) , tt) , (tt , tt))) ,
  (cong (λ u → app x (proj₁ u) , proj₂ u) eq)
proj₂ (𝕃-share X) (end , b) (inj₁ ((tt , i) , tt , tt)) = (tt , i) , refl
proj₂ (𝕃-share X) (app x a , b) (inj₁ ((tt , i) , tt , tt))
  with proj₂ (𝕃-share X) (a , b) (inj₁ ((tt , i) , (tt , tt)))
... | (tt , j) , eq = (tt , (inj₂ j)) , (cong (λ u → app x (proj₁ u) , proj₂ u) eq)
proj₂ (𝕃-share X) (end , end) (inj₂ j) = (tt , tt) , refl
proj₂ (𝕃-share X) (end , app x b) (inj₂ j) = (tt , (inj₁ tt)) , refl
proj₂ (𝕃-share X) (app x a , b) (inj₂ ((inj₁ tt , tt) , tt , tt)) = (tt , (inj₁ tt)) , refl
proj₂ (𝕃-share X) (app x a , b) (inj₂ ((inj₂ i , tt) , tt , tt))
  with proj₂ (𝕃-share X) (a , b) (inj₂ ((i , tt) , tt , tt))
... | (tt , j) , eq = (tt , (inj₂ j)) , (cong (λ u → app x (proj₁ u) , proj₂ u) eq)




-- interleaving
𝕃-∥ : {X : Set} → 𝕌Hom (𝕃 X × 𝕃 X) (𝕃 X)
𝕃-∥l : {X : Set} → 𝕌Hom (𝕃 X × 𝕃 X) (𝕃 X)
𝕃-∥r : {X : Set} → 𝕌Hom (𝕃 X × 𝕃 X) (𝕃 X)
𝕃-∥ (a , b) = 𝕌SL-∨ (𝕃-∥l (a , b)) (𝕃-∥r (a , b))
𝕃-∥l (end , b) = 𝕌SL-η b
𝕃-∥l (app x a , b) = 𝕌SL-fun (app x) (𝕃-∥ (a , b))
𝕃-∥r (a , end) = 𝕌SL-η a
𝕃-∥r (a , app x b) = 𝕌SL-fun (app x) (𝕃-∥ (a , b))

-- commutativity
𝕃-∥-com : {X : Set} → 𝕌Hom-≡ (𝕃-∥ {X}) (λ (a , b) → 𝕃-∥ (b , a))
𝕃-∥-tcom : {X : Set} → 𝕌Hom-≡ (𝕃-∥l {X}) (λ (a , b) → 𝕃-∥r (b , a)) 
proj₁ 𝕃-∥-com (a , b) (inj₁ i) =
  inj₂ (proj₁ (proj₁ 𝕃-∥-tcom (a , b) i)) , proj₂ (proj₁ 𝕃-∥-tcom (a , b) i)
proj₁ 𝕃-∥-com (a , b) (inj₂ i) =
  inj₁ (proj₁ (proj₂ 𝕃-∥-tcom (b , a) i)) , proj₂ (proj₂ 𝕃-∥-tcom (b , a) i)
proj₂ 𝕃-∥-com (a , b) (inj₁ i) =
  inj₂ (proj₁ (proj₁ 𝕃-∥-tcom (b , a) i)) , proj₂ (proj₁ 𝕃-∥-tcom (b , a) i)
proj₂ 𝕃-∥-com (a , b) (inj₂ i) =
  inj₁ (proj₁ (proj₂ 𝕃-∥-tcom (a , b) i)) , proj₂ (proj₂ 𝕃-∥-tcom (a , b) i)
proj₁ 𝕃-∥-tcom (end , b) tt = tt , refl
proj₁ 𝕃-∥-tcom (app x a , b) i with proj₁ 𝕃-∥-com (a , b) i
... | k , eq = k , (cong (app x) eq)
proj₂ 𝕃-∥-tcom (end , b) tt = tt , refl
proj₂ 𝕃-∥-tcom (app x a , b) i with proj₁ 𝕃-∥-com (b , a) i
... | k , eq = k , (cong (app x) eq)

-- left unitality
𝕃-∥-luni  : {X : Set} → 𝕌Hom-≡ (λ a → 𝕃-∥  (end , a)) (𝕌Hom-id (𝕃 X))
𝕃-∥l-luni : {X : Set} → 𝕌Hom-≡ (λ a → 𝕃-∥l (end , a)) (𝕌Hom-id (𝕃 X))
𝕃-∥r-luni : {X : Set} → 𝕌Hom-≡ (λ a → 𝕃-∥r (end , a)) (𝕌Hom-id (𝕃 X))
proj₁ 𝕃-∥-luni a (inj₁ tt) = proj₁ 𝕃-∥l-luni a tt
proj₁ 𝕃-∥-luni a (inj₂ i)  = proj₁ 𝕃-∥r-luni a i 
proj₂ 𝕃-∥-luni a tt = (inj₁ tt) , refl
proj₁ 𝕃-∥l-luni a i = tt , refl
proj₂ 𝕃-∥l-luni a i = tt , refl
proj₁ 𝕃-∥r-luni end tt = tt , refl
proj₁ 𝕃-∥r-luni (app x a) i with proj₁ 𝕃-∥-luni a i
... | k , eq = k , (cong (app x) eq)
proj₂ 𝕃-∥r-luni end tt = tt , refl
proj₂ 𝕃-∥r-luni (app x a) tt with proj₂ 𝕃-∥-luni a tt
... | k , eq = k , (cong (app x) eq)


-- associativity (one way)
-- it is split into three cases, each focussing on a different input list
𝕃-∥-asso : {X : Set} → (a b c : 𝕃 X) → 𝕌SL→ _
  (𝕌SL-κ (λ z → 𝕃-∥ (z , c)) (𝕃-∥ (a , b)))   (𝕌SL-κ (λ z → 𝕃-∥ (a , z)) (𝕃-∥ (b , c)))
𝕃-∥l-asso : {X : Set} → (a b c : 𝕃 X) → 𝕌SL→ _
  (𝕌SL-κ (λ z → 𝕃-∥l (z , c)) (𝕃-∥l (a , b))) (𝕌SL-κ (λ z → 𝕃-∥l (a , z)) (𝕃-∥ (b , c)))
𝕃-∥m-asso : {X : Set} → (a b c : 𝕃 X) → 𝕌SL→ _
  (𝕌SL-κ (λ z → 𝕃-∥l (z , c)) (𝕃-∥r (a , b)))  (𝕌SL-κ (λ z → 𝕃-∥ (a , z)) (𝕃-∥l (b , c)))
𝕃-∥r-asso : {X : Set} → (a b c : 𝕃 X) → 𝕌SL→ _
  (𝕌SL-κ (λ z → 𝕃-∥r (z , c)) (𝕃-∥ (a , b)))  (𝕌SL-κ (λ z → 𝕃-∥ (a , z)) (𝕃-∥r (b , c)))
-- the neutral operation directly splits into the three subcases by case analysis on index
𝕃-∥-asso a b c (i , inj₂ j)      with 𝕃-∥r-asso a b c (i , j)
... | (u , v) , eq = ((inj₂ u) , v) , eq
𝕃-∥-asso a b c (inj₁ i , inj₁ j) with 𝕃-∥l-asso a b c (i , j)
... | (u , v)  , eq = (u , (inj₁ v)) , eq
𝕃-∥-asso a b c (inj₂ i , inj₁ j) with 𝕃-∥m-asso a b c (i , j)
... | (u , v) , eq = ((inj₁ u) , v) , eq
-- the focussed operations depends on case of the list focussed upon.
𝕃-∥l-asso end b c (tt , i) = ((inj₁ i) , tt) , refl
𝕃-∥l-asso (app x a) b c i with 𝕃-∥-asso a b c i
... | u , eq = u , (cong (app x) eq)
𝕃-∥m-asso a end c (tt , i) = (tt , inj₁ i) , refl
𝕃-∥m-asso a (app x b) c i with 𝕃-∥-asso a b c i
... | (u , v) , eq = (u , inj₂ v) , cong (app x) eq
𝕃-∥r-asso a b end (i , tt) = (tt , i) , refl
𝕃-∥r-asso a b (app x c) i with 𝕃-∥-asso a b c i
... | (u , v) , eq = (u , (inj₂ v)) , (cong (app x) eq)

-- associativity the other way is provable using commutativity
