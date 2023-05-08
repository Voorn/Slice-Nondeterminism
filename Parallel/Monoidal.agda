module Parallel.Monoidal where

open import Data.Unit
open import Data.Empty
open import Data.Sum renaming (map to map⊎)
open import Data.Nat hiding (_⊔_)
open import Data.Product renaming (map to map×)
open import Relation.Binary.PropositionalEquality hiding ([_])


open import Slice-Functions.Base
open import Slice-Functions.Monoidal
open import Monads.Trace

open import Parallel.Base



-- Pseudomonoidal monad
ℙ-monoid-unit : (A E X Y : Set) → SF≡ (SF-∘ (SF-T-η A E X ⊗ SF-T-η A E Y) (ℙ A E X Y))
                                             (SF-T-η A E (X × Y))
ℙ-monoid-unit A E X Y = (λ { p (i , inj₁ tt) → tt , refl ; p (i , inj₂ tt) → tt , refl}) ,
                        λ x i → ((tt , tt) , (inj₁ tt)) , refl


ℙ-pseudo-mult : (A E X Y : Set)
  → SF≤ (SF-∘ (ℙ A E _ _) (SF-∘ (SF-T A E (ℙ A E X Y)) (SF-T-μ A E _)))
          (SF-∘ (SF-T-μ A E X ⊗ SF-T-μ A E Y) (ℙ A E X Y))
ℙ-pseudo-mult A E X Y (act a d , q) (inj₁ i , j , tt)
  with ℙ-pseudo-mult A E X Y (d , q) (i , (j , tt))
... | (u , v) , eq = ((tt , tt) , (inj₁ v)) , cong (act a) eq
ℙ-pseudo-mult A E X Y (err e , q) (inj₁ i , j , tt) = ((tt , tt) , (inj₁ tt)) , refl
ℙ-pseudo-mult A E X Y (ret x , act a q) (inj₂ i , j , tt)
    with ℙ-pseudo-mult A E X Y (ret x , q) (i , (j , tt))
... | (u , v) , eq = ((tt , tt) , (inj₂ v)) , cong (act a) eq
ℙ-pseudo-mult A E X Y (act b d , act a q) (inj₂ i , j , tt)
    with ℙ-pseudo-mult A E X Y (act b d , q) (i , (j , tt))
... | (u , v) , eq = ((tt , tt) , (inj₂ v)) , cong (act a) eq
ℙ-pseudo-mult A E X Y (err e , act a q) (inj₂ i , j , tt)
    with ℙ-pseudo-mult A E X Y (err e , q) (i , (j , tt))
... | (u , v) , eq = ((tt , tt) , (inj₂ v)) , cong (act a) eq
ℙ-pseudo-mult A E X Y (ret t , err e) (inj₂ i , j , tt) = ((tt , tt) , (inj₂ tt)) , refl
ℙ-pseudo-mult A E X Y (act a d , err e) (inj₂ i , j , tt) = ((tt , tt) , (inj₂ tt)) , refl
ℙ-pseudo-mult A E X Y (err f , err e) (inj₂ i , j , tt) = ((tt , tt) , (inj₂ tt)) , refl
ℙ-pseudo-mult A E X Y (ret t , ret r) (inj₂ i , j , tt) = ((tt , tt) , j) , refl
ℙ-pseudo-mult A E X Y (ret t , ret r) (inj₁ i , j , tt) = ((tt , tt) , j) , refl


-- Monoidal comonad (dependent on naturality of ℙ)
ℙ-moncom-unit : (A E X Y : Set) → SF≡ (SF-∘ (ℙ A E X Y) (SF-T-ε A E (X × Y)))
  (SF-T-ε A E X ⊗ SF-T-ε A E Y)
proj₁ (ℙ-moncom-unit A E X Y) (ret x , ret y) (inj₁ i , j) = (tt , tt) , refl
proj₁ (ℙ-moncom-unit A E X Y) (ret x , ret y) (inj₂ i , j) = (tt , tt) , refl
proj₂ (ℙ-moncom-unit A E X Y) (ret x , ret y) (i , j) = ((inj₁ tt) , tt) , refl



ℙ-moncom-mult< : (A E X Y : Set) → SF≤ (SF-∘ (ℙ A E X Y) (SF-T-δ A E (X × Y)))
  (SF-∘ (SF-T-δ A E X ⊗ SF-T-δ A E Y) (SF-∘ (ℙ A E _ _) (SF-T A E (ℙ A E X Y))))
ℙ-moncom-mult𝕃< : (A E X Y : Set) → SF≤ (SF-∘ (𝕃 A E X Y) (SF-T-δ A E (X × Y)))
  (SF-∘ (SF-T-δ A E X ⊗ SF-T-δ A E Y) (SF-∘ (ℙ A E _ _) (SF-T A E (ℙ A E X Y))))
ℙ-moncom-multℝ< : (A E X Y : Set) → SF≤ (SF-∘ (ℝ A E X Y) (SF-T-δ A E (X × Y)))
  (SF-∘ (SF-T-δ A E X ⊗ SF-T-δ A E Y) (SF-∘ (ℙ A E _ _) (SF-T A E (ℙ A E X Y))))

ℙ-moncom-mult< A E X Y l-r (inj₁ i , j) = ℙ-moncom-mult𝕃< A E X Y l-r (i , j)
ℙ-moncom-mult< A E X Y l-r (inj₂ i , j) = ℙ-moncom-multℝ< A E X Y l-r (i , j)

ℙ-moncom-mult𝕃< A E X Y (act a l , r) (i , inj₂ j)
  with ℙ-moncom-mult< A E X Y (l , r) (i , j)
... | ((u , v) , (w , p)) , eq = ((inj₂ u  , v) , inj₁ w , p) , cong (act a) eq
ℙ-moncom-mult𝕃< A E X Y (err e , r) (i , inj₂ y) =
  (((inj₂ tt) , SF-T-δ-Total A E Y r) , (inj₁ tt) , tt) , refl
ℙ-moncom-mult𝕃< A E X Y (ret x , ret y) (i , j) =
  ((tt , tt) , ((inj₁ tt) , (inj₁ tt))) , refl
ℙ-moncom-mult𝕃< A E X Y (act a l , ret y) (i , inj₁ j) =
  (((inj₁ tt) , tt) , ((inj₁ tt) , (inj₁ i))) , refl
ℙ-moncom-mult𝕃< A E X Y (act a l , act b r) (i , inj₁ j) =
  (((inj₁ tt) , inj₁ tt) , (inj₁ tt) , (inj₁ i)) , refl
ℙ-moncom-mult𝕃< A E X Y (act a l , err e) (i , inj₁ j) =
  (((inj₁ tt) , inj₁ tt) , (inj₁ tt) , (inj₁ i)) , refl
ℙ-moncom-mult𝕃< A E X Y (err e , ret y) (i , inj₁ x) =
  (((inj₁ tt) , tt) , ((inj₁ tt) , (inj₁ tt))) , refl
ℙ-moncom-mult𝕃< A E X Y (err e , act a r) (i , inj₁ x) =
  (((inj₁ tt) , (inj₁ tt)) , ((inj₁ tt) , (inj₁ tt))) , refl
ℙ-moncom-mult𝕃< A E X Y (err e , err v) (i , inj₁ x) =
  (((inj₁ tt ) , (inj₁ tt)) , ((inj₁ tt) , (inj₁ tt))) , refl

ℙ-moncom-multℝ< A E X Y  (l , act a r) (i , inj₂ j)
  with ℙ-moncom-mult< A E X Y (l , r) (i , j)
... | ((u , v) , (w , p)) , eq = ((u , inj₂ v) , inj₂ w , p) , cong (act a) eq
ℙ-moncom-multℝ< A E X Y (r , err e) (i , inj₂ y) =
  ((SF-T-δ-Total A E X r , (inj₂ tt)) , (inj₂ tt) , tt) , refl
ℙ-moncom-multℝ< A E X Y (ret x , ret y) (i , j) =
  ((tt , tt) , ((inj₁ tt) , (inj₁ tt))) , refl
ℙ-moncom-multℝ< A E X Y (ret y , act a l) (i , inj₁ j) =
  ((tt , (inj₁ tt)) , ((inj₁ tt) , (inj₂ i))) , refl
ℙ-moncom-multℝ< A E X Y  (act a l , act b r) (i , inj₁ j) =
  (((inj₁ tt) , inj₁ tt) , (inj₁ tt) , (inj₂ i)) , refl
ℙ-moncom-multℝ< A E X Y (err e , act b r) (i , inj₁ j) =
  (((inj₁ tt) , inj₁ tt) , (inj₁ tt) , (inj₂ i)) , refl
ℙ-moncom-multℝ< A E X Y  (ret x , err e) (i , inj₁ tt) =
  ((tt , (inj₁ tt)) , ((inj₁ tt) , (inj₂ tt))) , refl
ℙ-moncom-multℝ< A E X Y  (act a r , err e) (i , inj₁ x) =
  (((inj₁ tt) , (inj₁ tt)) , ((inj₁ tt) , (inj₂ tt))) , refl
ℙ-moncom-multℝ< A E X Y  (err e , err v) (i , inj₁ x) =
  (((inj₁ tt ) , (inj₁ tt)) , ((inj₁ tt) , (inj₂ tt))) , refl


ℙ-moncom-mult> : (A E X Y : Set)
  → SF≤ (SF-∘ (SF-T-δ A E X ⊗ SF-T-δ A E Y) (SF-∘ (ℙ A E _ _) (SF-T A E (ℙ A E X Y))))
          (SF-∘ (ℙ A E X Y) (SF-T-δ A E (X × Y)))
ℙ-moncom-mult𝕃> : (A E X Y : Set)
  → SF≤ (SF-∘ (SF-T-δ A E X ⊗ SF-T-δ A E Y) (SF-∘ (𝕃 A E _ _) (SF-T A E (ℙ A E X Y))))
          (SF-∘ (ℙ A E X Y) (SF-T-δ A E (X × Y)))
ℙ-moncom-multℝ> : (A E X Y : Set)
  → SF≤ (SF-∘ (SF-T-δ A E X ⊗ SF-T-δ A E Y) (SF-∘ (ℝ A E _ _) (SF-T A E (ℙ A E X Y))))
          (SF-∘ (ℙ A E X Y) (SF-T-δ A E (X × Y)))

ℙ-moncom-mult> A E X Y l-r (i , inj₁ k , v) = ℙ-moncom-mult𝕃> A E X Y l-r (i , k , v)
ℙ-moncom-mult> A E X Y l-r (i , inj₂ k , v) = ℙ-moncom-multℝ> A E X Y l-r (i , k , v)

ℙ-moncom-mult𝕃> A E X Y (act a t , r) ((inj₂ i , j) , k , v)
  with ℙ-moncom-mult> A E X Y (t , r) ((i , j) , k , v)
... | (u , w) , eq = ((inj₁ u) , (inj₂ w)) , (cong (act a) eq)
ℙ-moncom-mult𝕃> A E X Y (err e , r) ((inj₂ y , j) , k , v) = ((inj₁ tt) , (inj₂ tt)) , refl
ℙ-moncom-mult𝕃> A E X Y (ret x , ret y) ((i , j) , k , inj₁ tt) = ((inj₁ tt) , tt) , refl
ℙ-moncom-mult𝕃> A E X Y (ret x , ret y) ((i , j) , k , inj₂ tt) = ((inj₁ tt) , tt) , refl
ℙ-moncom-mult𝕃> A E X Y (ret x , act a r) ((i , inj₁ j) , k , inj₂ y) =
  ((inj₂ y) , (inj₁ tt)) , refl
ℙ-moncom-mult𝕃> A E X Y (ret x , err e) ((i , inj₁ j) , k , inj₂ tt) =
  ((inj₂ tt) , (inj₁ tt)) , refl
ℙ-moncom-mult𝕃> A E X Y (act a t , ret y) ((inj₁ i , j) , k , inj₁ v) =
  (inj₁ v , inj₁ tt) , refl
ℙ-moncom-mult𝕃> A E X Y (act a t , act b r) ((inj₁ i , inj₁ x) , k , inj₁ v) =
  ((inj₁ v) , (inj₁ tt)) , refl
ℙ-moncom-mult𝕃> A E X Y (act a t , act b r) ((inj₁ i , inj₁ x) , k , inj₂ v) =
  ((inj₂ v) , (inj₁ tt)) , refl
ℙ-moncom-mult𝕃> A E X Y (act a t , err e) ((inj₁ i , inj₁ j) , k , inj₁ v) =
  ((inj₁ v) , (inj₁ tt)) , refl
ℙ-moncom-mult𝕃> A E X Y (act a t , err e) ((inj₁ i , inj₁ j) , k , inj₂ v) =
  ((inj₂ v) , (inj₁ tt)) , refl
ℙ-moncom-mult𝕃> A E X Y (err e , ret y) ((inj₁ x , j) , k , inj₁ tt) =
  ((inj₁ tt) , (inj₁ tt)) , refl
ℙ-moncom-mult𝕃> A E X Y (err e , act b r) ((inj₁ x , inj₁ j) , k , inj₁ v) =
  (inj₁ v , inj₁ tt) , refl
ℙ-moncom-mult𝕃> A E X Y (err e , act b r) ((inj₁ x , inj₁ j) , k , inj₂ v) =
  (inj₂ v , inj₁ tt) , refl
ℙ-moncom-mult𝕃> A E X Y (err e , err f) ((inj₁ i , inj₁ j) , k , inj₁ v) =
  ((inj₁ tt) , (inj₁ tt)) , refl
ℙ-moncom-mult𝕃> A E X Y (err e , err f) ((inj₁ i , inj₁ j) , k , inj₂ v) =
  ((inj₂ tt) , (inj₁ tt)) , refl

ℙ-moncom-multℝ> A E X Y (r , err e) ((y , inj₂ j) , k , v) = ((inj₂ tt) , (inj₂ tt)) , refl
ℙ-moncom-multℝ> A E X Y (l , act a r) ((i , inj₂ j) , k , v)
  with ℙ-moncom-mult> A E X Y (l , r) ((i , j) , k , v)
... | (u , w) , eq = ((inj₂ u) , (inj₂ w)) , (cong (act a) eq)
ℙ-moncom-multℝ> A E X Y (ret x , ret y) ((i , j) , k , inj₁ tt) = ((inj₁ tt) , tt) , refl
ℙ-moncom-multℝ> A E X Y (ret x , ret y) ((i , j) , k , inj₂ tt) = ((inj₁ tt) , tt) , refl
ℙ-moncom-multℝ> A E X Y (act a l , ret x) ((inj₁ i , j) , k , inj₁ y) =
  ((inj₁ y) , inj₁ tt) , refl
ℙ-moncom-multℝ> A E X Y (err e , ret x) ((inj₁ i , j) , k , inj₁ tt) =
  ((inj₁ tt) , (inj₁ tt)) , refl
ℙ-moncom-multℝ> A E X Y (ret x , act a r) ((i , inj₁ j) , k , inj₂ v) =
  (inj₂ v , inj₁ tt) , refl
ℙ-moncom-multℝ> A E X Y (act a t , act b r) ((inj₁ i , inj₁ x) , k , inj₁ v) =
  ((inj₁ v) , (inj₁ tt)) , refl
ℙ-moncom-multℝ> A E X Y (act a t , act b r) ((inj₁ i , inj₁ x) , k , inj₂ v) =
  ((inj₂ v) , (inj₁ tt)) , refl
ℙ-moncom-multℝ> A E X Y (err e , act a r) ((inj₁ i , inj₁ j) , k , inj₁ v) =
  ((inj₁ v) , (inj₁ tt)) , refl
ℙ-moncom-multℝ> A E X Y (err e , act a r) ((inj₁ i , inj₁ j) , k , inj₂ v) =
  ((inj₂ v) , (inj₁ tt)) , refl
ℙ-moncom-multℝ> A E X Y (ret y , err e) ((x , inj₁ j) , k , inj₂ tt) =
  ((inj₂ tt) , (inj₁ tt)) , refl
ℙ-moncom-multℝ> A E X Y (act b r , err e) ((inj₁ x , inj₁ j) , k , inj₁ v) =
  (inj₁ v , inj₁ tt) , refl
ℙ-moncom-multℝ> A E X Y (act b r , err e) ((inj₁ x , inj₁ j) , k , inj₂ v) =
  (inj₂ v , inj₁ tt) , refl
ℙ-moncom-multℝ> A E X Y (err e , err f) ((inj₁ i , inj₁ j) , k , inj₁ v) =
  ((inj₁ tt) , (inj₁ tt)) , refl
ℙ-moncom-multℝ> A E X Y (err e , err f) ((inj₁ i , inj₁ j) , k , inj₂ v) =
  ((inj₂ tt) , (inj₁ tt)) , refl


ℙ-moncom-mult : (A E X Y : Set) → SF≡ (SF-∘ (ℙ A E X Y) (SF-T-δ A E (X × Y)))
  (SF-∘ (SF-T-δ A E X ⊗ SF-T-δ A E Y) (SF-∘ (ℙ A E _ _) (SF-T A E (ℙ A E X Y))))
ℙ-moncom-mult A E X Y = (ℙ-moncom-mult< A E X Y) , (ℙ-moncom-mult> A E X Y)




-- Interaction law equations
IL-unit-𝕃 : (A E X Y : Set) → SF≡ (SF-∘ (SF-T-η A E X ⊗ SF-id _) (𝕃 A E X Y))
                                   (SF-∘ (SF-id _ ⊗ SF-T-ε A E Y) (SF-T-η A E _))
proj₁ (IL-unit-𝕃 A E X Y) (x , ret y) i = ((tt , tt) , tt) , refl
proj₂ (IL-unit-𝕃 A E X Y) (x , ret y) i = ((tt , tt) , tt) , refl


IL-mult-𝕃 : (A E X Y : Set) → SF≡ (SF-∘ (SF-T-μ A E X ⊗ SF-id _) (𝕃 A E X Y))
  (SF-∘ (SF-id _ ⊗ SF-T-δ A E Y) (SF-∘ (𝕃 A E _ _)
        (SF-∘ (SF-T A E (𝕃 A E X Y)) (SF-T-μ A E _)))) 
IL-mult-ℙ : (A E X Y : Set) → SF≡ (SF-∘ (SF-T-μ A E X ⊗ SF-id _) (ℙ A E X Y))
  (SF-∘ (SF-id _ ⊗ SF-T-δ A E Y) (SF-∘ (ℙ A E _ _)
        (SF-∘ (SF-T A E (𝕃 A E X Y)) (SF-T-μ A E _)))) 
IL-mult-ℝ< : (A E X Y : Set) → SF≤ (SF-∘ (SF-T-μ A E X ⊗ SF-id _) (ℝ A E X Y))
  (SF-∘ (SF-id _ ⊗ SF-T-δ A E Y) (SF-∘ (ℙ A E _ _)
        (SF-∘ (SF-T A E (𝕃 A E X Y)) (SF-T-μ A E _))))
IL-mult-ℝ> : (A E X Y : Set) → SF≤ (SF-∘ (SF-id _ ⊗ SF-T-δ A E Y) (SF-∘ (ℝ A E _ _)
        (SF-∘ (SF-T A E (𝕃 A E X Y)) (SF-T-μ A E _))))
        (SF-∘ (SF-T-μ A E X ⊗ SF-id _) (ℙ A E X Y))

proj₁ (IL-mult-𝕃 A E X Y) (ret t , ret y) ((tt , tt) , i) =
  ((tt , tt) , (tt , (i , tt))) , refl
proj₁ (IL-mult-𝕃 A E X Y) (ret t , act a r) ((tt , tt) , i) =
  ((tt , (inj₁ tt)) , (tt , (i , tt))) , refl
proj₁ (IL-mult-𝕃 A E X Y) (ret t , err e) ((tt , tt) , i) =
  ((tt , (inj₁ tt)) , (tt , (i , tt))) , refl
proj₁ (IL-mult-𝕃 A E X Y) (act a d , r) ((tt , tt) , i)
  with proj₁ (IL-mult-ℙ A E X Y) (d , r) ((tt , tt) , i)
... | (u , v) , w = (u , v) , cong (act a) w
proj₁ (IL-mult-𝕃 A E X Y) (err e , r) ((tt , tt) , i) = ((tt , (SF-T-δ-Total A E Y r)) ,
  (tt , (tt , tt))) , refl 
proj₂ (IL-mult-𝕃 A E X Y) (ret t , ret y) (i , j , k , l) = ((tt , tt) , k) , refl
proj₂ (IL-mult-𝕃 A E X Y) (ret t , act a r) ((tt , inj₁ tt) , j , k , l) =
  ((tt , tt) , k) , refl
proj₂ (IL-mult-𝕃 A E X Y) (ret t , err e) ((tt , inj₁ tt) , j , k , l) =
  ((tt , tt) , k) , refl
proj₂ (IL-mult-𝕃 A E X Y) (act a d , r) ((tt , i) , j , k , l)
  with proj₂ (IL-mult-ℙ A E X Y) (d , r) ((tt , i) , (j , (k , l)))
... | (u , v) , eq = (u , v) , cong (act a) eq
proj₂ (IL-mult-𝕃 A E X Y) (err e , r) ((tt , i) , j , k , l) = ((tt , tt) , tt) , refl

proj₁ (IL-mult-ℙ A E X Y) (d , r) ((tt , tt) , inj₁ i)
  with proj₁ (IL-mult-𝕃 A E X Y) (d , r) ((tt , tt) , i)
... | (u , v , w) , eq = (u , ((inj₁ v) , w)) , eq
proj₁ (IL-mult-ℙ A E X Y) (d , r) ((tt , tt) , inj₂ i) =
  IL-mult-ℝ< A E X Y (d , r) ((tt , tt) , i)
proj₂ (IL-mult-ℙ A E X Y) (d , r) (i , inj₁ j , p)
   with proj₂ (IL-mult-𝕃 A E X Y) (d , r) (i , (j , p))
... | ((tt , tt) , u) , eq = ((tt , tt) , (inj₁ u)) , eq
proj₂ (IL-mult-ℙ A E X Y) (d , r) ((tt , i) , inj₂ j , p , tt) =
  IL-mult-ℝ> A E X Y (d , r) ((tt , i) , (j , (p , tt)))


IL-mult-ℝ< A E X Y (d , act a r) ((tt , tt) , i)
  with proj₁ (IL-mult-ℙ A E X Y) (d , r) ((tt , tt) , i)
... | ((tt , u) , v , k , l) , eq = ((tt , inj₂ u) , inj₂ v , k , l) , cong (act a) eq
IL-mult-ℝ< A E X Y (d , err e) ((tt , tt) , i) =
  ((tt , (inj₂ tt)) , (inj₂ tt , tt , tt)) , refl
IL-mult-ℝ< A E X Y (ret (ret x) , ret y) ((tt , tt) , i) =
  ((tt , tt) , ((inj₂ tt) , (tt , tt))) , refl
IL-mult-ℝ> A E X Y (d , act a r) ((tt , inj₂ i) , j , p , tt)
  with proj₂ (IL-mult-ℙ A E X Y) (d , r) ((tt , i) , (j , (p , tt)))
... | ((tt , tt) , k) , eq = ((tt , tt) , inj₂ k) , cong (act a) eq
IL-mult-ℝ> A E X Y (d , err e) ((tt , inj₂ tt) , j , p , tt) = ((tt , tt) , (inj₂ tt)) , refl
IL-mult-ℝ> A E X Y (ret t , ret y) ((tt , i) , j , p , tt) = ((tt , tt) , (inj₁ p)) , refl
IL-mult-ℝ> A E X Y (ret t , act a r) ((tt , inj₁ tt) , j , p , tt) =
  ((tt , tt) , (inj₁ p)) , refl
IL-mult-ℝ> A E X Y (ret t , err e) ((tt , inj₁ tt) , j , p , tt) =
  ((tt , tt) , (inj₁ p)) , refl

