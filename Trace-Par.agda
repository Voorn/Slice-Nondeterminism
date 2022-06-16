module Trace-Par where

open import Data.Unit
open import Data.Empty
open import Data.Sum renaming (map to map⊎)
open import Data.Nat hiding (_⊔_)
open import Data.Product renaming (map to map×)
open import Relation.Binary.PropositionalEquality hiding ([_])


open import Index-Nondeterminism
open import Monoidal
open import Free-Monad
open import Trace




-- Paralel operator
ℙ : (A E : Set) → (X Y : Set)
  → PK-Hom ((Trace A E X) × (Trace A E Y)) (Trace A E (X × Y))

𝕃 : (A E : Set) → (X Y : Set)
  → PK-Hom ((Trace A E X) × (Trace A E Y)) (Trace A E (X × Y))

ℝ : (A E : Set) → (X Y : Set)
  → PK-Hom ((Trace A E X) × (Trace A E Y)) (Trace A E (X × Y))

ℙ A E X Y p = join (𝕃 A E X Y p) (ℝ A E X Y p)

𝕃 A E X Y (ret x , ret y) = PK-Id _ (ret (x , y))
𝕃 A E X Y (ret x , act b r) = Pow-⊥ _
𝕃 A E X Y (ret x , err e) = Pow-⊥ _
𝕃 A E X Y (act a l , r) = Pow-act a (X × Y) (ℙ A E X Y (l , r))
𝕃 A E X Y (err e , r) = PK-Id _ (err e)


ℝ A E X Y (l , act b r) = Pow-act b (X × Y) (ℙ A E X Y (l , r))
ℝ A E X Y (l , err e) = PK-Id _ (err e)
ℝ A E X Y (ret x , ret y) = PK-Id _ (ret (x , y))
ℝ A E X Y (act a l , ret y) = Pow-⊥ _
ℝ A E X Y (err e , ret y) = Pow-⊥ _


ℙ-Total : (A E X Y : Set) → PK-Total (ℙ A E X Y)
ℙ-Total A E X Y (ret x , ret y) = inj₁ tt
ℙ-Total A E X Y (ret x , act a r) = inj₂ (ℙ-Total A E X Y (ret x , r))
ℙ-Total A E X Y (ret x , err e) = inj₂ tt
ℙ-Total A E X Y (act a l , r) = inj₁ (ℙ-Total A E X Y (l , r))
ℙ-Total A E X Y (err e , r) = inj₁ tt


-- < holds without totality, > needs totality
ℙ-T-nat : (A E : Set) → {X X' Y Y' : Set} → (f : PK-Hom X X') → (g : PK-Hom Y Y')
  → PK-Total f → PK-Total g → PK-≡ (PK-∘ (PK-T A E f ⊗ PK-T A E g) (ℙ A E X' Y'))
                                   (PK-∘ (ℙ A E X Y) (PK-T A E (f ⊗ g)))
𝕃-T-nat : (A E : Set) → {X X' Y Y' : Set} → (f : PK-Hom X X') → (g : PK-Hom Y Y')
  → PK-Total f → PK-Total g → PK-≡ (PK-∘ (PK-T A E f ⊗ PK-T A E g) (𝕃 A E X' Y'))
                                   (PK-∘ (𝕃 A E X Y) (PK-T A E (f ⊗ g)))
ℝ-T-nat : (A E : Set) → {X X' Y Y' : Set} → (f : PK-Hom X X') → (g : PK-Hom Y Y')
  → PK-Total f → PK-Total g → PK-≡ (PK-∘ (PK-T A E f ⊗ PK-T A E g) (ℝ A E X' Y'))
                                   (PK-∘ (ℝ A E X Y) (PK-T A E (f ⊗ g)))

proj₁ (ℙ-T-nat A E f g f-tot g-tot) (l , r) (i , inj₁ j)
  with proj₁ (𝕃-T-nat A E f g f-tot g-tot) (l , r) (i , j)
... | (u , v) , eq = (inj₁ u , v) , eq
proj₁ (ℙ-T-nat A E f g f-tot g-tot) (l , r) (i , inj₂ j)
  with proj₁ (ℝ-T-nat A E f g f-tot g-tot) (l , r) (i , j)
... | (u , v) , eq = (inj₂ u , v) , eq
proj₂ (ℙ-T-nat A E f g f-tot g-tot) (l , r) (inj₁ i , j)
  with proj₂ (𝕃-T-nat A E f g f-tot g-tot) (l , r) (i , j)
... | (u , v) , eq = (u , inj₁ v) , eq
proj₂ (ℙ-T-nat A E f g f-tot g-tot) (l , r) (inj₂ i , j)
  with proj₂ (ℝ-T-nat A E f g f-tot g-tot) (l , r) (i , j)
... | (u , v) , eq = (u , inj₂ v) , eq

proj₁ (𝕃-T-nat A E f g f-tot g-tot) (ret x , ret y) ((i , j) , p) = (tt , (i , j)) , refl
proj₁ (𝕃-T-nat A E f g f-tot g-tot) (act a l , r) ((i , j) , p)
  with proj₁ (ℙ-T-nat A E f g f-tot g-tot) (l , r) ((i , j) , p)
... | u , eq = u , cong (act a) eq
proj₁ (𝕃-T-nat A E f g f-tot g-tot) (err e , r) ((i , j) , p) = (tt , tt) , refl
proj₂ (𝕃-T-nat A E f g f-tot g-tot) (ret x , ret y) (i , j) = (j , tt) , refl
proj₂ (𝕃-T-nat A E f g f-tot g-tot) (act a l , r) (i , j)
  with proj₂ (ℙ-T-nat A E f g f-tot g-tot) (l , r) (i , j)
... | u , eq = u , (cong (act a) eq)
proj₂ (𝕃-T-nat A E f g f-tot g-tot) (err e , r) (i , j) =
  ((tt , (PK-T-Total A E g g-tot r)) , tt) , refl

proj₁ (ℝ-T-nat A E f g f-tot g-tot) (l , act a r) ((i , j) , p)
  with proj₁ (ℙ-T-nat A E f g f-tot g-tot) (l , r) ((i , j) , p)
... | u , eq = u , cong (act a) eq
proj₁ (ℝ-T-nat A E f g f-tot g-tot) (l , err e) ((i , j) , p) = (tt , tt) , refl
proj₁ (ℝ-T-nat A E f g f-tot g-tot) (ret x , ret y) ((i , j) , p) =
  (tt , (i , j)) , refl
proj₂ (ℝ-T-nat A E f g f-tot g-tot) (l , act a r) (i , j)
  with proj₂ (ℙ-T-nat A E f g f-tot g-tot) (l , r) (i , j)
... | u , eq = u , (cong (act a) eq)
proj₂ (ℝ-T-nat A E f g f-tot g-tot) (l , err e) (i , j) =
  ((PK-T-Total A E f f-tot l , tt) , tt) , refl
proj₂ (ℝ-T-nat A E f g f-tot g-tot) (ret x , ret y) (i , j) = (j , tt) , refl



ℙ-σ : (A E X Y : Set) → PK-≡ (PK-∘ (PK-T-η A E X ⊗ PK-Id _) (ℙ A E X Y))
                                        (PK-T-σ A E X Y)

proj₁ (ℙ-σ A E X Y) (x , ret y) ((tt , tt) , inj₁ tt) = tt , refl
proj₁ (ℙ-σ A E X Y) (x , ret y) ((tt , tt) , inj₂ tt) = tt , refl
proj₁ (ℙ-σ A E X Y) (x , act a r) ((tt , tt) , inj₂ i)
  with proj₁ (ℙ-σ A E X Y) (x , r) ((tt , tt) , i)
... | tt , eq = tt , (cong (act a) eq)
proj₁ (ℙ-σ A E X Y) (x , err e) ((tt , tt) , inj₂ tt) = tt , refl

proj₂ (ℙ-σ A E X Y) (x , ret y) tt = ((tt , tt) , (inj₁ tt)) , refl
proj₂ (ℙ-σ A E X Y) (x , act a r) tt
  with proj₂ (ℙ-σ A E X Y) (x , r) tt
... | ((tt , tt) , w) , eq = ((tt , tt) , inj₂ w) , cong (act a) eq
proj₂ (ℙ-σ A E X Y) (x , err e) tt = ((tt , tt) , (inj₂ tt)) , refl



𝕃ℝ-γ : (A E X Y : Set) → PK-≡ (PK-∘ (𝕃 A E X Y) (PK-T A E (⊗-γ X Y)))
                                   (PK-∘ (⊗-γ (Trace A E X) (Trace A E Y)) (ℝ A E Y X))
ℝ𝕃-γ : (A E X Y : Set) → PK-≡ (PK-∘ (ℝ A E X Y) (PK-T A E (⊗-γ X Y)))
                                   (PK-∘ (⊗-γ (Trace A E X) (Trace A E Y)) (𝕃 A E Y X))
ℙ-γ : (A E X Y : Set) → PK-≡ (PK-∘ (ℙ A E X Y) (PK-T A E (⊗-γ X Y)))
                                  (PK-∘ (⊗-γ (Trace A E X) (Trace A E Y)) (ℙ A E Y X))
proj₁ (𝕃ℝ-γ A E X Y) (ret x , ret y) (i , j) = (tt , tt) , refl
proj₁ (𝕃ℝ-γ A E X Y) (act a l , r) (i , j)
  with proj₁ (ℙ-γ A E X Y) (l , r) (i , j)
... | u , v = u , (cong (act a) v)
proj₁ (𝕃ℝ-γ A E X Y) (err e , r) (tt , tt) = (tt , tt) , refl
proj₂ (𝕃ℝ-γ A E X Y) (ret x , ret y) (tt , tt) = (tt , tt) , refl
proj₂ (𝕃ℝ-γ A E X Y) (act a l , r) (tt , i)
  with proj₂ (ℙ-γ A E X Y) (l , r) (tt , i)
... | u , v = u , cong (act a) v
proj₂ (𝕃ℝ-γ A E X Y) (err e , r) (tt , tt) = (tt , tt) , refl

proj₁ (ℝ𝕃-γ A E X Y) (l , act a r) (i , j)
  with proj₁ (ℙ-γ A E X Y) (l , r) (i , j)
... | u , v = u , (cong (act a) v)
proj₁ (ℝ𝕃-γ A E X Y) (l , err e) (tt , tt) = (tt , tt) , refl
proj₁ (ℝ𝕃-γ A E X Y) (ret x , ret y) (i , j) = (tt , tt) , refl
proj₂ (ℝ𝕃-γ A E X Y) (l , act a r) (tt , i)
  with proj₂ (ℙ-γ A E X Y) (l , r) (tt , i)
... | u , v = u , cong (act a) v
proj₂ (ℝ𝕃-γ A E X Y) (l , err e) (tt , tt) = (tt , tt) , refl
proj₂ (ℝ𝕃-γ A E X Y) (ret x , ret y) (tt , tt) = (tt , tt) , refl

proj₁ (ℙ-γ A E X Y) (l , r) (inj₁ i , j)
  with proj₁ (𝕃ℝ-γ A E X Y) (l ,  r) (i , j)
... | (tt , u) , w = (tt , (inj₂ u)) , w
proj₁ (ℙ-γ A E X Y) (l , r) (inj₂ i , j)
  with proj₁ (ℝ𝕃-γ A E X Y) (l ,  r) (i , j)
... | (tt , u) , w = (tt , (inj₁ u)) , w
proj₂ (ℙ-γ A E X Y) (l , r) (tt , inj₁ i)
  with proj₂ (ℝ𝕃-γ A E X Y) (l ,  r) (tt , i)
... | (u , v) , eq = ((inj₂ u) , v) , eq
proj₂ (ℙ-γ A E X Y) (l , r) (tt , inj₂ i)
  with proj₂ (𝕃ℝ-γ A E X Y) (l ,  r) (tt , i)
... | (u , v) , eq = ((inj₁ u) , v) , eq


-- associativity
ℙ-α : (A E X Y Z : Set) → PK-≡ (PK-∘ (PK-Id _ ⊗ ℙ A E Y Z) (ℙ A E X (Y × Z)))
  (PK-∘ (⊗-α' _ _ _) (PK-∘ (ℙ A E X Y ⊗ PK-Id _)
        (PK-∘ (ℙ A E (X × Y) Z) (PK-T A E (⊗-α X Y Z)))))
𝕃-α : (A E X Y Z : Set) → PK-≡ (PK-∘ (PK-Id _ ⊗ ℙ A E Y Z) (𝕃 A E X (Y × Z)))
  (PK-∘ (⊗-α' _ _ _) (PK-∘ (𝕃 A E X Y ⊗ PK-Id _)
        (PK-∘ (𝕃 A E (X × Y) Z) (PK-T A E (⊗-α X Y Z)))))
𝕄-α : (A E X Y Z : Set) → PK-≡ (PK-∘ (PK-Id _ ⊗ 𝕃 A E Y Z) (ℝ A E X (Y × Z)))
  (PK-∘ (⊗-α' _ _ _) (PK-∘ (ℝ A E X Y ⊗ PK-Id _)
        (PK-∘ (𝕃 A E (X × Y) Z) (PK-T A E (⊗-α X Y Z)))))
ℝ-α : (A E X Y Z : Set) → PK-≡ (PK-∘ (PK-Id _ ⊗ ℝ A E Y Z) (ℝ A E X (Y × Z)))
  (PK-∘ (⊗-α' _ _ _) (PK-∘ (ℙ A E X Y ⊗ PK-Id _)
        (PK-∘ (ℝ A E (X × Y) Z) (PK-T A E (⊗-α X Y Z)))))

proj₁ (ℙ-α A E X Y Z) (l , m , r) ((tt , i) , inj₁ j)
  with proj₁ (𝕃-α A E X Y Z) (l , m , r) ((tt , i) , j)
... | (tt , (u , tt) , v , w) , eq = (tt , ((inj₁ u , tt) , inj₁ v , w)) , eq
proj₁ (ℙ-α A E X Y Z) (l , m , r) ((tt , inj₁ i) , inj₂ j)
    with proj₁ (𝕄-α A E X Y Z) (l , m , r) ((tt , i) , j)
... | (tt , (u , tt) , v , w) , eq = (tt , ((inj₂ u , tt) , inj₁ v , w)) , eq
proj₁ (ℙ-α A E X Y Z) (l , m , r) ((tt , inj₂ i) , inj₂ j)
    with proj₁ (ℝ-α A E X Y Z) (l , m , r) ((tt , i) , j)
... | (tt , (u , tt) , v , w) , eq = (tt , ((u , tt) , inj₂ v , w)) , eq
proj₂ (ℙ-α A E X Y Z) (l , m , r) (tt , (inj₂ i , tt) , inj₁ j , p)
  with proj₂ (𝕄-α A E X Y Z) (l , m , r) (tt , (i , tt) , j , p)
... | ((tt , u) , v) , eq = ((tt , inj₁ u) , (inj₂ v)) , eq
proj₂ (ℙ-α A E X Y Z) (l , m , r) (tt , (inj₁ i , tt) , inj₁ j , p)
  with proj₂ (𝕃-α A E X Y Z) (l , m , r) (tt , (i , tt) , j , p)
... | ((tt , u) , v) , eq = ((tt , u) , (inj₁ v)) , eq
proj₂ (ℙ-α A E X Y Z) (l , m , r) (tt , (inj₁ i , tt) , inj₂ j , p)
  with proj₂ (ℝ-α A E X Y Z) (l , m , r) (tt , (inj₁ i , tt) , j , p)
... | ((tt , u) , v) , eq = ((tt , inj₂ u) , (inj₂ v)) , eq
proj₂ (ℙ-α A E X Y Z) (l , m , r) (tt , (inj₂ i , tt) , inj₂ j , p)
  with proj₂ (ℝ-α A E X Y Z) (l , m , r) (tt , (inj₂ i , tt) , j , p)
... | ((tt , u) , v) , eq = ((tt , inj₂ u) , (inj₂ v)) , eq

proj₁ (𝕃-α A E X Y Z) (ret x , ret y , ret z) ((tt , inj₁ i) , j) =
  (tt , ((tt , tt) , (tt , tt))) , refl
proj₁ (𝕃-α A E X Y Z) (ret x , ret y , ret z) ((tt , inj₂ i) , j) =
  (tt , ((tt , tt) , (tt , tt))) , refl
proj₁ (𝕃-α A E X Y Z) (act a l , m , r) ((tt , i) , j)
  with proj₁ (ℙ-α A E X Y Z) (l , m , r) ((tt , i) , j)
... | (tt , (u , tt) , v , w) , eq = (tt , ((u , tt) , v , w)) , cong (act a) eq
proj₁ (𝕃-α A E X Y Z) (err e , m , r) ((tt , i) , j) = (tt , ((tt , tt) , (tt , tt))) , refl
proj₂ (𝕃-α A E X Y Z) (ret x , ret y , ret z) (tt , (i , tt) , j , p) =
  ((tt , (inj₁ tt)) , tt) , refl
proj₂ (𝕃-α A E X Y Z) (act a l , m , r) i
  with proj₂ (ℙ-α A E X Y Z) (l , m , r) i
... | ((tt , u) , v) , eq = ((tt , u) , v) , (cong (act a) eq)
proj₂ (𝕃-α A E X Y Z) (err e , m , r) (tt , (i , tt) , j , p) =
  ((tt , (ℙ-Total A E Y Z (m , r))) , tt) , refl

proj₁ (𝕄-α A E X Y Z) (l , act a m , r) ((tt , i) , j)
    with proj₁ (ℙ-α A E X Y Z) (l , m , r) ((tt , i) , j)
... | (tt , (u , tt) , v , w) , eq = (tt , ((u , tt) , v , w)) , cong (act a) eq
proj₁ (𝕄-α A E X Y Z) (l , err e , r) ((tt , i) , j) = (tt , ((tt , tt) , (tt , tt))) , refl
proj₁ (𝕄-α A E X Y Z) (ret x , ret y , ret z) ((tt , i) , j) =
  (tt , ((tt , tt) , (tt , tt))) , refl
proj₁ (𝕄-α A E X Y Z) (act a l , ret y , ret z) ((tt , i) , ())
proj₁ (𝕄-α A E X Y Z) (err e , ret y , ret z) ((tt , i) , ())
proj₂ (𝕄-α A E X Y Z) (l , act a m , r) i
  with proj₂ (ℙ-α A E X Y Z) (l , m , r) i
... | ((tt , u) , v) , eq = ((tt , u) , v) , (cong (act a) eq)
proj₂ (𝕄-α A E X Y Z) (l , err e , r) (tt , (i , tt) , j , p) =
  ((tt , tt) , tt) , refl
proj₂ (𝕄-α A E X Y Z) (ret x , ret y , ret z) (tt , (i , tt) , j , p) =
  ((tt , tt) , tt) , refl

proj₁ (ℝ-α A E X Y Z) (l , m , act a r) ((tt , i) , j)
    with proj₁ (ℙ-α A E X Y Z) (l , m , r) ((tt , i) , j)
... | (tt , (u , tt) , v , w) , eq = (tt , ((u , tt) , v , w)) , cong (act a) eq
proj₁ (ℝ-α A E X Y Z) (l , m , err e) ((tt , i) , j) = (tt , (((ℙ-Total A E X Y (l , m)) ,
  tt) , (tt , tt))) , refl
proj₁ (ℝ-α A E X Y Z) (ret x , ret y , ret z) ((tt , i) , j) =
  (tt , (((inj₁ tt) , tt) , (tt , tt))) , refl
proj₁ (ℝ-α A E X Y Z) (act a l , ret y , ret z) ((tt , i) , ())
proj₁ (ℝ-α A E X Y Z) (err e , ret y , ret z) ((tt , i) , ())
proj₂ (ℝ-α A E X Y Z) (l , m , act a r) i
    with proj₂ (ℙ-α A E X Y Z) (l , m , r) i
... | ((tt , u) , v) , eq = ((tt , u) , v) , (cong (act a) eq)
proj₂ (ℝ-α A E X Y Z) (l , m , err e) (tt , (i , tt) , j , p) = ((tt , tt) , tt) , refl
proj₂ (ℝ-α A E X Y Z) (ret x , ret y , ret z) (tt , (inj₁ i , tt) , j , p) =
  ((tt , tt) , tt) , refl
proj₂ (ℝ-α A E X Y Z) (ret x , ret y , ret z) (tt , (inj₂ i , tt) , j , p) =
  ((tt , tt) , tt) , refl
proj₂ (ℝ-α A E X Y Z) (act a l , ret y , ret z) (tt , (inj₂ () , tt) , j , p)
proj₂ (ℝ-α A E X Y Z) (err e , ret y , ret z) (tt , (inj₂ () , tt) , j , p)
proj₂ (ℝ-α A E X Y Z) (l , act a m , ret z) (tt , (inj₂ (inj₁ x) , tt) , () , p)
proj₂ (ℝ-α A E X Y Z) (l , err e , ret z) (tt , (inj₂ i , tt) , () , p)

-- Pseudomonoidal
ℙ-monoid-unit : (A E X Y : Set) → PK-≡ (PK-∘ (PK-T-η A E X ⊗ PK-T-η A E Y) (ℙ A E X Y))
                                             (PK-T-η A E (X × Y))
ℙ-monoid-unit A E X Y = (λ { p (i , inj₁ tt) → tt , refl ; p (i , inj₂ tt) → tt , refl}) ,
                        λ x i → ((tt , tt) , (inj₁ tt)) , refl


ℙ-pseudo-mult : (A E X Y : Set)
  → Pow-< (PK-∘ (ℙ A E _ _) (PK-∘ (PK-T A E (ℙ A E X Y)) (PK-T-μ A E _)))
          (PK-∘ (PK-T-μ A E X ⊗ PK-T-μ A E Y) (ℙ A E X Y))
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


-- Monoidal comonad

ℙ-moncom-mult : (A E X Y : Set) → PK-≡ (PK-∘ (ℙ A E X Y) (PK-T-δ A E (X × Y)))
  (PK-∘ (PK-T-δ A E X ⊗ PK-T-δ A E Y) (PK-∘ (ℙ A E _ _) (PK-T A E (ℙ A E X Y))))
proj₁ (ℙ-moncom-mult A E X Y) (ret x , ret y) (inj₁ i , j) =
  ((tt , tt) , ((inj₁ tt) , (inj₁ tt))) , refl
proj₁ (ℙ-moncom-mult A E X Y) (act a l , ret y) (inj₁ i , inj₁ j) =
  (((inj₁ tt) , tt) , ((inj₁ tt) , (inj₁ i))) , refl
proj₁ (ℙ-moncom-mult A E X Y) (act a l , act b r) (inj₁ i , inj₁ j) =
  (((inj₁ tt) , inj₁ tt) , (inj₁ tt) , (inj₁ i)) , refl
proj₁ (ℙ-moncom-mult A E X Y) (act a l , err e) (inj₁ i , inj₁ j) =
  (((inj₁ tt) , inj₁ tt) , (inj₁ tt) , (inj₁ i)) , refl
proj₁ (ℙ-moncom-mult A E X Y) (act a l , r) (inj₁ i , inj₂ j)
  with proj₁ (ℙ-moncom-mult A E X Y) (l , r) (i , j)
... | ((u , v) , (w , p)) , eq = ((inj₂ u  , v) , inj₁ w , p) , cong (act a) eq
proj₁ (ℙ-moncom-mult A E X Y) (err e , ret y) (inj₁ i , inj₁ x) =
  (((inj₁ tt) , tt) , ((inj₁ tt) , (inj₁ tt))) , refl
proj₁ (ℙ-moncom-mult A E X Y) (err e , act a r) (inj₁ i , inj₁ x) =
  (((inj₁ tt) , (inj₁ tt)) , ((inj₁ tt) , (inj₁ tt))) , refl
proj₁ (ℙ-moncom-mult A E X Y) (err e , err v) (inj₁ i , inj₁ x) =
  (((inj₁ tt ) , (inj₁ tt)) , ((inj₁ tt) , (inj₁ tt))) , refl
proj₁ (ℙ-moncom-mult A E X Y) (err e , r) (inj₁ i , inj₂ y) =
  (((inj₂ tt) , PK-T-δ-Total A E Y r) , (inj₁ tt) , tt) , refl
proj₁ (ℙ-moncom-mult A E X Y) (ret x , ret y) (inj₂ i , j) =
  ((tt , tt) , ((inj₁ tt) , (inj₁ tt))) , refl
proj₁ (ℙ-moncom-mult A E X Y) (ret y , act a l) (inj₂ i , inj₁ j) =
  ((tt , (inj₁ tt)) , ((inj₁ tt) , (inj₂ i))) , refl
proj₁ (ℙ-moncom-mult A E X Y) (act a l , act b r) (inj₂ i , inj₁ j) =
  (((inj₁ tt) , inj₁ tt) , (inj₁ tt) , (inj₂ i)) , refl
proj₁ (ℙ-moncom-mult A E X Y) (err e , act b r) (inj₂ i , inj₁ j) =
  (((inj₁ tt) , inj₁ tt) , (inj₁ tt) , (inj₂ i)) , refl
proj₁ (ℙ-moncom-mult A E X Y) (l , act a r) (inj₂ i , inj₂ j)
  with proj₁ (ℙ-moncom-mult A E X Y) (l , r) (i , j)
... | ((u , v) , (w , p)) , eq = ((u , inj₂ v) , inj₂ w , p) , cong (act a) eq
proj₁ (ℙ-moncom-mult A E X Y) (ret x , err e) (inj₂ i , inj₁ x) =
  ((tt , (inj₁ tt)) , ((inj₁ tt) , (inj₂ tt))) , refl
proj₁ (ℙ-moncom-mult A E X Y) (act a r , err e) (inj₂ i , inj₁ x) =
  (((inj₁ tt) , (inj₁ tt)) , ((inj₁ tt) , (inj₂ tt))) , refl
proj₁ (ℙ-moncom-mult A E X Y) (err e , err v) (inj₂ i , inj₁ x) =
  (((inj₁ tt ) , (inj₁ tt)) , ((inj₁ tt) , (inj₂ tt))) , refl
proj₁ (ℙ-moncom-mult A E X Y) (r , err e) (inj₂ i , inj₂ y) =
  ((PK-T-δ-Total A E X r , (inj₂ tt)) , (inj₂ tt) , tt) , refl



proj₂ (ℙ-moncom-mult A E X Y) (act a t , r) ((inj₂ i , j) , inj₁ k , v)
  with proj₂ (ℙ-moncom-mult A E X Y) (t , r) ((i , j) , k , v)
... | (u , w) , eq = ((inj₁ u) , (inj₂ w)) , (cong (act a) eq)
proj₂ (ℙ-moncom-mult A E X Y) (err e , r) ((inj₂ y , j) , inj₁ k , v) = ((inj₁ tt) , (inj₂ tt)) , refl
proj₂ (ℙ-moncom-mult A E X Y) (ret x , ret y) ((i , j) , inj₁ k , inj₁ tt) = ((inj₁ tt) , tt) , refl
proj₂ (ℙ-moncom-mult A E X Y) (ret x , ret y) ((i , j) , inj₁ k , inj₂ tt) = ((inj₁ tt) , tt) , refl
proj₂ (ℙ-moncom-mult A E X Y) (ret x , act a r) ((i , inj₁ j) , inj₁ k , inj₂ y) = ((inj₂ y) , (inj₁ tt)) , refl
proj₂ (ℙ-moncom-mult A E X Y) (ret x , err e) ((i , inj₁ j) , inj₁ k , inj₂ tt) = ((inj₂ tt) , (inj₁ tt)) , refl
proj₂ (ℙ-moncom-mult A E X Y) (act a t , ret y) ((inj₁ i , j) , inj₁ k , inj₁ v) = (inj₁ v , inj₁ tt) , refl
proj₂ (ℙ-moncom-mult A E X Y) (act a t , act b r) ((inj₁ i , inj₁ x) , inj₁ k , inj₁ v) = ((inj₁ v) , (inj₁ tt)) , refl
proj₂ (ℙ-moncom-mult A E X Y) (act a t , act b r) ((inj₁ i , inj₁ x) , inj₁ k , inj₂ v) = ((inj₂ v) , (inj₁ tt)) , refl
proj₂ (ℙ-moncom-mult A E X Y) (act a t , err e) ((inj₁ i , inj₁ j) , inj₁ k , inj₁ v) = ((inj₁ v) , (inj₁ tt)) , refl
proj₂ (ℙ-moncom-mult A E X Y) (act a t , err e) ((inj₁ i , inj₁ j) , inj₁ k , inj₂ v) = ((inj₂ v) , (inj₁ tt)) , refl
proj₂ (ℙ-moncom-mult A E X Y) (err e , ret y) ((inj₁ x , j) , inj₁ k , inj₁ tt) = ((inj₁ tt) , (inj₁ tt)) , refl
proj₂ (ℙ-moncom-mult A E X Y) (err e , act b r) ((inj₁ x , inj₁ j) , inj₁ k , inj₁ v) = (inj₁ v , inj₁ tt) , refl
proj₂ (ℙ-moncom-mult A E X Y) (err e , act b r) ((inj₁ x , inj₁ j) , inj₁ k , inj₂ v) = (inj₂ v , inj₁ tt) , refl
proj₂ (ℙ-moncom-mult A E X Y) (err e , err f) ((inj₁ i , inj₁ j) , inj₁ k , inj₁ v) = ((inj₁ tt) , (inj₁ tt)) , refl
proj₂ (ℙ-moncom-mult A E X Y) (err e , err f) ((inj₁ i , inj₁ j) , inj₁ k , inj₂ v) = ((inj₂ tt) , (inj₁ tt)) , refl

proj₂ (ℙ-moncom-mult A E X Y) (ret x , ret y) ((i , j) , inj₂ k , inj₁ tt) = ((inj₁ tt) , tt) , refl
proj₂ (ℙ-moncom-mult A E X Y) (ret x , ret y) ((i , j) , inj₂ k , inj₂ tt) = ((inj₁ tt) , tt) , refl
proj₂ (ℙ-moncom-mult A E X Y) (act a l , ret x) ((inj₁ i , j) , inj₂ k , inj₁ y) = ((inj₁ y) , inj₁ tt) , refl
proj₂ (ℙ-moncom-mult A E X Y) (err e , ret x) ((inj₁ i , j) , inj₂ k , inj₁ tt) = ((inj₁ tt) , (inj₁ tt)) , refl
proj₂ (ℙ-moncom-mult A E X Y) (ret x , act a r) ((i , inj₁ j) , inj₂ k , inj₂ v) = (inj₂ v , inj₁ tt) , refl
proj₂ (ℙ-moncom-mult A E X Y) (act a t , act b r) ((inj₁ i , inj₁ x) , inj₂ k , inj₁ v) = ((inj₁ v) , (inj₁ tt)) , refl
proj₂ (ℙ-moncom-mult A E X Y) (act a t , act b r) ((inj₁ i , inj₁ x) , inj₂ k , inj₂ v) = ((inj₂ v) , (inj₁ tt)) , refl
proj₂ (ℙ-moncom-mult A E X Y) (err e , act a r) ((inj₁ i , inj₁ j) , inj₂ k , inj₁ v) = ((inj₁ v) , (inj₁ tt)) , refl
proj₂ (ℙ-moncom-mult A E X Y) (err e , act a r) ((inj₁ i , inj₁ j) , inj₂ k , inj₂ v) = ((inj₂ v) , (inj₁ tt)) , refl
proj₂ (ℙ-moncom-mult A E X Y) (ret y , err e) ((x , inj₁ j) , inj₂ k , inj₂ tt) = ((inj₂ tt) , (inj₁ tt)) , refl
proj₂ (ℙ-moncom-mult A E X Y) (act b r , err e) ((inj₁ x , inj₁ j) , inj₂ k , inj₁ v) = (inj₁ v , inj₁ tt) , refl
proj₂ (ℙ-moncom-mult A E X Y) (act b r , err e) ((inj₁ x , inj₁ j) , inj₂ k , inj₂ v) = (inj₂ v , inj₁ tt) , refl
proj₂ (ℙ-moncom-mult A E X Y) (err e , err f) ((inj₁ i , inj₁ j) , inj₂ k , inj₁ v) = ((inj₁ tt) , (inj₁ tt)) , refl
proj₂ (ℙ-moncom-mult A E X Y) (err e , err f) ((inj₁ i , inj₁ j) , inj₂ k , inj₂ v) = ((inj₂ tt) , (inj₁ tt)) , refl
proj₂ (ℙ-moncom-mult A E X Y) (r , err e) ((y , inj₂ j) , inj₂ k , v) = ((inj₂ tt) , (inj₂ tt)) , refl
proj₂ (ℙ-moncom-mult A E X Y) (l , act a r) ((i , inj₂ j) , inj₂ k , v)
  with proj₂ (ℙ-moncom-mult A E X Y) (l , r) ((i , j) , k , v)
... | (u , w) , eq = ((inj₂ u) , (inj₂ w)) , (cong (act a) eq)



-- Interaction law
IL-unit-𝕃 : (A E X Y : Set) → PK-≡ (PK-∘ (PK-T-η A E X ⊗ PK-Id _) (𝕃 A E X Y))
                                   (PK-∘ (PK-Id _ ⊗ PK-T-ε A E Y) (PK-T-η A E _))
proj₁ (IL-unit-𝕃 A E X Y) (x , ret y) i = ((tt , tt) , tt) , refl
proj₂ (IL-unit-𝕃 A E X Y) (x , ret y) i = ((tt , tt) , tt) , refl


IL-mult-𝕃 : (A E X Y : Set) → PK-≡ (PK-∘ (PK-T-μ A E X ⊗ PK-Id _) (𝕃 A E X Y))
  (PK-∘ (PK-Id _ ⊗ PK-T-δ A E Y) (PK-∘ (𝕃 A E _ _)
        (PK-∘ (PK-T A E (𝕃 A E X Y)) (PK-T-μ A E _)))) 
IL-mult-ℙ : (A E X Y : Set) → PK-≡ (PK-∘ (PK-T-μ A E X ⊗ PK-Id _) (ℙ A E X Y))
  (PK-∘ (PK-Id _ ⊗ PK-T-δ A E Y) (PK-∘ (ℙ A E _ _)
        (PK-∘ (PK-T A E (𝕃 A E X Y)) (PK-T-μ A E _)))) 
IL-mult-ℝ< : (A E X Y : Set) → Pow-< (PK-∘ (PK-T-μ A E X ⊗ PK-Id _) (ℝ A E X Y))
  (PK-∘ (PK-Id _ ⊗ PK-T-δ A E Y) (PK-∘ (ℙ A E _ _)
        (PK-∘ (PK-T A E (𝕃 A E X Y)) (PK-T-μ A E _))))
IL-mult-ℝ> : (A E X Y : Set) → Pow-< (PK-∘ (PK-Id _ ⊗ PK-T-δ A E Y) (PK-∘ (ℝ A E _ _)
        (PK-∘ (PK-T A E (𝕃 A E X Y)) (PK-T-μ A E _))))
        (PK-∘ (PK-T-μ A E X ⊗ PK-Id _) (ℙ A E X Y))

proj₁ (IL-mult-𝕃 A E X Y) (ret t , ret y) ((tt , tt) , i) =
  ((tt , tt) , (tt , (i , tt))) , refl
proj₁ (IL-mult-𝕃 A E X Y) (ret t , act a r) ((tt , tt) , i) =
  ((tt , (inj₁ tt)) , (tt , (i , tt))) , refl
proj₁ (IL-mult-𝕃 A E X Y) (ret t , err e) ((tt , tt) , i) =
  ((tt , (inj₁ tt)) , (tt , (i , tt))) , refl
proj₁ (IL-mult-𝕃 A E X Y) (act a d , r) ((tt , tt) , i)
  with proj₁ (IL-mult-ℙ A E X Y) (d , r) ((tt , tt) , i)
... | (u , v) , w = (u , v) , cong (act a) w
proj₁ (IL-mult-𝕃 A E X Y) (err e , r) ((tt , tt) , i) = ((tt , (PK-T-δ-Total A E Y r)) ,
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



-- -- Naturality
-- ℙ-nat : (A E : Set) → {X X' Y Y' : Set} → (f : PK-Hom X X') → (g : PK-Hom Y Y')
--   → PK-≡ (PK-∘ (PK-T A E f ⊗ PK-T A E g) (ℙ A E X' Y'))
--          (PK-∘ (ℙ A E X Y) (PK-T A E (f ⊗ g)))

-- 𝕃-nat : (A E : Set) → {X X' Y Y' : Set} → (f : PK-Hom X X') → (g : PK-Hom Y Y')
--   → PK-≡ (PK-∘ (PK-T A E f ⊗ PK-T A E g) (𝕃 A E X' Y'))
--          (PK-∘ (𝕃 A E X Y) (PK-T A E (f ⊗ g)))

-- ℝ-nat : (A E : Set) → {X X' Y Y' : Set} → (f : PK-Hom X X') → (g : PK-Hom Y Y')
--   → PK-≡ (PK-∘ (PK-T A E f ⊗ PK-T A E g) (ℝ A E X' Y'))
--          (PK-∘ (ℝ A E X Y) (PK-T A E (f ⊗ g)))

-- proj₁ (ℙ-nat A E f g) p (ij , inj₁ u) with proj₁ (𝕃-nat A E f g) p (ij , u)
-- ... | (v , w) , eq = ((inj₁ v) , w) , eq
-- proj₁ (ℙ-nat A E f g) p (ij , inj₂ u) with proj₁ (ℝ-nat A E f g) p (ij , u)
-- ... | (v , w) , eq = ((inj₂ v) , w) , eq
-- proj₂ (ℙ-nat A E f g) p (inj₁ u , i) with proj₂ (𝕃-nat A E f g) p (u , i)
-- ... | (v , w) , eq = (v , inj₁ w) , eq
-- proj₂ (ℙ-nat A E f g) p (inj₂ u , j) with proj₂ (ℝ-nat A E f g) p (u , j)
-- ... | (v , w) , eq = (v , inj₂ w) , eq

-- proj₁ (𝕃-nat A E f g) (ret x , ret y) (ij , tt) = (tt , ij) , refl
-- proj₁ (𝕃-nat A E f g) (act a l , r) =
--   Pow-act-< a (_ × _) _ _ (proj₁ (ℙ-nat A E f g) (l , r))
-- proj₂ (𝕃-nat A E f g) (ret x , ret y) (tt , ij) = (ij , tt) , refl
-- proj₂ (𝕃-nat A E f g) (act a l , r) =
--   Pow-act-< a (_ × _) _ _ (proj₂ (ℙ-nat A E f g) (l , r))

-- proj₁ (ℝ-nat A E f g) (l , act b r)  =
--   Pow-act-< b (_ × _) _ _ (proj₁ (ℙ-nat A E f g) (l , r))
-- proj₁ (ℝ-nat A E f g) (ret x , ret y) (ij , tt) = (tt , ij) , refl
-- proj₂ (ℝ-nat A E f g) (l , act b r) =
--   Pow-act-< b (_ × _) _ _ (proj₂ (ℙ-nat A E f g) (l , r))
-- proj₂ (ℝ-nat A E f g) (ret x , ret y) (tt , ij) = (ij , tt) , refl


-- -- Unit law
-- 𝕃-unit : (A E : Set) → (X Y : Set)
--   → PK-≡ (PK-∘ (PK-T-η A E X ⊗ PK-Id (Trace A E Y))  (𝕃 A E X Y))
--          (PK-∘ (PK-Id X ⊗ PK-T-ε A E Y) (PK-T-η A E (X × Y)))
-- proj₁ (𝕃-unit A E X Y) (x , ret y) ((tt , tt) , tt) = ((tt , tt) , tt) , refl
-- proj₂ (𝕃-unit A E X Y) (x , ret y) ((tt , tt) , tt) = ((tt , tt) , tt) , refl


-- -- Multiplication law
-- 𝕃-mult : (A E : Set) → (X Y : Set)
--   → PK-≡ (PK-∘ (PK-T-μ A E X ⊗ PK-Id (Trace A E Y))
--                (𝕃 A E X Y))
--          (PK-∘ (PK-Id (Trace A E (Trace A E X)) ⊗ PK-T-δ A E Y)
--          (PK-∘ (𝕃 A E (Trace A E X) (Trace A E Y))
--          (PK-∘ (PK-T A E (𝕃 A E X Y))
--                (PK-T-μ A E (X × Y)))))
-- 𝕃-mult' : (A E : Set) → (X Y : Set)
--   → PK-≡ (PK-∘ (PK-T-μ A E X ⊗ PK-Id (Trace A E Y))
--                (ℙ A E X Y))
--          (PK-∘ (PK-Id (Trace A E (Trace A E X)) ⊗ PK-T-δ A E Y)
--          (PK-∘ (ℙ A E (Trace A E X) (Trace A E Y))
--          (PK-∘ (PK-T A E (𝕃 A E X Y))
--                (PK-T-μ A E (X × Y)))))
-- proj₁ (𝕃-mult A E X Y) (ret l , ret y) ((tt , tt) , j) =
--   ((tt , tt) , (tt , (j , tt))) , refl
-- proj₁ (𝕃-mult A E X Y) (ret l , act b r) ((tt , tt) , j) =
--   ((tt , (inj₁ tt)) , (tt , (j , tt))) , refl
-- proj₁ (𝕃-mult A E X Y) (act a d , r) ((i , tt) , j)
--   with proj₁ (𝕃-mult' A E X Y) (d , r) ((i , tt) , j)
-- ... | u , eq = u , cong (act a) eq
-- proj₂ (𝕃-mult A E X Y) (ret l , ret y) ((tt , i) , j , k , v) = ((tt , tt) , k) , refl
-- proj₂ (𝕃-mult A E X Y) (ret l , act b r) ((tt , inj₁ tt) , j , k , v) =
--   ((tt , tt) , k) , refl
-- proj₂ (𝕃-mult A E X Y) (act a d , r) i
--   with proj₂ (𝕃-mult' A E X Y) (d , r) i
-- ... | ((p , tt) , q) , eq = ((p , tt) , q) , (cong (act a) eq)

-- proj₁ (𝕃-mult' A E X Y) (d , t) ((i , tt) , inj₁ j)
--   with proj₁ (𝕃-mult A E X Y) (d , t) ((i , tt) , j)
-- ... | (u , v , w) , eq = (u , ((inj₁ v) , w)) , eq
-- proj₁ (𝕃-mult' A E X Y) (ret (ret x) , ret y) ((tt , tt) , inj₂ tt) =
--   ((tt , tt) , ((inj₁ tt) , (tt , tt))) , refl
-- proj₁ (𝕃-mult' A E X Y) (d , act a r) ((i , tt) , inj₂ j)
--   with proj₁ (𝕃-mult' A E X Y) (d , r) ((i , tt) , j)
-- ... | ((tt , u) , v , w) , eq = ((tt , (inj₂ u)) , ((inj₂ v) , w)) , cong (act a) eq
-- proj₂ (𝕃-mult' A E X Y) (d , t) (i , inj₁ j , k)
--   with proj₂ (𝕃-mult A E X Y) (d , t) (i , j , k)
-- ... | (u , v) , eq = (u , (inj₁ v)) , eq
-- proj₂ (𝕃-mult' A E X Y) (ret l , ret x) ((tt , tt) , inj₂ tt , k , tt) =
--   ((tt , tt) , (inj₁ k)) , refl
-- proj₂ (𝕃-mult' A E X Y) (ret d , act a r) ((tt , inj₁ tt) , inj₂ tt , k , tt) =
--   ((tt , tt) , (inj₁ k)) , refl
-- proj₂ (𝕃-mult' A E X Y) (d , act a r) ((tt , inj₂ i) , inj₂ j , k , l)
--   with proj₂ (𝕃-mult' A E X Y) (d , r) ((tt , i) , j , k , l)
-- ... | ((u , tt) , v) , eq = ((u , tt) , (inj₂ v)) , (cong (act a) eq)


-- -- Symmetry
-- ℙ-sym : (A E : Set) → (X Y : Set) → PK-≡ (PK-∘ (ℙ A E X Y) (PK-T A E (⊗-γ X Y)))
--   (PK-∘ (⊗-γ (Trace A E X) (Trace A E Y)) (ℙ A E Y X))
  
-- 𝕃>R : (A E : Set) → (X Y : Set) → PK-≡ (PK-∘ (𝕃 A E X Y) (PK-T A E (⊗-γ X Y)))
--   (PK-∘ (⊗-γ (Trace A E X) (Trace A E Y)) (ℝ A E Y X))
  
-- ℝ>L : (A E : Set) → (X Y : Set) → PK-≡ (PK-∘ (ℝ A E X Y) (PK-T A E (⊗-γ X Y)))
--   (PK-∘ (⊗-γ (Trace A E X) (Trace A E Y)) (𝕃 A E Y X))
  
-- proj₁ (ℙ-sym A E X Y) p (inj₁ i , tt) with proj₁ (𝕃>R A E X Y) p (i , tt)
-- ... | u , eq = (tt , (inj₂ (proj₂ u))) , eq
-- proj₁ (ℙ-sym A E X Y) p (inj₂ j , tt) with proj₁ (ℝ>L A E X Y) p (j , tt)
-- ... | u , eq = (tt , (inj₁ (proj₂ u))) , eq
-- proj₂ (ℙ-sym A E X Y) p (tt , inj₁ i) with proj₂ (ℝ>L A E X Y) p (tt , i)
-- ... | u , eq = ((inj₂ (proj₁ u)) , tt) , eq
-- proj₂ (ℙ-sym A E X Y) p (tt , inj₂ j) with proj₂ (𝕃>R A E X Y) p (tt , j)
-- ... | u , eq = ((inj₁ (proj₁ u)) , tt) , eq

-- proj₁ (𝕃>R A E X Y) (act a l , r) i with proj₁ (ℙ-sym A E X Y) (l , r) i
-- ... | u , eq = (tt , (proj₂ u)) , (cong (act a) eq)
-- proj₁ (𝕃>R A E X Y) (ret x , ret y) (tt , tt) = (tt , tt) , refl
-- proj₂ (𝕃>R A E X Y) (act a l , r) i with proj₂ (ℙ-sym A E X Y) (l , r) i
-- ... | u , eq =  ((proj₁ u) , tt) , (cong (act a) eq)
-- proj₂ (𝕃>R A E X Y) (ret x , ret y) (tt , tt) = (tt , tt) , refl


-- proj₁ (ℝ>L A E X Y) (l , act b r) i with proj₁ (ℙ-sym A E X Y) (l , r) i
-- ... | u , eq = (tt , (proj₂ u)) , (cong (act b) eq)
-- proj₁ (ℝ>L A E X Y) (ret x , ret y) (tt , tt) = (tt , tt) , refl
-- proj₂ (ℝ>L A E X Y) (l , act b r) i with proj₂ (ℙ-sym A E X Y) (l , r) i
-- ... | u , eq = ((proj₁ u) , tt) , (cong (act b) eq)
-- proj₂ (ℝ>L A E X Y) (ret x , ret y) (tt , tt) = (tt , tt) , refl



-- -- Associativity
-- -- Needs some clean-up
-- ℙ-asso : (A E : Set) → (X Y Z : Set)
--   → PK-≡ (PK-∘ (ℙ A E X Y ⊗ PK-Id (Trace A E Z))
--                (PK-∘ (ℙ A E (X × Y) Z) (PK-T A E (⊗-α X Y Z))))
--          (PK-∘ (⊗-α (Trace A E X) (Trace A E Y) (Trace A E Z))
--                (PK-∘ (PK-Id (Trace A E X) ⊗ ℙ A E Y Z) (ℙ A E X (Y × Z))))

-- -- Focus on left 1 1
-- proj₁ (ℙ-asso A E X Y Z) ((ret x , ret y) , ret z) ((inj₁ c , tt) , inj₁ d , tt)
--   = (tt , ((tt , (inj₁ tt)) , (inj₁ tt))) , refl
-- proj₁ (ℙ-asso A E X Y Z) ((ret x , ret y) , act c z) ((inj₁ c₁ , tt) , inj₁ () , tt)
-- proj₁ (ℙ-asso A E X Y Z) ((act a l , m) , r) ((inj₁ c , tt) , inj₁ d , tt)
--   with proj₁ (ℙ-asso A E X Y Z) ((l , m) , r) ((c , tt) , (d , tt))
-- ... | (tt , (tt , u) , v) , eq = (tt , ((tt , u) , (inj₁ v))) , cong (act a) eq

-- -- Focus on middle 2 1
-- proj₁ (ℙ-asso A E X Y Z) ((ret x , ret y) , ret z) ((inj₂ c , tt) , inj₁ d , tt)
--   = (tt , ((tt , (inj₁ tt)) , (inj₁ tt))) , refl
-- proj₁ (ℙ-asso A E X Y Z) ((ret x , ret y) , act c r) ((inj₂ c₁ , tt) , inj₁ () , tt)
-- proj₁ (ℙ-asso A E X Y Z) ((ret x , act b m) , r) ((inj₂ c , tt) , inj₁ d , tt)
--   with proj₁ (ℙ-asso A E X Y Z) ((ret x , m) , r) ((c , tt) , (d , tt))
-- ... | (tt , (tt , u) , v) , eq = (tt , ((tt , (inj₁ u)) , (inj₂ v))) , (cong (act b) eq)
-- proj₁ (ℙ-asso A E X Y Z) ((act a l , act b m) , r) ((inj₂ c , tt) , inj₁ d , tt)
--   with proj₁ (ℙ-asso A E X Y Z) ((act a l , m) , r) ((c , tt) , (d , tt))
-- ... | (tt , (tt , u) , v) , eq = (tt , ((tt , (inj₁ u)) , (inj₂ v))) , (cong (act b) eq)

-- -- Focus on right - 2
-- proj₁ (ℙ-asso A E X Y Z) ((ret x , ret y) , ret z) ((inj₁ x₁ , tt) , inj₂ y , tt)
--   = (tt , ((tt , (inj₁ tt)) , (inj₁ tt))) , refl
-- proj₁ (ℙ-asso A E X Y Z) ((ret x , act b m) , ret z) ((inj₁ () , tt) , inj₂ y , tt)
-- proj₁ (ℙ-asso A E X Y Z) ((ret x , ret y) , ret z) ((inj₂ y₁ , tt) , inj₂ y , tt)
--   = (tt , ((tt , (inj₁ tt)) , (inj₁ tt))) , refl
-- proj₁ (ℙ-asso A E X Y Z) ((ret x , ret y) , act c r) ((ij , tt) , inj₂ v , tt)
--   with proj₁ (ℙ-asso A E X Y Z) ((ret x , ret y) , r) ((ij , tt) , (v , tt))
-- ... | (tt , (tt , u) , w) , eq = (tt , ((tt , (inj₂ u)) , (inj₂ w))) , (cong (act c) eq)
-- proj₁ (ℙ-asso A E X Y Z) ((ret x , act b m) , act c r) ((ij , tt) , inj₂ y , tt)
--   with proj₁ (ℙ-asso A E X Y Z) ((ret x , act b m) , r) ((ij , tt) , (y , tt))
-- ... | (tt , (tt , u) , v) , eq = (tt , ((tt , (inj₂ u)) , (inj₂ v))) , (cong (act c) eq)
-- proj₁ (ℙ-asso A E X Y Z) ((act a l , ret y) , act c r) ((ij , tt) , inj₂ v , tt)
--   with proj₁ (ℙ-asso A E X Y Z) ((act a l , ret y) , r) ((ij , tt) , (v , tt))
-- ... | (tt , (tt , u) , w) , eq = (tt , ((tt , (inj₂ u)) , (inj₂ w))) , (cong (act c) eq)
-- proj₁ (ℙ-asso A E X Y Z) ((act a l , act b m) , act c r) ((ij , tt) , inj₂ y , tt)
--   with proj₁ (ℙ-asso A E X Y Z) ((act a l , act b m) , r) ((ij , tt) , (y , tt))
-- ... | (tt , (tt , u) , v) , eq = (tt , ((tt , (inj₂ u)) , (inj₂ v))) , (cong (act c) eq)


-- -- Focus on left - 1
-- proj₂ (ℙ-asso A E X Y Z) ((ret x , ret y) , ret z) (tt , (tt , inj₁ u) , inj₁ v)
--   = (((inj₁ tt) , tt) , ((inj₁ tt) , tt)) , refl
-- proj₂ (ℙ-asso A E X Y Z) ((ret x , ret y) , ret z) (tt , (tt , inj₂ u) , inj₁ v)
--   = (((inj₁ tt) , tt) , ((inj₁ tt) , tt)) , refl
-- proj₂ (ℙ-asso A E X Y Z) ((ret x , m) , act c r) (tt , (tt , inj₂ u) , inj₁ ()) 
-- proj₂ (ℙ-asso A E X Y Z) ((ret x , act b m) , ret y) (tt , (tt , inj₂ ()) , inj₁ v)
-- proj₂ (ℙ-asso A E X Y Z) ((act a l , m) , r)       (tt , (tt , u) , inj₁ v)
--   with proj₂ (ℙ-asso A E X Y Z) ((l , m) , r) (tt , (tt , u) , v)
-- ... | ((p , tt) , q , tt) , eq = (((inj₁ p) , tt) , ((inj₁ q) , tt)) , (cong (act a) eq)

-- -- Focus on middle 1 2
-- proj₂ (ℙ-asso A E X Y Z) ((ret x , ret y) , ret z) (tt , (tt , inj₁ u) , inj₂ v)
--   = (((inj₁ tt) , tt) , ((inj₁ tt) , tt)) , refl
-- proj₂ (ℙ-asso A E X Y Z) ((ret x , ret y) , act c r) (tt , (tt , inj₁ ()) , inj₂ v)
-- proj₂ (ℙ-asso A E X Y Z) ((ret x , act b m) , ret z)   (tt , (tt , inj₁ u) , inj₂ v)
--   with proj₂ (ℙ-asso A E X Y Z) ((ret x , m) , ret z) (tt , (tt , u) , v)
-- ... | ((p , tt) , q , tt) , eq = (((inj₂ p) , tt) , ((inj₁ q) , tt)) , (cong (act b) eq)
-- proj₂ (ℙ-asso A E X Y Z) ((ret x , act b m) , act c r)   (tt , (tt , inj₁ u) , inj₂ v)
--   with proj₂ (ℙ-asso A E X Y Z) ((ret x , m) , act c r) (tt , (tt , u) , v)
-- ... | ((p , tt) , q , tt) , eq = (((inj₂ p) , tt) , ((inj₁ q) , tt)) , (cong (act b) eq)
-- proj₂ (ℙ-asso A E X Y Z) ((act a l , ret y) , ret z) (tt , (tt , inj₁ u) , inj₂ ())
-- proj₂ (ℙ-asso A E X Y Z) ((act a l , ret y) , act c r) (tt , (tt , inj₁ ()) , inj₂ v)
-- proj₂ (ℙ-asso A E X Y Z) ((act a l , act b m) , r) (tt , (tt , inj₁ u) , inj₂ v)
--   with proj₂ (ℙ-asso A E X Y Z) ((act a l , m) , r) (tt , (tt , u) , v)
-- ... | ((p , tt) , q , tt) , eq = (((inj₂ p) , tt) , ((inj₁ q) , tt)) , (cong (act b) eq)

-- -- Focus on right 2 2
-- proj₂ (ℙ-asso A E X Y Z) ((ret x , ret y) , ret z) (tt , (tt , inj₂ u) , inj₂ v)
--   = (((inj₁ tt) , tt) , ((inj₁ tt) , tt)) , refl
-- proj₂ (ℙ-asso A E X Y Z) ((ret x , ret y) , act c r) (tt , (tt , inj₂ u) , inj₂ v)
--   with proj₂ (ℙ-asso A E X Y Z) ((ret x , ret y) , r) (tt , (tt , u) , v)
-- ... | ((inj₁ p , tt) , q , tt) , eq = (((inj₂ tt) , tt) , (inj₂ q , tt)) , (cong (act c) eq)
-- ... | ((inj₂ p , tt) , q , tt) , eq = (((inj₂ tt) , tt) , (inj₂ q , tt)) , (cong (act c) eq)
-- proj₂ (ℙ-asso A E X Y Z) ((ret x , act b m) , ret z) (tt , (tt , inj₂ ()) , v)
-- proj₂ (ℙ-asso A E X Y Z) ((ret x , act b m) , act c r) (tt , (tt , inj₂ u) , inj₂ v)
--   with proj₂ (ℙ-asso A E X Y Z) ((ret x , act b m) , r) (tt , (tt , u) , v)
-- ... | ((inj₂ p , tt) , q , tt) , eq = (((inj₂ p) , tt) , (inj₂ q) , tt) , cong (act c) eq
-- proj₂ (ℙ-asso A E X Y Z) ((act a l , ret y) , ret z) (tt , (tt , inj₂ u) , inj₂ ())
-- proj₂ (ℙ-asso A E X Y Z) ((act a l , act b m) , ret z) (tt , (tt , inj₂ ()) , inj₂ v)
-- proj₂ (ℙ-asso A E X Y Z) ((act a l , ret y) , act c r) (tt , (tt , inj₂ u) , inj₂ v)
--   with proj₂ (ℙ-asso A E X Y Z) ((act a l , ret y) , r) (tt , (tt , u) , v)
-- ... | ((p , tt) , q , tt) , eq = ((p , tt) , (inj₂ q) , tt) , cong (act c) eq
-- proj₂ (ℙ-asso A E X Y Z) ((act a l , act b m) , act c r) (tt , (tt , inj₂ u) , inj₂ v)
--   with proj₂ (ℙ-asso A E X Y Z) ((act a l , act b m) , r) (tt , (tt , u) , v)
-- ... | ((p , tt) , q , tt) , eq = ((p , tt) , (inj₂ q) , tt) , cong (act c) eq






