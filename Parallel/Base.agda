module Parallel.Base where

open import Data.Unit
open import Data.Empty
open import Data.Sum renaming (map to map⊎)
open import Data.Nat hiding (_⊔_)
open import Data.Product renaming (map to map×)
open import Relation.Binary.PropositionalEquality hiding ([_])


open import Slice.Lattice

open import Slice-Functions.Base
open import Slice-Functions.Subcategories
open import Slice-Functions.Monoidal

open import Monads.Trace




-- Paralel operator
ℙ : (A E : Set) → (X Y : Set)
  → SF ((Trace A E X) × (Trace A E Y)) (Trace A E (X × Y))

𝕃 : (A E : Set) → (X Y : Set)
  → SF ((Trace A E X) × (Trace A E Y)) (Trace A E (X × Y))

ℝ : (A E : Set) → (X Y : Set)
  → SF ((Trace A E X) × (Trace A E Y)) (Trace A E (X × Y))

ℙ A E X Y p = join (𝕃 A E X Y p) (ℝ A E X Y p)

𝕃 A E X Y (ret x , ret y) = SF-id _ (ret (x , y))
𝕃 A E X Y (ret x , act b r) = SL-⊥ _
𝕃 A E X Y (ret x , err e) = SL-⊥ _
𝕃 A E X Y (act a l , r) = SL-act a (X × Y) (ℙ A E X Y (l , r))
𝕃 A E X Y (err e , r) = SF-id _ (err e)


ℝ A E X Y (l , act b r) = SL-act b (X × Y) (ℙ A E X Y (l , r))
ℝ A E X Y (l , err e) = SF-id _ (err e)
ℝ A E X Y (ret x , ret y) = SF-id _ (ret (x , y))
ℝ A E X Y (act a l , ret y) = SL-⊥ _
ℝ A E X Y (err e , ret y) = SL-⊥ _


ℙ-Total : (A E X Y : Set) → SF-Total (ℙ A E X Y)
ℙ-Total A E X Y (ret x , ret y) = inj₁ tt
ℙ-Total A E X Y (ret x , act a r) = inj₂ (ℙ-Total A E X Y (ret x , r))
ℙ-Total A E X Y (ret x , err e) = inj₂ tt
ℙ-Total A E X Y (act a l , r) = inj₁ (ℙ-Total A E X Y (l , r))
ℙ-Total A E X Y (err e , r) = inj₁ tt


-- < holds without totality, > needs totality
ℙ-T-nat : (A E : Set) → {X X' Y Y' : Set} → (f : SF X X') → (g : SF Y Y')
  → SF-Total f → SF-Total g → SF≡ (SF-∘ (SF-T A E f ⊗ SF-T A E g) (ℙ A E X' Y'))
                                   (SF-∘ (ℙ A E X Y) (SF-T A E (f ⊗ g)))
𝕃-T-nat : (A E : Set) → {X X' Y Y' : Set} → (f : SF X X') → (g : SF Y Y')
  → SF-Total f → SF-Total g → SF≡ (SF-∘ (SF-T A E f ⊗ SF-T A E g) (𝕃 A E X' Y'))
                                   (SF-∘ (𝕃 A E X Y) (SF-T A E (f ⊗ g)))
ℝ-T-nat : (A E : Set) → {X X' Y Y' : Set} → (f : SF X X') → (g : SF Y Y')
  → SF-Total f → SF-Total g → SF≡ (SF-∘ (SF-T A E f ⊗ SF-T A E g) (ℝ A E X' Y'))
                                   (SF-∘ (ℝ A E X Y) (SF-T A E (f ⊗ g)))

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
  ((tt , (SF-T-Total A E g g-tot r)) , tt) , refl

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
  ((SF-T-Total A E f f-tot l , tt) , tt) , refl
proj₂ (ℝ-T-nat A E f g f-tot g-tot) (ret x , ret y) (i , j) = (j , tt) , refl

𝕃-T-nat-left : (A E Y : Set) → {X X' : Set} → (f : SF X X') 
  → SF-Total f → SF≡ (SF-∘ (SF-T A E f ⊗ SF-id _) (𝕃 A E X' Y))
                            (SF-∘ (𝕃 A E X Y) (SF-T A E (f ⊗ SF-id _)))
𝕃-T-nat-left A E Y f f-tot = SF≡-Tran _ _ _
  (SF-∘-l≡ (SF-T A E f ⊗ SF-id _) (SF-T A E f ⊗ (SF-T A E (SF-id _))) (𝕃 A E _ _)
           (⊗-≡ (SF≡-Refl (SF-T A E f)) (SF≡-Symm _ _ (SF-T-Id A E Y))))
  (𝕃-T-nat A E f (SF-id _) f-tot λ x → tt)

𝕃-T-nat-right : (A E X : Set) → {Y Y' : Set} → (f : SF Y Y') 
  → SF-Total f → SF≡ (SF-∘ (SF-id _ ⊗ SF-T A E f) (𝕃 A E X Y'))
                            (SF-∘ (𝕃 A E X Y) (SF-T A E (SF-id _ ⊗ f)))
𝕃-T-nat-right A E Y f f-tot = SF≡-Tran _ _ _
  (SF-∘-l≡ (SF-id _ ⊗ SF-T A E f) ((SF-T A E (SF-id _)) ⊗ (SF-T A E f)) (𝕃 A E _ _)
           (⊗-≡ (SF≡-Symm _ _ (SF-T-Id A E Y)) (SF≡-Refl (SF-T A E f))))
  (𝕃-T-nat A E (SF-id _) f (λ x → tt) f-tot)


-- ⊗-≡ (SF≡-Refl (SF-T A E f)) (SF≡-Symm _ _ (SF-T-Id A E Y))

ℙ-σ : (A E X Y : Set) → SF≡ (SF-∘ (SF-T-η A E X ⊗ SF-id _) (ℙ A E X Y))
                                        (SF-T-σ A E X Y)

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



𝕃ℝ-γ : (A E X Y : Set) → SF≡ (SF-∘ (𝕃 A E X Y) (SF-T A E (⊗-γ X Y)))
                                   (SF-∘ (⊗-γ (Trace A E X) (Trace A E Y)) (ℝ A E Y X))
ℝ𝕃-γ : (A E X Y : Set) → SF≡ (SF-∘ (ℝ A E X Y) (SF-T A E (⊗-γ X Y)))
                                   (SF-∘ (⊗-γ (Trace A E X) (Trace A E Y)) (𝕃 A E Y X))
ℙ-γ : (A E X Y : Set) → SF≡ (SF-∘ (ℙ A E X Y) (SF-T A E (⊗-γ X Y)))
                                  (SF-∘ (⊗-γ (Trace A E X) (Trace A E Y)) (ℙ A E Y X))
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
ℙ-α : (A E X Y Z : Set) → SF≡ (SF-∘ (SF-id _ ⊗ ℙ A E Y Z) (ℙ A E X (Y × Z)))
  (SF-∘ (⊗-α' _ _ _) (SF-∘ (ℙ A E X Y ⊗ SF-id _)
        (SF-∘ (ℙ A E (X × Y) Z) (SF-T A E (⊗-α X Y Z)))))
𝕃-α : (A E X Y Z : Set) → SF≡ (SF-∘ (SF-id _ ⊗ ℙ A E Y Z) (𝕃 A E X (Y × Z)))
  (SF-∘ (⊗-α' _ _ _) (SF-∘ (𝕃 A E X Y ⊗ SF-id _)
        (SF-∘ (𝕃 A E (X × Y) Z) (SF-T A E (⊗-α X Y Z)))))
𝕄-α : (A E X Y Z : Set) → SF≡ (SF-∘ (SF-id _ ⊗ 𝕃 A E Y Z) (ℝ A E X (Y × Z)))
  (SF-∘ (⊗-α' _ _ _) (SF-∘ (ℝ A E X Y ⊗ SF-id _)
        (SF-∘ (𝕃 A E (X × Y) Z) (SF-T A E (⊗-α X Y Z)))))
ℝ-α : (A E X Y Z : Set) → SF≡ (SF-∘ (SF-id _ ⊗ ℝ A E Y Z) (ℝ A E X (Y × Z)))
  (SF-∘ (⊗-α' _ _ _) (SF-∘ (ℙ A E X Y ⊗ SF-id _)
        (SF-∘ (ℝ A E (X × Y) Z) (SF-T A E (⊗-α X Y Z)))))

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
