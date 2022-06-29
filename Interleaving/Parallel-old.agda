module Interleaving.Parallel-old where

open import Data.Unit
open import Data.Empty
open import Data.Sum renaming (map to map⊎)
open import Data.Nat hiding (_⊔_)
open import Data.Product renaming (map to map×)
open import Relation.Binary.PropositionalEquality hiding ([_])


open import Index-Nondeterminism
open import Monoidal
open import Monads.Trace-old




-- Paralel operator
PK-T-P : (A : Set) → (X Y : Set) → PK-Hom ((Trace A X) × (Trace A Y)) (Trace A (X × Y))

PK-T-L : (A : Set) → (X Y : Set) → PK-Hom ((Trace A X) × (Trace A Y)) (Trace A (X × Y))

PK-T-R : (A : Set) → (X Y : Set) → PK-Hom ((Trace A X) × (Trace A Y)) (Trace A (X × Y))

PK-T-P A X Y p = join (PK-T-L A X Y p) (PK-T-R A X Y p)

PK-T-L A X Y (ret x , ret y) = PK-Id _ (ret (x , y))
PK-T-L A X Y (ret x , act b r) = ⊥ , (λ ())
PK-T-L A X Y (act a l , r) = Pow-act a (X × Y) (PK-T-P A X Y (l , r))

PK-T-R A X Y (l , act b r) = Pow-act b (X × Y) (PK-T-P A X Y (l , r))
PK-T-R A X Y (ret x , ret y) = PK-Id _ (ret (x , y))
PK-T-R A X Y (act a l , ret y) = ⊥ , (λ ())


-- Naturality
PK-T-P-nat : (A : Set) → {X X' Y Y' : Set} → (f : PK-Hom X X') → (g : PK-Hom Y Y')
  → PK-≡ (PK-∘ (PK-T A f ⊗ PK-T A g) (PK-T-P A X' Y'))
         (PK-∘ (PK-T-P A X Y) (PK-T A (f ⊗ g)))

PK-T-L-nat : (A : Set) → {X X' Y Y' : Set} → (f : PK-Hom X X') → (g : PK-Hom Y Y')
  → PK-≡ (PK-∘ (PK-T A f ⊗ PK-T A g) (PK-T-L A X' Y'))
         (PK-∘ (PK-T-L A X Y) (PK-T A (f ⊗ g)))

PK-T-R-nat : (A : Set) → {X X' Y Y' : Set} → (f : PK-Hom X X') → (g : PK-Hom Y Y')
  → PK-≡ (PK-∘ (PK-T A f ⊗ PK-T A g) (PK-T-R A X' Y'))
         (PK-∘ (PK-T-R A X Y) (PK-T A (f ⊗ g)))

proj₁ (PK-T-P-nat A f g) p (ij , inj₁ u) with proj₁ (PK-T-L-nat A f g) p (ij , u)
... | (v , w) , eq = ((inj₁ v) , w) , eq
proj₁ (PK-T-P-nat A f g) p (ij , inj₂ u) with proj₁ (PK-T-R-nat A f g) p (ij , u)
... | (v , w) , eq = ((inj₂ v) , w) , eq
proj₂ (PK-T-P-nat A f g) p (inj₁ u , i) with proj₂ (PK-T-L-nat A f g) p (u , i)
... | (v , w) , eq = (v , inj₁ w) , eq
proj₂ (PK-T-P-nat A f g) p (inj₂ u , j) with proj₂ (PK-T-R-nat A f g) p (u , j)
... | (v , w) , eq = (v , inj₂ w) , eq

proj₁ (PK-T-L-nat A f g) (ret x , ret y) (ij , tt) = (tt , ij) , refl
proj₁ (PK-T-L-nat A f g) (act a l , r) =
  Pow-act-< a (_ × _) _ _ (proj₁ (PK-T-P-nat A f g) (l , r))
proj₂ (PK-T-L-nat A f g) (ret x , ret y) (tt , ij) = (ij , tt) , refl
proj₂ (PK-T-L-nat A f g) (act a l , r) =
  Pow-act-< a (_ × _) _ _ (proj₂ (PK-T-P-nat A f g) (l , r))

proj₁ (PK-T-R-nat A f g) (l , act b r)  =
  Pow-act-< b (_ × _) _ _ (proj₁ (PK-T-P-nat A f g) (l , r))
proj₁ (PK-T-R-nat A f g) (ret x , ret y) (ij , tt) = (tt , ij) , refl
proj₂ (PK-T-R-nat A f g) (l , act b r) =
  Pow-act-< b (_ × _) _ _ (proj₂ (PK-T-P-nat A f g) (l , r))
proj₂ (PK-T-R-nat A f g) (ret x , ret y) (tt , ij) = (ij , tt) , refl


-- Unit law
PK-T-L-unit : (A : Set) → (X Y : Set)
  → PK-≡ (PK-∘ (PK-T-η A X ⊗ PK-Id (Trace A Y))  (PK-T-L A X Y))
         (PK-∘ (PK-Id X ⊗ PK-T-ε A Y) (PK-T-η A (X × Y)))
proj₁ (PK-T-L-unit A X Y) (x , ret y) ((tt , tt) , tt) = ((tt , tt) , tt) , refl
proj₂ (PK-T-L-unit A X Y) (x , ret y) ((tt , tt) , tt) = ((tt , tt) , tt) , refl


-- Multiplication law
PK-T-L-mult : (A : Set) → (X Y : Set)
  → PK-≡ (PK-∘ (PK-T-μ A X ⊗ PK-Id (Trace A Y))
               (PK-T-L A X Y))
         (PK-∘ (PK-Id (Trace A (Trace A X)) ⊗ PK-T-δ A Y)
         (PK-∘ (PK-T-L A (Trace A X) (Trace A Y))
         (PK-∘ (PK-T A (PK-T-L A X Y))
               (PK-T-μ A (X × Y)))))
PK-T-L-mult' : (A : Set) → (X Y : Set)
  → PK-≡ (PK-∘ (PK-T-μ A X ⊗ PK-Id (Trace A Y))
               (PK-T-P A X Y))
         (PK-∘ (PK-Id (Trace A (Trace A X)) ⊗ PK-T-δ A Y)
         (PK-∘ (PK-T-P A (Trace A X) (Trace A Y))
         (PK-∘ (PK-T A (PK-T-L A X Y))
               (PK-T-μ A (X × Y)))))
proj₁ (PK-T-L-mult A X Y) (ret l , ret y) ((tt , tt) , j) =
  ((tt , tt) , (tt , (j , tt))) , refl
proj₁ (PK-T-L-mult A X Y) (ret l , act b r) ((tt , tt) , j) =
  ((tt , (inj₁ tt)) , (tt , (j , tt))) , refl
proj₁ (PK-T-L-mult A X Y) (act a d , r) ((i , tt) , j)
  with proj₁ (PK-T-L-mult' A X Y) (d , r) ((i , tt) , j)
... | u , eq = u , cong (act a) eq
proj₂ (PK-T-L-mult A X Y) (ret l , ret y) ((tt , i) , j , k , v) = ((tt , tt) , k) , refl
proj₂ (PK-T-L-mult A X Y) (ret l , act b r) ((tt , inj₁ tt) , j , k , v) =
  ((tt , tt) , k) , refl
proj₂ (PK-T-L-mult A X Y) (act a d , r) i
  with proj₂ (PK-T-L-mult' A X Y) (d , r) i
... | ((p , tt) , q) , eq = ((p , tt) , q) , (cong (act a) eq)

proj₁ (PK-T-L-mult' A X Y) (d , t) ((i , tt) , inj₁ j)
  with proj₁ (PK-T-L-mult A X Y) (d , t) ((i , tt) , j)
... | (u , v , w) , eq = (u , ((inj₁ v) , w)) , eq
proj₁ (PK-T-L-mult' A X Y) (ret (ret x) , ret y) ((tt , tt) , inj₂ tt) =
  ((tt , tt) , ((inj₁ tt) , (tt , tt))) , refl
proj₁ (PK-T-L-mult' A X Y) (d , act a r) ((i , tt) , inj₂ j)
  with proj₁ (PK-T-L-mult' A X Y) (d , r) ((i , tt) , j)
... | ((tt , u) , v , w) , eq = ((tt , (inj₂ u)) , ((inj₂ v) , w)) , cong (act a) eq
proj₂ (PK-T-L-mult' A X Y) (d , t) (i , inj₁ j , k)
  with proj₂ (PK-T-L-mult A X Y) (d , t) (i , j , k)
... | (u , v) , eq = (u , (inj₁ v)) , eq
proj₂ (PK-T-L-mult' A X Y) (ret l , ret x) ((tt , tt) , inj₂ tt , k , tt) =
  ((tt , tt) , (inj₁ k)) , refl
proj₂ (PK-T-L-mult' A X Y) (ret d , act a r) ((tt , inj₁ tt) , inj₂ tt , k , tt) =
  ((tt , tt) , (inj₁ k)) , refl
proj₂ (PK-T-L-mult' A X Y) (d , act a r) ((tt , inj₂ i) , inj₂ j , k , l)
  with proj₂ (PK-T-L-mult' A X Y) (d , r) ((tt , i) , j , k , l)
... | ((u , tt) , v) , eq = ((u , tt) , (inj₂ v)) , (cong (act a) eq)


-- Symmetry
PK-T-P-sym : (A : Set) → (X Y : Set) → PK-≡ (PK-∘ (PK-T-P A X Y) (PK-T A (⊗-γ X Y)))
  (PK-∘ (⊗-γ (Trace A X) (Trace A Y)) (PK-T-P A Y X))
  
PK-T-L>R : (A : Set) → (X Y : Set) → PK-≡ (PK-∘ (PK-T-L A X Y) (PK-T A (⊗-γ X Y)))
  (PK-∘ (⊗-γ (Trace A X) (Trace A Y)) (PK-T-R A Y X))
  
PK-T-R>L : (A : Set) → (X Y : Set) → PK-≡ (PK-∘ (PK-T-R A X Y) (PK-T A (⊗-γ X Y)))
  (PK-∘ (⊗-γ (Trace A X) (Trace A Y)) (PK-T-L A Y X))
  
proj₁ (PK-T-P-sym A X Y) p (inj₁ i , tt) with proj₁ (PK-T-L>R A X Y) p (i , tt)
... | u , eq = (tt , (inj₂ (proj₂ u))) , eq
proj₁ (PK-T-P-sym A X Y) p (inj₂ j , tt) with proj₁ (PK-T-R>L A X Y) p (j , tt)
... | u , eq = (tt , (inj₁ (proj₂ u))) , eq
proj₂ (PK-T-P-sym A X Y) p (tt , inj₁ i) with proj₂ (PK-T-R>L A X Y) p (tt , i)
... | u , eq = ((inj₂ (proj₁ u)) , tt) , eq
proj₂ (PK-T-P-sym A X Y) p (tt , inj₂ j) with proj₂ (PK-T-L>R A X Y) p (tt , j)
... | u , eq = ((inj₁ (proj₁ u)) , tt) , eq

proj₁ (PK-T-L>R A X Y) (act a l , r) i with proj₁ (PK-T-P-sym A X Y) (l , r) i
... | u , eq = (tt , (proj₂ u)) , (cong (act a) eq)
proj₁ (PK-T-L>R A X Y) (ret x , ret y) (tt , tt) = (tt , tt) , refl
proj₂ (PK-T-L>R A X Y) (act a l , r) i with proj₂ (PK-T-P-sym A X Y) (l , r) i
... | u , eq =  ((proj₁ u) , tt) , (cong (act a) eq)
proj₂ (PK-T-L>R A X Y) (ret x , ret y) (tt , tt) = (tt , tt) , refl


proj₁ (PK-T-R>L A X Y) (l , act b r) i with proj₁ (PK-T-P-sym A X Y) (l , r) i
... | u , eq = (tt , (proj₂ u)) , (cong (act b) eq)
proj₁ (PK-T-R>L A X Y) (ret x , ret y) (tt , tt) = (tt , tt) , refl
proj₂ (PK-T-R>L A X Y) (l , act b r) i with proj₂ (PK-T-P-sym A X Y) (l , r) i
... | u , eq = ((proj₁ u) , tt) , (cong (act b) eq)
proj₂ (PK-T-R>L A X Y) (ret x , ret y) (tt , tt) = (tt , tt) , refl



-- Associativity
-- Needs some clean-up
PK-T-P-asso : (A : Set) → (X Y Z : Set)
  → PK-≡ (PK-∘ (PK-T-P A X Y ⊗ PK-Id (Trace A Z))
               (PK-∘ (PK-T-P A (X × Y) Z) (PK-T A (⊗-α X Y Z))))
         (PK-∘ (⊗-α (Trace A X) (Trace A Y) (Trace A Z))
               (PK-∘ (PK-Id (Trace A X) ⊗ PK-T-P A Y Z) (PK-T-P A X (Y × Z))))

-- Focus on left 1 1
proj₁ (PK-T-P-asso A X Y Z) ((ret x , ret y) , ret z) ((inj₁ c , tt) , inj₁ d , tt)
  = (tt , ((tt , (inj₁ tt)) , (inj₁ tt))) , refl
proj₁ (PK-T-P-asso A X Y Z) ((ret x , ret y) , act c z) ((inj₁ c₁ , tt) , inj₁ () , tt)
proj₁ (PK-T-P-asso A X Y Z) ((act a l , m) , r) ((inj₁ c , tt) , inj₁ d , tt)
  with proj₁ (PK-T-P-asso A X Y Z) ((l , m) , r) ((c , tt) , (d , tt))
... | (tt , (tt , u) , v) , eq = (tt , ((tt , u) , (inj₁ v))) , cong (act a) eq

-- Focus on middle 2 1
proj₁ (PK-T-P-asso A X Y Z) ((ret x , ret y) , ret z) ((inj₂ c , tt) , inj₁ d , tt)
  = (tt , ((tt , (inj₁ tt)) , (inj₁ tt))) , refl
proj₁ (PK-T-P-asso A X Y Z) ((ret x , ret y) , act c r) ((inj₂ c₁ , tt) , inj₁ () , tt)
proj₁ (PK-T-P-asso A X Y Z) ((ret x , act b m) , r) ((inj₂ c , tt) , inj₁ d , tt)
  with proj₁ (PK-T-P-asso A X Y Z) ((ret x , m) , r) ((c , tt) , (d , tt))
... | (tt , (tt , u) , v) , eq = (tt , ((tt , (inj₁ u)) , (inj₂ v))) , (cong (act b) eq)
proj₁ (PK-T-P-asso A X Y Z) ((act a l , act b m) , r) ((inj₂ c , tt) , inj₁ d , tt)
  with proj₁ (PK-T-P-asso A X Y Z) ((act a l , m) , r) ((c , tt) , (d , tt))
... | (tt , (tt , u) , v) , eq = (tt , ((tt , (inj₁ u)) , (inj₂ v))) , (cong (act b) eq)

-- Focus on right - 2
proj₁ (PK-T-P-asso A X Y Z) ((ret x , ret y) , ret z) ((inj₁ x₁ , tt) , inj₂ y , tt)
  = (tt , ((tt , (inj₁ tt)) , (inj₁ tt))) , refl
proj₁ (PK-T-P-asso A X Y Z) ((ret x , act b m) , ret z) ((inj₁ () , tt) , inj₂ y , tt)
proj₁ (PK-T-P-asso A X Y Z) ((ret x , ret y) , ret z) ((inj₂ y₁ , tt) , inj₂ y , tt)
  = (tt , ((tt , (inj₁ tt)) , (inj₁ tt))) , refl
proj₁ (PK-T-P-asso A X Y Z) ((ret x , ret y) , act c r) ((ij , tt) , inj₂ v , tt)
  with proj₁ (PK-T-P-asso A X Y Z) ((ret x , ret y) , r) ((ij , tt) , (v , tt))
... | (tt , (tt , u) , w) , eq = (tt , ((tt , (inj₂ u)) , (inj₂ w))) , (cong (act c) eq)
proj₁ (PK-T-P-asso A X Y Z) ((ret x , act b m) , act c r) ((ij , tt) , inj₂ y , tt)
  with proj₁ (PK-T-P-asso A X Y Z) ((ret x , act b m) , r) ((ij , tt) , (y , tt))
... | (tt , (tt , u) , v) , eq = (tt , ((tt , (inj₂ u)) , (inj₂ v))) , (cong (act c) eq)
proj₁ (PK-T-P-asso A X Y Z) ((act a l , ret y) , act c r) ((ij , tt) , inj₂ v , tt)
  with proj₁ (PK-T-P-asso A X Y Z) ((act a l , ret y) , r) ((ij , tt) , (v , tt))
... | (tt , (tt , u) , w) , eq = (tt , ((tt , (inj₂ u)) , (inj₂ w))) , (cong (act c) eq)
proj₁ (PK-T-P-asso A X Y Z) ((act a l , act b m) , act c r) ((ij , tt) , inj₂ y , tt)
  with proj₁ (PK-T-P-asso A X Y Z) ((act a l , act b m) , r) ((ij , tt) , (y , tt))
... | (tt , (tt , u) , v) , eq = (tt , ((tt , (inj₂ u)) , (inj₂ v))) , (cong (act c) eq)


-- Focus on left - 1
proj₂ (PK-T-P-asso A X Y Z) ((ret x , ret y) , ret z) (tt , (tt , inj₁ u) , inj₁ v)
  = (((inj₁ tt) , tt) , ((inj₁ tt) , tt)) , refl
proj₂ (PK-T-P-asso A X Y Z) ((ret x , ret y) , ret z) (tt , (tt , inj₂ u) , inj₁ v)
  = (((inj₁ tt) , tt) , ((inj₁ tt) , tt)) , refl
proj₂ (PK-T-P-asso A X Y Z) ((ret x , m) , act c r) (tt , (tt , inj₂ u) , inj₁ ()) 
proj₂ (PK-T-P-asso A X Y Z) ((ret x , act b m) , ret y) (tt , (tt , inj₂ ()) , inj₁ v)
proj₂ (PK-T-P-asso A X Y Z) ((act a l , m) , r)       (tt , (tt , u) , inj₁ v)
  with proj₂ (PK-T-P-asso A X Y Z) ((l , m) , r) (tt , (tt , u) , v)
... | ((p , tt) , q , tt) , eq = (((inj₁ p) , tt) , ((inj₁ q) , tt)) , (cong (act a) eq)

-- Focus on middle 1 2
proj₂ (PK-T-P-asso A X Y Z) ((ret x , ret y) , ret z) (tt , (tt , inj₁ u) , inj₂ v)
  = (((inj₁ tt) , tt) , ((inj₁ tt) , tt)) , refl
proj₂ (PK-T-P-asso A X Y Z) ((ret x , ret y) , act c r) (tt , (tt , inj₁ ()) , inj₂ v)
proj₂ (PK-T-P-asso A X Y Z) ((ret x , act b m) , ret z)   (tt , (tt , inj₁ u) , inj₂ v)
  with proj₂ (PK-T-P-asso A X Y Z) ((ret x , m) , ret z) (tt , (tt , u) , v)
... | ((p , tt) , q , tt) , eq = (((inj₂ p) , tt) , ((inj₁ q) , tt)) , (cong (act b) eq)
proj₂ (PK-T-P-asso A X Y Z) ((ret x , act b m) , act c r)   (tt , (tt , inj₁ u) , inj₂ v)
  with proj₂ (PK-T-P-asso A X Y Z) ((ret x , m) , act c r) (tt , (tt , u) , v)
... | ((p , tt) , q , tt) , eq = (((inj₂ p) , tt) , ((inj₁ q) , tt)) , (cong (act b) eq)
proj₂ (PK-T-P-asso A X Y Z) ((act a l , ret y) , ret z) (tt , (tt , inj₁ u) , inj₂ ())
proj₂ (PK-T-P-asso A X Y Z) ((act a l , ret y) , act c r) (tt , (tt , inj₁ ()) , inj₂ v)
proj₂ (PK-T-P-asso A X Y Z) ((act a l , act b m) , r) (tt , (tt , inj₁ u) , inj₂ v)
  with proj₂ (PK-T-P-asso A X Y Z) ((act a l , m) , r) (tt , (tt , u) , v)
... | ((p , tt) , q , tt) , eq = (((inj₂ p) , tt) , ((inj₁ q) , tt)) , (cong (act b) eq)

-- Focus on right 2 2
proj₂ (PK-T-P-asso A X Y Z) ((ret x , ret y) , ret z) (tt , (tt , inj₂ u) , inj₂ v)
  = (((inj₁ tt) , tt) , ((inj₁ tt) , tt)) , refl
proj₂ (PK-T-P-asso A X Y Z) ((ret x , ret y) , act c r) (tt , (tt , inj₂ u) , inj₂ v)
  with proj₂ (PK-T-P-asso A X Y Z) ((ret x , ret y) , r) (tt , (tt , u) , v)
... | ((inj₁ p , tt) , q , tt) , eq = (((inj₂ tt) , tt) , (inj₂ q , tt)) , (cong (act c) eq)
... | ((inj₂ p , tt) , q , tt) , eq = (((inj₂ tt) , tt) , (inj₂ q , tt)) , (cong (act c) eq)
proj₂ (PK-T-P-asso A X Y Z) ((ret x , act b m) , ret z) (tt , (tt , inj₂ ()) , v)
proj₂ (PK-T-P-asso A X Y Z) ((ret x , act b m) , act c r) (tt , (tt , inj₂ u) , inj₂ v)
  with proj₂ (PK-T-P-asso A X Y Z) ((ret x , act b m) , r) (tt , (tt , u) , v)
... | ((inj₂ p , tt) , q , tt) , eq = (((inj₂ p) , tt) , (inj₂ q) , tt) , cong (act c) eq
proj₂ (PK-T-P-asso A X Y Z) ((act a l , ret y) , ret z) (tt , (tt , inj₂ u) , inj₂ ())
proj₂ (PK-T-P-asso A X Y Z) ((act a l , act b m) , ret z) (tt , (tt , inj₂ ()) , inj₂ v)
proj₂ (PK-T-P-asso A X Y Z) ((act a l , ret y) , act c r) (tt , (tt , inj₂ u) , inj₂ v)
  with proj₂ (PK-T-P-asso A X Y Z) ((act a l , ret y) , r) (tt , (tt , u) , v)
... | ((p , tt) , q , tt) , eq = ((p , tt) , (inj₂ q) , tt) , cong (act c) eq
proj₂ (PK-T-P-asso A X Y Z) ((act a l , act b m) , act c r) (tt , (tt , inj₂ u) , inj₂ v)
  with proj₂ (PK-T-P-asso A X Y Z) ((act a l , act b m) , r) (tt , (tt , u) , v)
... | ((p , tt) , q , tt) , eq = ((p , tt) , (inj₂ q) , tt) , cong (act c) eq






