module Runner where

open import Data.Unit
open import Data.Empty
open import Data.Sum renaming (map to map⊎)
open import Data.Nat hiding (_⊔_)
open import Data.Product renaming (map to map×)
open import Relation.Binary.PropositionalEquality hiding ([_])


open import Index-Nondeterminism
open import Free-Monad
open import Monoidal


-- State Monad

State : Set → Set → Set
State M X = M → X × M

State-mor : (M : Set) → {X Y : Set} → PK-Hom X Y → PK-Hom (State M X) (State M Y)
State-mor M f s = ((m : M) → proj₁ (f (proj₁ (s m)))) ,
  (λ i m → proj₂ (f (proj₁ (s m))) (i m) , proj₂ (s m))

State-mor-Id : (M X : Set) → PK-≡ (State-mor M (PK-Id X)) (PK-Id (State M X))
proj₁ (State-mor-Id M X) x i = tt , refl
proj₂ (State-mor-Id M X) x tt = (λ m → tt) , refl

State-mor-∘ : (M : Set) → {X Y Z : Set} → (f : PK-Hom X Y) → (g : PK-Hom Y Z)
  → PK-≡ (State-mor M (PK-∘ f g)) (PK-∘ (State-mor M f) (State-mor M g))
proj₁ (State-mor-∘ M f g) x i = ((λ m → proj₁ (i m)) , (λ m → proj₂ (i m))) , refl
proj₂ (State-mor-∘ M f g) x (i , j) = (λ m → (i m , j m)) , refl



State-η : (M X : Set) → PK-Hom X (State M X)
State-η M X x = PK-Id _ (λ m → x , m)

--State-η-nat : (M : Set) → {X Y : Set} → (f : PK-Hom X Y)
--  → PK-≡ (PK-∘ f (State-η M Y)) (PK-∘ (State-η M X) (State-mor M f))
--proj₁ (State-η-nat M f) x (i , tt) = (tt , (λ m → i)) , refl
--proj₂ (State-η-nat M f) x (tt , im) = ({!!} , {!!}) , {!!}



State-μ : (M X : Set) → PK-Hom (State M (State M X)) (State M X)
State-μ M X d = PK-Id _ (λ x → proj₁ (d x) (proj₂ (d x)))


--State-μ-nat : (M : Set) → {X Y : Set} → (f : PK-Hom X Y) → PK-≡
--  (PK-∘ (State-mor M (State-mor M f)) (State-μ M Y)) (PK-∘ (State-μ M X) (State-mor M f))
--proj₁ (State-μ-nat M f) = {!!}
--proj₂ (State-μ-nat M f) = {!!}



Runner : Sig → Set → Set₁
Runner (A , B) M = (σ : A) → PK-Hom M ((B σ) × M)


R-map-cur : (S : Sig) → (M : Set) → Runner S M → (X : Set) → M → PK-Hom (Free S X) (X × M)
R-map-cur S M ϕ X m (leaf x) = PK-Id _ (x , m)
R-map-cur S M ϕ X m (node σ ts) =
  Pow-κ _ _ (λ i → R-map-cur S M ϕ X (proj₂ i) (ts (proj₁ i))) (ϕ σ m)


R-map :  (S : Sig) → (M : Set) → Runner S M → (X : Set) → PK-Hom ((Free S X) × M) (X × M)
R-map S M ϕ X (t , m) = R-map-cur S M ϕ X m t

R-map-snat-cur : (S : Sig) → (M : Set) → (ϕ : Runner S M) → {X Y : Set} → (f : X → Y)
  → (m : M)
  → PK-≡ (PK-∘ (PK-F S (PK-Fun f)) (R-map-cur S M ϕ Y m))
         (PK-∘ (R-map-cur S M ϕ X m) ((PK-Fun f) ⊗ PK-Id _))
proj₁ (R-map-snat-cur S M ϕ f m) (leaf x) (tt , tt) = (tt , (tt , tt)) , refl
proj₁ (R-map-snat-cur S M ϕ f m) (node σ ts) (i , j , k)
  with proj₁ (R-map-snat-cur S M ϕ f (proj₂ (proj₂ (ϕ σ m) j)))
       (ts (proj₁ (proj₂ (ϕ σ m) j))) (i (proj₁ (proj₂ (ϕ σ m) j)) , k)
... | (u , v , tt) , eq = ((j , u) , (v , tt)) , eq
proj₂ (R-map-snat-cur S M ϕ f m) (leaf x) (i , tt , tt) = (tt , tt) , refl
proj₁ (proj₁ (proj₂ (R-map-snat-cur S M ϕ f m) (node σ ts) (i , tt , tt))) =
  (λ c → Pos-In S _ (λ x → ⊤) (ts c) (λ x → tt))
proj₂ (proj₁ (proj₂ (R-map-snat-cur S M ϕ f m) (node σ ts) (i , tt , tt))) = (proj₁ i) ,
  {!proj₂ (proj₁ (proj₂ (R-map-snat-cur S M ϕ f (proj₂ (proj₂ (ϕ σ m) (proj₁ i)))) (ts (proj₁ (proj₂ (ϕ σ m) (proj₁ i)))) (proj₂ i , tt , tt)))!}

R-map-nat-cur : (S : Sig) → (M : Set) → (ϕ : Runner S M) → {X Y : Set} → (f : PK-Hom X Y)
  → (m : M)
  → PK-≡ (PK-∘ (PK-F S f) (R-map-cur S M ϕ Y m)) (PK-∘ (R-map-cur S M ϕ X m) (f ⊗ PK-Id _))
proj₁ (R-map-nat-cur S M ϕ f m) (leaf x) (i , tt) = (tt , (i , tt)) , refl
proj₁ (R-map-nat-cur S M ϕ f m) (node σ ts) (i , j , k)
  with proj₁ (R-map-nat-cur S M ϕ f (proj₂ (proj₂ (ϕ σ m) j))) (ts (proj₁ (proj₂ (ϕ σ m) j)))
  ((i (proj₁ (proj₂ (ϕ σ m) j))) , k)
... | (u , v , tt) , eq = ((j , u) , (v , tt)) , eq
proj₂ (R-map-nat-cur S M ϕ f m) (leaf x) (tt , i , tt) = (i , tt) , refl
proj₂ (R-map-nat-cur S M ϕ f m) (node σ ts) ((i , j) , k , tt)
      = ((λ c → proj₁ (proj₁ (proj₂ (R-map-nat-cur S M ϕ f m) (ts c) ({!j!} , {!!})))) , {!!}) , {!!}

R-map-nat : (S : Sig) → (M : Set) → (ϕ : Runner S M) → {X Y : Set} → (f : PK-Hom X Y)
  → PK-≡ (PK-∘ ((PK-F S f) ⊗ PK-Id _) (R-map S M ϕ Y)) (PK-∘ (R-map S M ϕ X) (f ⊗ PK-Id _))


R-map-η : (S : Sig) → (M : Set) → (ϕ : Runner S M) → (X : Set)
  → PK-≡ (PK-∘ ((PK-F-η S X) ⊗ PK-Id _) (R-map S M ϕ X)) (PK-Id _)
proj₁ (R-map-η S M ϕ X) x i = tt , refl
proj₂ (R-map-η S M ϕ X) x i = ((tt , tt) , tt) , refl



R-map-μ-cur : (S : Sig) → (M : Set) → (ϕ : Runner S M) → (X : Set) → (m : M)
  → PK-≡ (PK-∘ (PK-F-μ S X) (R-map-cur S M ϕ X m))
         (PK-∘ (R-map-cur S M ϕ (Free S X) m) (R-map S M ϕ X))
proj₁ (R-map-μ-cur S M ϕ X m) (leaf x) i = i , refl
proj₁ (R-map-μ-cur S M ϕ X m) (node σ ts) (tt , i , j) =
  ((i , (proj₁ (proj₁ (proj₁ (R-map-μ-cur S M ϕ X (proj₂ (proj₂ (ϕ σ m) i)))
               (ts (proj₁ (proj₂ (ϕ σ m) i))) (tt , j))))) ,
        (proj₂ (proj₁ (proj₁ (R-map-μ-cur S M ϕ X (proj₂ (proj₂ (ϕ σ m) i)))
               (ts (proj₁ (proj₂ (ϕ σ m) i))) (tt , j))))) ,
  (proj₂ (proj₁ (R-map-μ-cur S M ϕ X (proj₂ (proj₂ (ϕ σ m) i)))
               (ts (proj₁ (proj₂ (ϕ σ m) i))) (tt , j)))
proj₂ (R-map-μ-cur S M ϕ X m) (leaf x) i = i , refl
proj₂ (R-map-μ-cur S M ϕ X m) (node σ ts) ((i , j) , k) = (tt , (i ,
  (proj₂ (proj₁ (proj₂ (R-map-μ-cur S M ϕ X (proj₂ (proj₂ (ϕ σ m) i)))
               (ts (proj₁ (proj₂ (ϕ σ m) i))) (j , k)))))) ,
  proj₂ (proj₂ (R-map-μ-cur S M ϕ X (proj₂ (proj₂ (ϕ σ m) i)))
               (ts (proj₁ (proj₂ (ϕ σ m) i))) (j , k))

R-map-μ : (S : Sig) → (M : Set) → (ϕ : Runner S M) → (X : Set) 
  → PK-≡ (PK-∘ (PK-F-μ S X ⊗ PK-Id _) (R-map S M ϕ X))
         (PK-∘ (R-map S M ϕ (Free S X)) (R-map S M ϕ X))
proj₁ (R-map-μ S M ϕ X) (d , m) ((tt , tt) , i) = proj₁ (R-map-μ-cur S M ϕ X m) d (tt , i)
proj₂ (R-map-μ S M ϕ X) (d , m) (i , j) = ((tt , tt) ,
  (proj₂ (proj₁ (proj₂ (R-map-μ-cur S M ϕ X m) d (i , j))))) ,
  (proj₂ (proj₂ (R-map-μ-cur S M ϕ X m) d (i , j)))
