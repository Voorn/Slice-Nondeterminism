module Monads.Trace where

open import Data.Unit
open import Data.Empty
open import Data.Sum renaming (map to map⊎)
open import Data.Nat hiding (_⊔_)
open import Data.Product renaming (map to map×)
open import Relation.Binary.PropositionalEquality hiding ([_])


open import Slice.Base
open import Slice.Lattice

open import Slice-Functions.Base
open import Slice-Functions.Subcategories
open import Slice-Functions.Monoidal
open import Slice-Functions.Dagger

open import Monads.Free-Monad

SigT : Set → Sig
SigT A = A , (λ x → ⊤)


data Trace (A E X : Set) : Set where
  ret : X → Trace A E X
  act : A → Trace A E X → Trace A E X
  err : E → Trace A E X

-- Note: from the definition, there may seem to be no difference between E and X,
-- but they are separated for their purpose: X is a parameter of results, and operations
-- over traces will need to be natural in X, whereas E is fixed and can be used in decisions

Trace-μ : (A E X : Set) → Trace A E (Trace A E X) → Trace A E X
Trace-μ A E X (ret t) = t
Trace-μ A E X (act a d) = act a (Trace-μ A E X d)
Trace-μ A E X (err e) = err e

Trace-κ : (A E X Y : Set) → (X → Trace A E Y) → (Trace A E X → Trace A E Y)
Trace-κ A E X Y f (ret x) = f x
Trace-κ A E X Y f (act a t) = act a (Trace-κ A E X Y f t)
Trace-κ A E X Y f (err e) = err e


Trace-σ : (A E X Y : Set) → X × Trace A E Y → Trace A E (X × Y)
Trace-σ A E X Y (x , ret y) = ret (x , y)
Trace-σ A E X Y (x , act a t) = act a (Trace-σ A E X Y (x , t))
Trace-σ A E X Y (y , err e) = err e

Trace-ex : {A E X : Set} → Trace A E X → E ⊎ X
Trace-ex (ret x) = inj₂ x
Trace-ex (act a t) = Trace-ex t
Trace-ex (err e) = inj₁ e

Trace-b : (A : Set) → {E X : Set} → E ⊎ X → Trace A E X
Trace-b A (inj₁ e) = err e
Trace-b A (inj₂ x) = ret x

Trace-map : (A E : Set) → {X Y : Set} → (X → Y) → Trace A E X → Trace A E Y
Trace-map A E f (ret x) = ret (f x)
Trace-map A E f (act a t) = act a (Trace-map A E f t)
Trace-map A E f (err e) = err e


SL-act : {A E : Set} → (a : A) → (X : Set) → SL (Trace A E X) → SL (Trace A E X)
SL-act a X = SL-fun (act a)

SL-act-< : {A E : Set} → (a : A) → (X : Set) → (u v : SL (Trace A E X))
  → SL→ (Trace A E X) u v → SL→ (Trace A E X) (SL-act a X u) (SL-act a X v)
SL-act-< a X u v u<v i = (proj₁ (u<v i)) , (cong (act a) (proj₂ (u<v i)))


SF-T : (A E : Set) → {X Y : Set} → SF X Y → SF (Trace A E X) (Trace A E Y)
SF-T A E f (ret x) = proj₁ (f x) , λ i → ret (proj₂ (f x) i)
SF-T A E f (act a t) = SL-act a _ (SF-T A E f t)
SF-T A E f (err e) = SF-id _ (err e)


SF-T-Id :  (A E X : Set) → SF≡ (SF-T A E (SF-id X)) (SF-id (Trace A E X))
proj₁ (SF-T-Id A E X) (ret x) i = tt , refl
proj₁ (SF-T-Id A E X) (act a t) i = tt , (cong (act a) (proj₂ (proj₁ (SF-T-Id A E X) t i)))
proj₁ (SF-T-Id A E X) (err e) i = tt , refl
proj₂ (SF-T-Id A E X) (ret x) i = tt , refl
proj₂ (SF-T-Id A E X) (act a t) i = (proj₁ (proj₂ (SF-T-Id A E X) t i)) ,
  (cong (act a) (proj₂ (proj₂ (SF-T-Id A E X) t i)))
proj₂ (SF-T-Id A E X) (err e) i = tt , refl

SF-T-∘ : (A E : Set) → {X Y Z : Set} → (f : SF X Y) → (g : SF Y Z)
  → SF≡ (SF-T A E (SF-∘ f g)) (SF-∘ (SF-T A E f) (SF-T A E g))
proj₁ (SF-T-∘ A E f g) (ret x) (i , j) = (i , j) , refl
proj₁ (SF-T-∘ A E f g) (act a t) i with proj₁ (SF-T-∘ A E f g) t i
... | u , eq = u , (cong (act a) eq)
proj₁ (SF-T-∘ A E f g) (err e) i = (tt , tt) , refl
proj₂ (SF-T-∘ A E f g) (ret x) (i , j) = (i , j) , refl
proj₂ (SF-T-∘ A E f g) (act a t) (i , j) with proj₂ (SF-T-∘ A E f g) t (i , j)
... | u ,  eq = u , (cong (act a) eq)
proj₂ (SF-T-∘ A E f g) (err e) (i , j) = tt , refl

SF-T-Total : (A E : Set) → {X Y : Set} → (f : SF X Y)
  → (SF-Total f) → SF-Total (SF-T A E f)
SF-T-Total A E f f-tot (ret x) = f-tot x
SF-T-Total A E f f-tot (act a t) = SF-T-Total A E f f-tot t
SF-T-Total A E f f-tot (err e) = tt

SF-T-σ : (A E X Y : Set) → SF (X × Trace A E Y) (Trace A E (X × Y))
SF-T-σ A E X Y = SF-Fun (Trace-σ A E X Y)


-- Naturality on total maps
SF-T-σ-nat< : (A E : Set) → {X X' Y Y' : Set} → (f : SF X X') → (g : SF Y Y')
  → SF≤ (SF-∘ (f ⊗ (SF-T A E g)) (SF-T-σ A E X' Y'))
          (SF-∘ (SF-T-σ A E X Y) (SF-T A E (f ⊗ g)))

SF-T-σ-nat< A E f g (y , ret x) (i , tt) = (tt , i) , refl
SF-T-σ-nat< A E f g (y , act a t) (i , tt)
  with SF-T-σ-nat< A E f g (y , t) (i , tt)
... | u , eq = u , (cong (act a) eq)
SF-T-σ-nat< A E f g (y , err e) (i , tt) = (tt , tt) , refl

SF-T-σ-T-nat> : (A E : Set) → {X X' Y Y' : Set} → (f : SF X X') → (g : SF Y Y')
  → SF-Total f
  → SF≤ (SF-∘ (SF-T-σ A E X Y) (SF-T A E (f ⊗ g)))
          (SF-∘ (f ⊗ (SF-T A E g)) (SF-T-σ A E X' Y'))
SF-T-σ-T-nat> A E f g f-tot (x , ret y) (tt , i , j) = ((i , j) , tt) , refl
SF-T-σ-T-nat> A E f g f-tot (x , act a t) (tt , i)
   with  SF-T-σ-T-nat> A E f g f-tot (x , t) (tt , i)
... | u , eq = u , cong (act a) eq
SF-T-σ-T-nat> A E f g f-tot (x , err e) (tt , i) = ((f-tot x , tt) , tt) , refl

SF-T-σ-T-nat : (A E : Set) → {X X' Y Y' : Set} → (f : SF X X') → (g : SF Y Y')
  → SF-Total f
  → SF≡ (SF-∘ (f ⊗ (SF-T A E g)) (SF-T-σ A E X' Y'))
         (SF-∘ (SF-T-σ A E X Y) (SF-T A E (f ⊗ g)))
SF-T-σ-T-nat A E f g f-tot = (SF-T-σ-nat< A E f g) , (SF-T-σ-T-nat> A E f g f-tot)




SF-T-η : (A E : Set) → (X : Set) → SF X (Trace A E X)
SF-T-η A E X = SF-Fun ret

SF-T-η-nat : (A E : Set) → {X Y : Set} → (f : SF X Y)
  → SF≡ (SF-∘ f (SF-T-η A E Y)) (SF-∘ (SF-T-η A E X) (SF-T A E f))
proj₁ (SF-T-η-nat A E f) x (i , tt) = (tt , i) , refl
proj₂ (SF-T-η-nat A E f) x (tt , i) = (i , tt) , refl

SF-T-η-Total : (A E X : Set) → SF-Total (SF-T-η A E X)
SF-T-η-Total A E X = SF-Fun-Total {X} {Trace A E X} ret


SF-T-μ : (A E : Set) → (X : Set) → SF (Trace A E (Trace A E X)) (Trace A E X)
SF-T-μ A E X = SF-Fun (Trace-μ A E X)

SF-T-μ-nat : (A E : Set) → {X Y : Set} → (f : SF X Y)
  → SF≡ (SF-∘ (SF-T A E (SF-T A E f)) (SF-T-μ A E Y)) (SF-∘ (SF-T-μ A E X) (SF-T A E f))
proj₁ (SF-T-μ-nat A E f) (ret t) (i , tt) = (tt , i) , refl
proj₁ (SF-T-μ-nat A E f) (act a t) i
  with proj₁ (SF-T-μ-nat A E f) t i
... | u , eq = u , (cong (act a) eq)
proj₁ (SF-T-μ-nat A E f) (err e) i = (tt , tt) , refl

proj₂ (SF-T-μ-nat A E f) (ret x) (tt , j) = (j , tt) , refl
proj₂ (SF-T-μ-nat A E f) (act a t) i
  with proj₂ (SF-T-μ-nat A E f) t i
... | u , eq = u , (cong (act a) eq)
proj₂ (SF-T-μ-nat A E f) (err e) i = (tt , tt) , refl

SF-T-μ-Total : (A E X : Set) → SF-Total (SF-T-μ A E X)
SF-T-μ-Total A E X = SF-Fun-Total {_} {Trace A E X} (Trace-μ A E X)



SF-T-κ : {A E : Set} → (X Y : Set) → SF X (Trace A E Y)
                                   → SF (Trace A E X) (Trace A E Y)
SF-T-κ X Y f (ret x) = f x
SF-T-κ X Y f (act a t) = SL-act a Y (SF-T-κ X Y f t)
SF-T-κ X Y f (err e) = SF-id _ (err e)

-- comonad
SF-T-ε : (A E X : Set) → SF (Trace A E X) X
SF-T-ε A E X (ret x) = SF-id _ x
SF-T-ε A E X (act a t) = SL-⊥ _
SF-T-ε A E X (err e) = SL-⊥ _


SF-T-η-rev : (A E X : Set) → SF≡ (SF-∘ (SF-T-η A E X) (SF-T-ε A E X)) (SF-id _)
SF-T-η-rev A E X = (λ x i → tt , refl) , (λ x i → (tt , tt) , refl)


SF-T-ε-Onele : (A E X : Set) → SF-Onele (SF-T-ε A E X)
SF-T-ε-Onele A E X (ret x) i j = refl

SF-T-ε-not-Total : (A E X : Set) → ((A × X) ⊎ E) → SF-Total (SF-T-ε A E X) → ⊥
SF-T-ε-not-Total A E X (inj₁ (a , x)) tot = tot (act a (ret x))
SF-T-ε-not-Total A E X (inj₂ e) tot = tot (err e)

-- The followinng could also be shown indirectly with rev:
SF-T-ε-nat : (A E : Set) → {X Y : Set} → (f : SF X Y)
  → SF≡ (SF-∘ (SF-T A E f) (SF-T-ε A E Y)) (SF-∘ (SF-T-ε A E X) f)
proj₁ (SF-T-ε-nat A E f) (ret x) (i , tt) = (tt , i) , refl
proj₂ (SF-T-ε-nat A E f) (ret x) (tt , i) = (i , tt) , refl




SF-T-δ : (A E : Set) → (X : Set) → SF (Trace A E X) (Trace A E (Trace A E X))
SF-T-δ A E X (ret x) = SF-id _ (ret (ret x))
SF-T-δ A E X (act a t) = join (SF-id _ (ret (act a t)))
                              (SL-act a (Trace A E X) (SF-T-δ A E X t))
SF-T-δ A E X (err e) = (⊤ ⊎ ⊤) , (λ { (inj₁ x) → ret (err e) ;
                                 (inj₂ y) → err e})


SF-T-δ-Total : (A E X : Set) → SF-Total (SF-T-δ A E X)
SF-T-δ-Total A E X (ret x) = tt
SF-T-δ-Total A E X (act a t) = inj₁ tt
SF-T-δ-Total A E X (err e) = inj₁ tt


SF-T-δ-nat : (A E : Set) → {X Y : Set} → (f : SF X Y)
  → SF≡ (SF-∘ (SF-T A E f) (SF-T-δ A E Y)) (SF-∘ (SF-T-δ A E X) (SF-T A E (SF-T A E f)))
proj₁ (SF-T-δ-nat A E f) (ret x) (i , tt) = (tt , i) , refl
proj₁ (SF-T-δ-nat A E f) (act a t) (i , inj₁ tt) = ((inj₁ tt) , i) , refl
proj₁ (SF-T-δ-nat A E f) (act a t) (i , inj₂ j)
  with proj₁ (SF-T-δ-nat A E f) t (i , j)
... | (u , v) , w = ((inj₂ u) , v) , (cong (act a) w)
proj₁ (SF-T-δ-nat A E f) (err e) (tt , inj₁ tt) = ((inj₁ tt) , tt) , refl
proj₁ (SF-T-δ-nat A E f) (err e) (tt , inj₂ tt) = ((inj₂ tt) , tt) , refl
proj₂ (SF-T-δ-nat A E f) (ret x) (tt , i) = (i , tt) , refl
proj₂ (SF-T-δ-nat A E f) (act a t) (inj₁ tt , j) = (j , (inj₁ tt)) , refl
proj₂ (SF-T-δ-nat A E f) (act a t) (inj₂ i , j)
  with proj₂ (SF-T-δ-nat A E f) t (i , j)
... | (u , v) , w = (u , (inj₂ v)) , (cong (act a) w)
proj₂ (SF-T-δ-nat A E f) (err e) (inj₁ tt , j) = (tt , (inj₁ tt)) , refl
proj₂ (SF-T-δ-nat A E f) (err e) (inj₂ tt , j) = (tt , (inj₂ tt)) , refl


SF-T-μ-dag :  (A E X : Set) → SF≡ (SF-dag (SF-T-μ A E X)) (SF-T-δ A E X)
proj₁ (SF-T-μ-dag A E X) (ret x) (ret .(ret x) , tt , refl) = tt , refl
proj₁ (SF-T-μ-dag A E X) (act x t) (ret .(act x t) , tt , refl) = (inj₁ tt) , refl
proj₁ (SF-T-μ-dag A E X) (err x) (ret .(err x) , tt , refl) = (inj₁ tt) , refl
proj₁ (SF-T-μ-dag A E X) .(act a (Trace-μ A E X d)) (act a d , tt , refl)
  with proj₁ (SF-T-μ-dag A E X) (Trace-μ A E X d) (d , (tt , refl))
... | u , v = (inj₂ u) , cong (act a) v
proj₁ (SF-T-μ-dag A E X) .(err e) (err e , tt , refl) = (inj₂ tt) , refl
proj₂ (SF-T-μ-dag A E X) (ret x) tt = ((ret (ret x)) , (tt , refl)) , refl
proj₂ (SF-T-μ-dag A E X) (act a t) (inj₁ tt) = (ret (act a t) , tt , refl) , refl
proj₂ (SF-T-μ-dag A E X) (act a t) (inj₂ y) with proj₂ (SF-T-μ-dag A E X) t y
... | (d , tt , refl) , v = (act a d , tt , refl) , cong (act a) v
proj₂ (SF-T-μ-dag A E X) (err e) (inj₁ tt) = (ret (err e) , (tt , refl)) , refl
proj₂ (SF-T-μ-dag A E X) (err e) (inj₂ tt) = ((err e) , (tt , refl)) , refl


SF-T-δ-asso : (A E X : Set) → SF≡ (SF-∘ (SF-T-δ A E X) (SF-T-δ A E (Trace A E X)))
                                   (SF-∘ (SF-T-δ A E X) (SF-T A E (SF-T-δ A E X)))
proj₁ (SF-T-δ-asso A E X) (ret x) i = (tt , tt) , refl
proj₁ (SF-T-δ-asso A E X) (act a t) (inj₁ i , j) = ((inj₁ tt) , (inj₁ tt)) , refl
proj₁ (SF-T-δ-asso A E X) (act a t) (inj₂ i , inj₁ j) = ((inj₁ tt) , (inj₂ i)) , refl
proj₁ (SF-T-δ-asso A E X) (act a t) (inj₂ i , inj₂ j)
  with proj₁ (SF-T-δ-asso A E X) t (i , j)
... | (u , v) , eq = (inj₂ u , v) , cong (act a) eq
proj₁ (SF-T-δ-asso A E X) (err e) (inj₁ i , j) = ((inj₁ tt) , (inj₁ tt)) , refl
proj₁ (SF-T-δ-asso A E X) (err e) (inj₂ i , inj₁ j) = ((inj₁ tt) , (inj₂ tt)) , refl
proj₁ (SF-T-δ-asso A E X) (err e) (inj₂ i , inj₂ j) = ((inj₂ tt) , tt) , refl

proj₂ (SF-T-δ-asso A E X) (ret x) (i , j) = (tt , tt) , refl
proj₂ (SF-T-δ-asso A E X) (act a t) (inj₁ tt , inj₁ tt) = ((inj₁ tt) , tt) , refl
proj₂ (SF-T-δ-asso A E X) (act a t) (inj₁ tt , inj₂ j) = ((inj₂ j) , inj₁ tt) , refl
proj₂ (SF-T-δ-asso A E X) (act a t) (inj₂ i , j)
  with proj₂ (SF-T-δ-asso A E X) t (i , j)
... | (u , v) , eq = (inj₂ u , inj₂ v) , cong (act a) eq
proj₂ (SF-T-δ-asso A E X) (err x) (inj₁ i , inj₁ tt) = ((inj₁ tt) , tt) , refl
proj₂ (SF-T-δ-asso A E X) (err x) (inj₁ i , inj₂ tt) = ((inj₂ i) , inj₁ tt) , refl
proj₂ (SF-T-δ-asso A E X) (err x) (inj₂ i , j) = ((inj₂ tt) , (inj₂ tt)) , refl

-- Extra structure: The comomonad

SF-T-ηε : (A E X : Set) → SF≡ (SF-∘ (SF-T-η A E X) (SF-T-ε A E X)) (SF-id X)
SF-T-ηε A E X = (λ x i → tt , refl) , (λ x i → (tt , tt) , refl)


SF-T-ηδ : (A E X : Set) → SF≡ (SF-∘ (SF-T-η A E X) (SF-T-δ A E X))
                               (SF-∘ (SF-T-η A E X) (SF-T-η A E (Trace A E X)))
SF-T-ηδ A E X = (λ x i → (tt , tt) , refl) , (λ x i → (tt , tt) , refl)


SF-T-με : (A E X : Set) → SF≡ (SF-∘ (SF-T-μ A E X) (SF-T-ε A E X))
                               (SF-∘ (SF-T-ε A E (Trace A E X)) (SF-T-ε A E X))
proj₁ (SF-T-με A E X) (ret t) (tt , i) = (tt , i) , refl
proj₂ (SF-T-με A E X) (ret t) (tt , i) = (tt , i) , refl


SF-T-δμ : (A E X : Set) → SF≡ (SF-∘ (SF-T-δ A E X) (SF-T-μ A E X)) (SF-id (Trace A E X))

proj₁ (SF-T-δμ A E X) (ret x) i = tt , refl
proj₁ (SF-T-δμ A E X) (act a t) (inj₁ tt , tt) = tt , refl
proj₁ (SF-T-δμ A E X) (act a t) (inj₂ i , tt)
  with proj₁ (SF-T-δμ A E X) t (i , tt)
... | tt , eq = tt , cong (act a) eq
proj₁ (SF-T-δμ A E X) (err e) (inj₁ tt , tt) = tt , refl
proj₁ (SF-T-δμ A E X) (err e) (inj₂ tt , tt) = tt , refl

proj₂ (SF-T-δμ A E X) (ret x) i = (tt , tt) , refl
proj₂ (SF-T-δμ A E X) (act a t) i = ((inj₁ tt) , tt) , refl
proj₂ (SF-T-δμ A E X) (err e) tt = ((inj₁ tt) , tt) , refl




SF-T-χ : (A E X : Set) → SF (Trace A E (Trace A E X)) (Trace A E (Trace A E X))
SF-T-χ A E X = SF-∘ (SF-T-μ A E X) (SF-T-δ A E X)


-- SF-T-><> : (A E X : Set) → SF≡ (SF-∘ (SF-T A E (SF-T-δ A E X))
--   (SF-∘ (SF-T-χ A E (Trace A E X)) (SF-T A E (SF-T-μ A E X))))
--   (SF-T-χ A E X)

-- proj₁ (SF-T-><> A E X) (ret (ret x)) (tt , (tt , tt) , tt) = (tt , tt) , refl
-- proj₁ (SF-T-><> A E X) (ret (act a t)) (inj₁ tt , (tt , tt) , tt) = (tt , (inj₁ tt)) , refl
-- proj₁ (SF-T-><> A E X) (ret (act a t)) (inj₂ i , (tt , inj₁ tt) , p) = (tt , (inj₁ tt)) ,
--   cong ret (cong (act a) (proj₂ (proj₁ (SF-T-δμ A E X) t (i , tt))))
-- proj₁ (SF-T-><> A E X) (ret (act a t)) (inj₂ i , (tt , inj₂ j) , p)
--   with proj₁ (SF-T-><> A E X) (ret t) (i , (tt , j) , p)
-- ... | (tt , u) , w = (tt , (inj₂ u)) , (cong (act a) w)
-- proj₁ (SF-T-><> A E X) (ret (err e)) (inj₁ tt , (tt , tt) , tt) = (tt , (inj₁ tt)) , refl
-- proj₁ (SF-T-><> A E X) (ret (err e)) (inj₂ tt , (tt , inj₁ tt) , tt) =
--   (tt , (inj₁ tt)) , refl
-- proj₁ (SF-T-><> A E X) (ret (err e)) (inj₂ tt , (tt , inj₂ tt) , tt) =
--   (tt , (inj₂ tt)) , refl
-- proj₁ (SF-T-><> A E X) (act a d) (i , (tt , inj₁ tt) , tt) = (tt , (inj₁ tt)) ,
--   (cong ret (cong (act a) {!SF-T-μ-as!}))
-- proj₁ (SF-T-><> A E X) (act a d) (i , (tt , inj₂ j) , p) = {!!}
-- proj₁ (SF-T-><> A E X) (err e) (i , (j , l) , p) = {!!}

-- proj₂ (SF-T-><> A E X) d i = {!!}



-- Maybe
Maybe : Set → Set
Maybe X = X ⊎ ⊤

SF-M : {X Y : Set} → (SF X Y) → (SF (Maybe X) (Maybe Y))
SF-M f (inj₁ x) = (proj₁ (f x)) , (λ i → inj₁ (proj₂ (f x) i))
SF-M f (inj₂ y) = ⊤ , (λ x → inj₂ tt)


SF-M-η : (X : Set) → SF X (Maybe X)
SF-M-η X = SF-Fun inj₁

SF-M-μ : (X : Set) → SF (Maybe (Maybe X)) (Maybe X)
SF-M-μ X (inj₁ x) = SF-id _ x
SF-M-μ X (inj₂ y) = SF-id _ (inj₂ tt)


-- Error
Error : Set → Set → Set
Error E X = X ⊎ E

SF-E : (E : Set) → {X Y : Set} → (SF X Y) → (SF (Error E X) (Error E Y))
SF-E E f (inj₁ x) = (proj₁ (f x)) , (λ i → inj₁ (proj₂ (f x) i))
SF-E E f (inj₂ e) = ⊤ , (λ x → inj₂ e)



SF-T-in : {A E X Y : Set} → (f : SF X Y) → (SF-Total f) → (t : Trace A E X)
  → proj₁ (SF-T A E f t)
SF-T-in f f-tot (ret x) = f-tot x
SF-T-in f f-tot (act x t) = SF-T-in f f-tot t
SF-T-in f f-tot (err x) = tt





-- -- Partial Runners
-- T-Runner : (A E S : Set) → Set₁
-- T-Runner A E S = (A → SF S (Maybe S))

-- T-Runner-Total : {A E S : Set} → T-Runner A E S → Set
-- T-Runner-Total {A} θ = (a : A) → SF-Total (θ a)

-- T-Runner-map : {A E : Set} → (S : Set) → (θ : T-Runner A E S)
--   → (X : Set) → (s : S) → SF (Trace A E X) (Maybe (S × X))
-- T-Runner-map S θ X s (ret x) = SF-id _ (inj₁ (s , x))
-- T-Runner-map S θ X s (act a t) = SL-κ _ _
--   (λ {(inj₁ z) → T-Runner-map S θ X z t ; (inj₂ tt) → SF-id _ (inj₂ tt)}) (θ a s)
-- T-Runner-map S θ X s (err x) = SF-id _ (inj₂ tt)



-- T-Runner-map-Total : {A E : Set} → (S : Set)
--   → (θ : T-Runner A E S) → (T-Runner-Total {A} {E} {S} θ)
--   → (X : Set) → (s : S) → SF-Total (T-Runner-map {A} {E} S θ X s)
-- T-Runner-map-Total S θ θ-tot X s (ret x) = tt
-- proj₁ (T-Runner-map-Total S θ θ-tot X s (act x t)) = θ-tot x s
-- proj₂ (T-Runner-map-Total S θ θ-tot X s (act x t)) with (proj₂ (θ x s) (θ-tot x s))
-- ... | inj₁ a = T-Runner-map-Total S θ θ-tot X a t
-- ... | inj₂ b = tt
-- T-Runner-map-Total S θ θ-tot X s (err x) = tt


-- T-Runner-map-nat< : {A E : Set} → (S : Set) → (θ : T-Runner A E S)
--   → {X Y : Set} → (f : SF X Y) → (s : S)
--   → SF≤ (SF-∘ (SF-T A E f) (T-Runner-map S θ Y s))
--           (SF-∘ (T-Runner-map S θ X s) (SF-M (SF-id S ⊗ f)))
-- T-Runner-map-nat< S θ f s (ret x) (i , tt) = (tt , (tt , i)) , refl
-- proj₁ (proj₁ (proj₁ (T-Runner-map-nat< S θ f s (act x t) (i , j , k)))) = j
-- proj₂ (proj₁ (proj₁ (T-Runner-map-nat< S θ f s (act x t) (i , j , k)))) with proj₂ (θ x s) j
-- ... | inj₁ a = proj₁ (proj₁ (T-Runner-map-nat< S θ f a t (i , k)))
-- ... | inj₂ b = tt
-- proj₂ (proj₁ (T-Runner-map-nat< S θ f s (act x t) (i , j , k))) with proj₂ (θ x s) j
-- ... | inj₁ a = proj₂ (proj₁ (T-Runner-map-nat< S θ f a t (i , k)))
-- ... | inj₂ b = tt
-- proj₂ (T-Runner-map-nat< S θ f s (act x t) (i , j , k)) with proj₂ (θ x s) j
-- ... | inj₁ a = proj₂ (T-Runner-map-nat< S θ f a t (i , k))
-- ... | inj₂ b = refl
-- T-Runner-map-nat< S θ f s (err x) (i , j) = (tt , tt) , refl


-- T-Runner-map-T-nat> : {A E : Set} → (S : Set) → (θ : T-Runner A E S)
--   → {X Y : Set} → (f : SF X Y) → (SF-Total f) → (s : S)
--   → SF≤ (SF-∘ (T-Runner-map S θ X s) (SF-M (SF-id S ⊗ f)))
--           (SF-∘ (SF-T A E f) (T-Runner-map S θ Y s))
          
-- T-Runner-map-T-nat> S θ f f-tot s (ret x) (tt , tt , j) = (j , tt) , refl
-- proj₁ (proj₁ (T-Runner-map-T-nat> S θ f f-tot s (act x t) ((i , j) , k)))
--   with proj₂ (θ x s) i
-- ... | inj₁ a = proj₁ (proj₁ (T-Runner-map-T-nat> S θ f f-tot a t (j , k)))
-- ... | inj₂ b = SF-T-in f f-tot t
-- proj₁ (proj₂ (proj₁ (T-Runner-map-T-nat> S θ f f-tot s (act x t) ((i , j) , k)))) = i
-- proj₂ (proj₂ (proj₁ (T-Runner-map-T-nat> S θ f f-tot s (act x t) ((i , j) , k))))
--   with proj₂ (θ x s) i
-- ... | inj₁ a = proj₂ (proj₁ (T-Runner-map-T-nat> S θ f f-tot a t (j , k)))
-- ... | inj₂ b = tt
-- proj₂ (T-Runner-map-T-nat> S θ f f-tot s (act x t) ((i , j) , k)) with proj₂ (θ x s) i
-- ... | inj₁ a = proj₂ (T-Runner-map-T-nat> S θ f f-tot a t (j , k))
-- ... | inj₂ b = refl
-- T-Runner-map-T-nat> S θ f f-tot s (err x) (i , j) = (tt , tt) , refl

-- T-Runner-map-T-nat : {A E : Set} → (S : Set) → (θ : T-Runner A E S)
--   → {X Y : Set} → (f : SF X Y) → (SF-Total f) → (s : S)
--   → SF≡ (SF-∘ (SF-T A E f) (T-Runner-map S θ Y s))
--          (SF-∘ (T-Runner-map S θ X s) (SF-M (SF-id S ⊗ f)))
-- T-Runner-map-T-nat S θ f f-tot s = T-Runner-map-nat< S θ f s ,
--                                    T-Runner-map-T-nat> S θ f f-tot s


-- T-Runner-map-η : {A E : Set} → (S : Set) → (θ : T-Runner A E S)
--   → (X : Set) → (s : S)
--   → SF≡ (SF-∘ (SF-T-η A E X) (T-Runner-map S θ X s))
--          (SF-∘ (SF-Fun (λ x → (s , x))) (SF-M-η (S × X)))
-- proj₁ (T-Runner-map-η S θ X s) x i = (tt , tt) , refl
-- proj₂ (T-Runner-map-η S θ X s) x i = (tt , tt) , refl




-- T-Runner-map-μ : {A E : Set} → (S : Set) → (θ : T-Runner A E S)
--   → (X : Set) → (s : S)
--   → SF≡ (SF-∘ (SF-T-μ A E X) (T-Runner-map S θ X s))
--          (SF-∘ (T-Runner-map S θ (Trace A E X) s)
--                (SF-∘ (SF-M (cur (T-Runner-map S θ X))) (SF-M-μ (S × X))))

-- proj₁ (T-Runner-map-μ S θ X s) (ret t) (tt , i) = (tt , (i , tt)) , refl
-- proj₁ (proj₁ (proj₁ (proj₁ (T-Runner-map-μ S θ X s) (act a d) (tt , i , j)))) = i
-- proj₂ (proj₁ (proj₁ (proj₁ (T-Runner-map-μ S θ X s) (act a d) (tt , i , j))))
--   with (proj₂ (θ a s) i)
-- ... | inj₁ z = proj₁ (proj₁ (proj₁ (T-Runner-map-μ S θ X z) d (tt , j)))
-- ... | inj₂ tt = tt
-- proj₂ (proj₁ (proj₁ (T-Runner-map-μ S θ X s) (act a d) (tt , i , j))) with (proj₂ (θ a s) i)
-- ... | inj₁ z = (proj₂ (proj₁ (proj₁ (T-Runner-map-μ S θ X z) d (tt , j))))
-- ... | inj₂ tt = tt , tt
-- proj₂ (proj₁ (T-Runner-map-μ S θ X s) (act a d) (tt , i , j)) with (proj₂ (θ a s) i)
-- ... | inj₁ z = proj₂ (proj₁ (T-Runner-map-μ S θ X z) d (tt , j))
-- ... | inj₂ tt = refl
-- proj₁ (T-Runner-map-μ S θ X s) (err x) (tt , i) = (tt , (tt , tt)) , refl

-- proj₂ (T-Runner-map-μ S θ X s) (ret d) (tt , j , tt) = (tt , j) , refl
-- proj₁ (proj₁ (proj₂ (T-Runner-map-μ S θ X s) (act a d) ((i , v) , j , k))) = tt
-- proj₁ (proj₂ (proj₁ (proj₂ (T-Runner-map-μ S θ X s) (act a d) ((i , v) , j , k)))) = i
-- proj₂ (proj₂ (proj₁ (proj₂ (T-Runner-map-μ S θ X s) (act a d) ((i , v) , j , k))))
--    with (proj₂ (θ a s) i)
-- ... | inj₁ z = proj₂ (proj₁ (proj₂ (T-Runner-map-μ S θ X z) d (v , (j , k))))
-- ... | inj₂ tt = tt
-- proj₂ (proj₂ (T-Runner-map-μ S θ X s) (act a d) ((i , v) , j , k))
--    with (proj₂ (θ a s) i)
-- ... | inj₁ z = proj₂ (proj₂ (T-Runner-map-μ S θ X z) d (v , (j , k)))
-- ... | inj₂ tt = refl
-- proj₂ (T-Runner-map-μ S θ X s) (err e) (tt , tt , tt) = (tt , tt) , refl


-- -- SF-T-ε : (A E : Set) → (X : Set) → SF (Trace A E X) X
-- -- SF-T-ε A E X (ret x) = SF-id X x
-- -- SF-T-ε A E X (act x t) = ⊥ , (λ ())

-- -- SF-T-η<>ε : (A E X : Set) → SF≡ (SF-T-ε A E X) (SF-dag (SF-T-η A E X))
-- -- proj₁ (SF-T-η<>ε A E X) (ret x) tt = (x , (tt , refl)) , refl
-- -- proj₂ (SF-T-η<>ε A E X) (ret x) (.x , tt , refl) = tt , refl


-- -- SF-T-δ : (A E : Set) → (X : Set) → SF (Trace A E X) (Trace A E (Trace A E X))
-- -- SF-T-δ A E X (ret x) = SF-id (Trace A E (Trace A E X)) (ret (ret x))
-- -- SF-T-δ A E X (act a t) = join (SF-id (Trace A E (Trace A E X)) (ret (act a t)))
-- --                             (SL-act a (Trace A E X) (SF-T-δ A E X t))


-- -- SF-T-μ<>δ : (A E X : Set) → SF≡ (SF-T-δ A E X) (SF-dag (SF-T-μ A E X))
-- -- proj₁ (SF-T-μ<>δ A E X) (ret x) tt = (ret (ret x) , tt , refl) , refl
-- -- proj₁ (SF-T-μ<>δ A E X) (act a t) (inj₁ i) = ((ret (act a t)) , (tt , refl)) , refl
-- -- proj₁ (SF-T-μ<>δ A E X) (act a t) (inj₂ i) with (proj₁ (SF-T-μ<>δ A E X) t i)
-- -- ... | (d , p , v) , eq = (act a d , (p , cong (act a) v)) , cong (act a) eq
-- -- proj₂ (SF-T-μ<>δ A E X) (ret x) (ret .(ret x) , tt , refl) = tt , refl
-- -- proj₂ (SF-T-μ<>δ A E X) (act a t) (ret .(act a t) , tt , refl) = (inj₁ tt) , refl
-- -- proj₂ (SF-T-μ<>δ A E X) (act a .(proj₂ (SF-T-μ A E X d) i)) (act .a d , i , refl)
-- --   with proj₂ (SF-T-μ<>δ A E X) (proj₂ (SF-T-μ A E X d) i) (d , i , refl)
-- -- ... | j , eq = (inj₂ j) , (cong (act a) eq)
