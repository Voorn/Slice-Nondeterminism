module Trace where

open import Data.Unit
open import Data.Empty
open import Data.Sum renaming (map to map⊎)
open import Data.Nat hiding (_⊔_)
open import Data.Product renaming (map to map×)
open import Relation.Binary.PropositionalEquality hiding ([_])


open import Index-Nondeterminism
open import Monoidal
open import Free-Monad

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


--PK-T : (A E : Set) → {X Y : Set} → PK-Hom X Y → PK-Hom (Trace A E X) (Trace A E Y)
--proj₁ (PK-T A E f t) with Trace-ex t
--... | inj₁ e = ⊤
--... | inj₂ x = proj₁ (f x)
--proj₂ (PK-T A E f (ret x)) i = ret (proj₂ (f x) i)
--proj₂ (PK-T A E f (act a t)) i  with Trace-ex t
--... | inj₁ e = {!!}
--... | inj₂ x = act a (proj₂ (PK-T A E f t) {!!})


Pow-act : {A E : Set} → (a : A) → (X : Set) → Pow (Trace A E X) → Pow (Trace A E X)
Pow-act a X = Pow→ (act a)

Pow-act-< : {A E : Set} → (a : A) → (X : Set) → (u v : Pow (Trace A E X))
  → Pow-Γ≡ (Trace A E X) u v → Pow-Γ≡ (Trace A E X) (Pow-act a X u) (Pow-act a X v)
Pow-act-< a X u v u<v i = (proj₁ (u<v i)) , (cong (act a) (proj₂ (u<v i)))


PK-T : (A E : Set) → {X Y : Set} → PK-Hom X Y → PK-Hom (Trace A E X) (Trace A E Y)
PK-T A E f (ret x) = proj₁ (f x) , λ i → ret (proj₂ (f x) i)
PK-T A E f (act a t) = Pow-act a _ (PK-T A E f t)
PK-T A E f (err e) = PK-Id _ (err e)

PK-T-Total : (A E : Set) → {X Y : Set} → (f : PK-Hom X Y)
  → (PK-Total f) → PK-Total (PK-T A E f)
PK-T-Total A E f f-tot (ret x) = f-tot x
PK-T-Total A E f f-tot (act a t) = PK-T-Total A E f f-tot t
PK-T-Total A E f f-tot (err e) = tt

PK-T-σ : (A E X Y : Set) → PK-Hom (X × Trace A E Y) (Trace A E (X × Y))
PK-T-σ A E X Y = PK-Fun (Trace-σ A E X Y)


-- Naturality on total maps
PK-T-σ-nat< : (A E : Set) → {X X' Y Y' : Set} → (f : PK-Hom X X') → (g : PK-Hom Y Y')
  → Pow-< (PK-∘ (f ⊗ (PK-T A E g)) (PK-T-σ A E X' Y'))
          (PK-∘ (PK-T-σ A E X Y) (PK-T A E (f ⊗ g)))

PK-T-σ-nat< A E f g (y , ret x) (i , tt) = (tt , i) , refl
PK-T-σ-nat< A E f g (y , act a t) (i , tt)
  with PK-T-σ-nat< A E f g (y , t) (i , tt)
... | u , eq = u , (cong (act a) eq)
PK-T-σ-nat< A E f g (y , err e) (i , tt) = (tt , tt) , refl

PK-T-σ-T-nat> : (A E : Set) → {X X' Y Y' : Set} → (f : PK-Hom X X') → (g : PK-Hom Y Y')
  → PK-Total f
  → Pow-< (PK-∘ (PK-T-σ A E X Y) (PK-T A E (f ⊗ g)))
          (PK-∘ (f ⊗ (PK-T A E g)) (PK-T-σ A E X' Y'))
PK-T-σ-T-nat> A E f g f-tot (x , ret y) (tt , i , j) = ((i , j) , tt) , refl
PK-T-σ-T-nat> A E f g f-tot (x , act a t) (tt , i)
   with  PK-T-σ-T-nat> A E f g f-tot (x , t) (tt , i)
... | u , eq = u , cong (act a) eq
PK-T-σ-T-nat> A E f g f-tot (x , err e) (tt , i) = ((f-tot x , tt) , tt) , refl

PK-T-σ-T-nat : (A E : Set) → {X X' Y Y' : Set} → (f : PK-Hom X X') → (g : PK-Hom Y Y')
  → PK-Total f
  → PK-≡ (PK-∘ (f ⊗ (PK-T A E g)) (PK-T-σ A E X' Y'))
         (PK-∘ (PK-T-σ A E X Y) (PK-T A E (f ⊗ g)))
PK-T-σ-T-nat A E f g f-tot = (PK-T-σ-nat< A E f g) , (PK-T-σ-T-nat> A E f g f-tot)




PK-T-η : (A E : Set) → (X : Set) → PK-Hom X (Trace A E X)
PK-T-η A E X = PK-Fun ret

PK-T-η-nat : (A E : Set) → {X Y : Set} → (f : PK-Hom X Y)
  → PK-≡ (PK-∘ f (PK-T-η A E Y)) (PK-∘ (PK-T-η A E X) (PK-T A E f))
proj₁ (PK-T-η-nat A E f) x (i , tt) = (tt , i) , refl
proj₂ (PK-T-η-nat A E f) x (tt , i) = (i , tt) , refl

PK-T-η-Total : (A E X : Set) → PK-Total (PK-T-η A E X)
PK-T-η-Total A E X = PK-Fun-Total {X} {Trace A E X} ret


PK-T-μ : (A E : Set) → (X : Set) → PK-Hom (Trace A E (Trace A E X)) (Trace A E X)
PK-T-μ A E X = PK-Fun (Trace-μ A E X)

PK-T-μ-nat : (A E : Set) → {X Y : Set} → (f : PK-Hom X Y)
  → PK-≡ (PK-∘ (PK-T A E (PK-T A E f)) (PK-T-μ A E Y)) (PK-∘ (PK-T-μ A E X) (PK-T A E f))
proj₁ (PK-T-μ-nat A E f) (ret t) (i , tt) = (tt , i) , refl
proj₁ (PK-T-μ-nat A E f) (act a t) i
  with proj₁ (PK-T-μ-nat A E f) t i
... | u , eq = u , (cong (act a) eq)
proj₁ (PK-T-μ-nat A E f) (err e) i = (tt , tt) , refl

proj₂ (PK-T-μ-nat A E f) (ret x) (tt , j) = (j , tt) , refl
proj₂ (PK-T-μ-nat A E f) (act a t) i
  with proj₂ (PK-T-μ-nat A E f) t i
... | u , eq = u , (cong (act a) eq)
proj₂ (PK-T-μ-nat A E f) (err e) i = (tt , tt) , refl

PK-T-μ-Total : (A E X : Set) → PK-Total (PK-T-μ A E X)
PK-T-μ-Total A E X = PK-Fun-Total {_} {Trace A E X} (Trace-μ A E X)



PK-T-κ : {A E : Set} → (X Y : Set) → PK-Hom X (Trace A E Y)
                                   → PK-Hom (Trace A E X) (Trace A E Y)
PK-T-κ X Y f (ret x) = f x
PK-T-κ X Y f (act a t) = Pow-act a Y (PK-T-κ X Y f t)
PK-T-κ X Y f (err e) = PK-Id _ (err e)

-- comonad
PK-T-ε : (A E X : Set) → PK-Hom (Trace A E X) X
PK-T-ε A E X (ret x) = PK-Id _ x
PK-T-ε A E X (act a t) = Pow-⊥ _
PK-T-ε A E X (err e) = Pow-⊥ _


PK-T-η-rev : (A E X : Set) → PK-≡ (PK-∘ (PK-T-η A E X) (PK-T-ε A E X)) (PK-Id _)
PK-T-η-rev A E X = (λ x i → tt , refl) , (λ x i → (tt , tt) , refl)


PK-T-ε-Onele : (A E X : Set) → PK-Onele (PK-T-ε A E X)
PK-T-ε-Onele A E X (ret x) i j = refl

PK-T-ε-not-Total : (A E X : Set) → ((A × X) ⊎ E) → PK-Total (PK-T-ε A E X) → ⊥
PK-T-ε-not-Total A E X (inj₁ (a , x)) tot = tot (act a (ret x))
PK-T-ε-not-Total A E X (inj₂ e) tot = tot (err e)

-- The followinng could also be shown indirectly with rev:
PK-T-ε-nat : (A E : Set) → {X Y : Set} → (f : PK-Hom X Y)
  → PK-≡ (PK-∘ (PK-T A E f) (PK-T-ε A E Y)) (PK-∘ (PK-T-ε A E X) f)
proj₁ (PK-T-ε-nat A E f) (ret x) (i , tt) = (tt , i) , refl
proj₂ (PK-T-ε-nat A E f) (ret x) (tt , i) = (i , tt) , refl




PK-T-δ : (A E : Set) → (X : Set) → PK-Hom (Trace A E X) (Trace A E (Trace A E X))
PK-T-δ A E X (ret x) = PK-Id _ (ret (ret x))
PK-T-δ A E X (act a t) = join (PK-Id _ (ret (act a t)))
                              (Pow-act a (Trace A E X) (PK-T-δ A E X t))
PK-T-δ A E X (err e) = (⊤ ⊎ ⊤) , (λ { (inj₁ x) → ret (err e) ;
                                 (inj₂ y) → err e})


PK-T-δ-Total : (A E X : Set) → PK-Total (PK-T-δ A E X)
PK-T-δ-Total A E X (ret x) = tt
PK-T-δ-Total A E X (act a t) = inj₁ tt
PK-T-δ-Total A E X (err e) = inj₁ tt


PK-T-δ-nat : (A E : Set) → {X Y : Set} → (f : PK-Hom X Y)
  → PK-≡ (PK-∘ (PK-T A E f) (PK-T-δ A E Y)) (PK-∘ (PK-T-δ A E X) (PK-T A E (PK-T A E f)))
proj₁ (PK-T-δ-nat A E f) (ret x) (i , tt) = (tt , i) , refl
proj₁ (PK-T-δ-nat A E f) (act a t) (i , inj₁ tt) = ((inj₁ tt) , i) , refl
proj₁ (PK-T-δ-nat A E f) (act a t) (i , inj₂ j)
  with proj₁ (PK-T-δ-nat A E f) t (i , j)
... | (u , v) , w = ((inj₂ u) , v) , (cong (act a) w)
proj₁ (PK-T-δ-nat A E f) (err e) (tt , inj₁ tt) = ((inj₁ tt) , tt) , refl
proj₁ (PK-T-δ-nat A E f) (err e) (tt , inj₂ tt) = ((inj₂ tt) , tt) , refl
proj₂ (PK-T-δ-nat A E f) (ret x) (tt , i) = (i , tt) , refl
proj₂ (PK-T-δ-nat A E f) (act a t) (inj₁ tt , j) = (j , (inj₁ tt)) , refl
proj₂ (PK-T-δ-nat A E f) (act a t) (inj₂ i , j)
  with proj₂ (PK-T-δ-nat A E f) t (i , j)
... | (u , v) , w = (u , (inj₂ v)) , (cong (act a) w)
proj₂ (PK-T-δ-nat A E f) (err e) (inj₁ tt , j) = (tt , (inj₁ tt)) , refl
proj₂ (PK-T-δ-nat A E f) (err e) (inj₂ tt , j) = (tt , (inj₂ tt)) , refl


PK-T-μ-rev :  (A E X : Set) → PK-≡ (PK-rev (PK-T-μ A E X)) (PK-T-δ A E X)
proj₁ (PK-T-μ-rev A E X) (ret x) (ret .(ret x) , tt , refl) = tt , refl
proj₁ (PK-T-μ-rev A E X) (act x t) (ret .(act x t) , tt , refl) = (inj₁ tt) , refl
proj₁ (PK-T-μ-rev A E X) (err x) (ret .(err x) , tt , refl) = (inj₁ tt) , refl
proj₁ (PK-T-μ-rev A E X) .(act a (Trace-μ A E X d)) (act a d , tt , refl)
  with proj₁ (PK-T-μ-rev A E X) (Trace-μ A E X d) (d , (tt , refl))
... | u , v = (inj₂ u) , cong (act a) v
proj₁ (PK-T-μ-rev A E X) .(err e) (err e , tt , refl) = (inj₂ tt) , refl
proj₂ (PK-T-μ-rev A E X) (ret x) tt = ((ret (ret x)) , (tt , refl)) , refl
proj₂ (PK-T-μ-rev A E X) (act a t) (inj₁ tt) = (ret (act a t) , tt , refl) , refl
proj₂ (PK-T-μ-rev A E X) (act a t) (inj₂ y) with proj₂ (PK-T-μ-rev A E X) t y
... | (d , tt , refl) , v = (act a d , tt , refl) , cong (act a) v
proj₂ (PK-T-μ-rev A E X) (err e) (inj₁ tt) = (ret (err e) , (tt , refl)) , refl
proj₂ (PK-T-μ-rev A E X) (err e) (inj₂ tt) = ((err e) , (tt , refl)) , refl





-- Extra structure: The comomonad

PK-T-ηε : (A E X : Set) → PK-≡ (PK-∘ (PK-T-η A E X) (PK-T-ε A E X)) (PK-Id X)
PK-T-ηε A E X = (λ x i → tt , refl) , (λ x i → (tt , tt) , refl)


PK-T-ηδ : (A E X : Set) → PK-≡ (PK-∘ (PK-T-η A E X) (PK-T-δ A E X))
                               (PK-∘ (PK-T-η A E X) (PK-T-η A E (Trace A E X)))
PK-T-ηδ A E X = (λ x i → (tt , tt) , refl) , (λ x i → (tt , tt) , refl)


PK-T-με : (A E X : Set) → PK-≡ (PK-∘ (PK-T-μ A E X) (PK-T-ε A E X))
                               (PK-∘ (PK-T-ε A E (Trace A E X)) (PK-T-ε A E X))
proj₁ (PK-T-με A E X) (ret t) (tt , i) = (tt , i) , refl
proj₂ (PK-T-με A E X) (ret t) (tt , i) = (tt , i) , refl


PK-T-δμ : (A E X : Set) → PK-≡ (PK-∘ (PK-T-δ A E X) (PK-T-μ A E X)) (PK-Id (Trace A E X))

proj₁ (PK-T-δμ A E X) (ret x) i = tt , refl
proj₁ (PK-T-δμ A E X) (act a t) (inj₁ tt , tt) = tt , refl
proj₁ (PK-T-δμ A E X) (act a t) (inj₂ i , tt)
  with proj₁ (PK-T-δμ A E X) t (i , tt)
... | tt , eq = tt , cong (act a) eq
proj₁ (PK-T-δμ A E X) (err e) (inj₁ tt , tt) = tt , refl
proj₁ (PK-T-δμ A E X) (err e) (inj₂ tt , tt) = tt , refl

proj₂ (PK-T-δμ A E X) (ret x) i = (tt , tt) , refl
proj₂ (PK-T-δμ A E X) (act a t) i = ((inj₁ tt) , tt) , refl
proj₂ (PK-T-δμ A E X) (err e) tt = ((inj₁ tt) , tt) , refl




PK-T-χ : (A E X : Set) → PK-Hom (Trace A E (Trace A E X)) (Trace A E (Trace A E X))
PK-T-χ A E X = PK-∘ (PK-T-μ A E X) (PK-T-δ A E X)


-- PK-T-><> : (A E X : Set) → PK-≡ (PK-∘ (PK-T A E (PK-T-δ A E X))
--   (PK-∘ (PK-T-χ A E (Trace A E X)) (PK-T A E (PK-T-μ A E X))))
--   (PK-T-χ A E X)

-- proj₁ (PK-T-><> A E X) (ret (ret x)) (tt , (tt , tt) , tt) = (tt , tt) , refl
-- proj₁ (PK-T-><> A E X) (ret (act a t)) (inj₁ tt , (tt , tt) , tt) = (tt , (inj₁ tt)) , refl
-- proj₁ (PK-T-><> A E X) (ret (act a t)) (inj₂ i , (tt , inj₁ tt) , p) = (tt , (inj₁ tt)) ,
--   cong ret (cong (act a) (proj₂ (proj₁ (PK-T-δμ A E X) t (i , tt))))
-- proj₁ (PK-T-><> A E X) (ret (act a t)) (inj₂ i , (tt , inj₂ j) , p)
--   with proj₁ (PK-T-><> A E X) (ret t) (i , (tt , j) , p)
-- ... | (tt , u) , w = (tt , (inj₂ u)) , (cong (act a) w)
-- proj₁ (PK-T-><> A E X) (ret (err e)) (inj₁ tt , (tt , tt) , tt) = (tt , (inj₁ tt)) , refl
-- proj₁ (PK-T-><> A E X) (ret (err e)) (inj₂ tt , (tt , inj₁ tt) , tt) =
--   (tt , (inj₁ tt)) , refl
-- proj₁ (PK-T-><> A E X) (ret (err e)) (inj₂ tt , (tt , inj₂ tt) , tt) =
--   (tt , (inj₂ tt)) , refl
-- proj₁ (PK-T-><> A E X) (act a d) (i , (tt , inj₁ tt) , tt) = (tt , (inj₁ tt)) ,
--   (cong ret (cong (act a) {!PK-T-μ-as!}))
-- proj₁ (PK-T-><> A E X) (act a d) (i , (tt , inj₂ j) , p) = {!!}
-- proj₁ (PK-T-><> A E X) (err e) (i , (j , l) , p) = {!!}

-- proj₂ (PK-T-><> A E X) d i = {!!}




-- Capturing trees
-- For each operation and continuation pair, an action
-- For each operation, an error (signifying potentially not receiving a response)

Sig-Act : Sig → Set
Sig-Act (S , ar) = Σ S λ σ → ar σ

Trace-F : Sig → Set → Set
Trace-F S X = Trace (Sig-Act S) (proj₁ S) X

Free-Trace : (S : Sig) → (X : Set) → PK-Hom (Free S X) (Trace-F S X)
Free-Trace (S , ar) X (leaf x) = PK-Id _ (ret x)
proj₁ (Free-Trace (S , ar) X (node σ ts)) =
  (Σ (ar σ) λ i → proj₁ (Free-Trace (S , ar) X (ts i))) ⊎ ⊤
proj₂ (Free-Trace (S , ar) X (node σ ts)) (inj₁ (i , c)) =
  act (σ , i) (proj₂ (Free-Trace (S , ar) X (ts i)) c)
proj₂ (Free-Trace (S , ar) X (node σ ts)) (inj₂ tt) = err σ


Free-Trace-nat< : (S : Sig) → {X Y : Set} → (f : PK-Hom X Y)
  → Pow-< (PK-∘ (PK-F S f) (Free-Trace S Y))
          (PK-∘ (Free-Trace S X) (PK-T _ _ f))
Free-Trace-nat< (S , ar) f (leaf x) (p , i) = (tt , p) , refl
Free-Trace-nat< (S , ar) f (node σ ts) (p , inj₁ (i , c))
  with Free-Trace-nat< (S , ar) f (ts i) (p i , c)
... | (u , v) , eq = ((inj₁ (i , u)) , v) , (cong (act (σ , i)) eq)
Free-Trace-nat< (S , ar) f (node σ ts) (p , inj₂ tt) = ((inj₂ tt) , tt) , refl




-- Intermission: Decidability and replacement
decid : (X : Set) → Set
decid X = (x y : X) → (x ≡ y) ⊎ ((x ≡ y) → ⊥)

repla : {X : Set} → {Y : X → Set} → decid X → ((x : X) → Y x) → (x : X) → (Y x)
  → ((x : X) → Y x)
repla D f x y x' with D x x'
... | inj₁ refl = y
... | inj₂ p = f x'

repla-invar : {X Y : Set} → (D D' : decid X) → (f : X → Y) → (x : X) → (y : Y) → (x' : X)
  → repla D f x y x' ≡ repla D' f x y x'
repla-invar D D' f x y x' with D x x' | D' x x'
... | inj₁ refl | inj₁ refl = refl
... | inj₁ refl | inj₂ b = ⊥-elim (b refl)
... | inj₂ a | inj₁ refl = ⊥-elim (a refl)
... | inj₂ a | inj₂ b = refl


repla-ref : {X Y : Set} → (D : decid X) → (f : X → Y) → (x : X) → (y : Y)
  → repla D f x y x ≡ y
repla-ref D f x y with D x x
... | inj₁ refl = refl
... | inj₂ a = ⊥-elim (a refl)


Sig-decid : Sig → Set
Sig-decid (S , ar) = (σ : S) → decid (ar σ)


Free-Trace-T-nat>-help' : (S : Sig) → {X Y : Set} → (Sd : Sig-decid S)
  → (f : PK-Hom X Y) → (f-tot : PK-Total f)
  → (σ : proj₁ S) → (ts : proj₂ S σ → Free S X)
  → (i : proj₂ S σ) → (u : Pos S X (λ x → proj₁ (f x)) (ts i))
  → (proj₁ (Free-Trace S Y (proj₂ (Free-P S (ts i) f) u)))
  → (proj₁ (Free-Trace S Y (proj₂ (Free-P S (ts i) f)
        (repla (Sd σ) (λ l → Pos-In S X (λ x → proj₁ (f x)) (ts l) f-tot) i u i))))
Free-Trace-T-nat>-help' S Sd f f-tot σ ts i u v with Sd σ i i
... | inj₁ refl = v
... | inj₂ y = ⊥-elim (y refl)


-- Totality necessary to find position in case of nullary operation
Free-Trace-T-nat> : (S : Sig) → {X Y : Set} → (Sig-decid S)
  → (f : PK-Hom X Y) → (PK-Total f)
  → Pow-< (PK-∘ (Free-Trace S X) (PK-T _ _ f))
          (PK-∘ (PK-F S f) (Free-Trace S Y))
Free-Trace-T-nat> S Sd f f-tot (leaf x) (tt , j) = (j , tt) , refl
proj₁ (Free-Trace-T-nat> S Sd f f-tot (node σ ts) (inj₁ (i , c) , j))
  with Free-Trace-T-nat> S Sd f f-tot (ts i) (c , j)
... | (u , v) , eq =
  (repla (Sd σ) (λ l → Pos-In S _ (λ x → proj₁ (f x)) (ts l) f-tot) i u  ,
  inj₁ (i , Free-Trace-T-nat>-help' S Sd f f-tot σ ts i u v))
proj₂ (Free-Trace-T-nat> S Sd f f-tot (node σ ts) (inj₁ (i , c) , j)) with Sd σ i i
... | inj₁ refl = cong (act (σ , i)) (proj₂ (Free-Trace-T-nat> S Sd f f-tot (ts i) (c , j)))
... | inj₂ y = ⊥-elim (y refl)
Free-Trace-T-nat> S Sd f f-tot (node σ ts) (inj₂ tt , tt) =
  ((λ i → Pos-In S _ (λ x → proj₁ (f x)) (ts i) f-tot) , (inj₂ tt)) , refl
          
Free-Trace-T-nat : (S : Sig) → {X Y : Set} → (Sig-decid S)
  → (f : PK-Hom X Y) → (PK-Total f)
  → PK-≡ (PK-∘ (PK-F S f) (Free-Trace S Y))
         (PK-∘ (Free-Trace S X) (PK-T _ _ f))
Free-Trace-T-nat S Sd f f-tot = Free-Trace-nat< S f , Free-Trace-T-nat> S Sd f f-tot




Free-Trace-η : (S : Sig) → (X : Set) → PK-≡ (PK-∘ (PK-F-η S X) (Free-Trace S X))
                                            (PK-T-η _ _ X)
proj₁ (Free-Trace-η S X) x (tt , tt) = tt , refl
proj₂ (Free-Trace-η S X) x tt = (tt , tt) , refl

Free-Trace-μ : (S : Sig) → (X : Set) → PK-≡ (PK-∘ (PK-F-μ S X) (Free-Trace S X))
  (PK-∘ (Free-Trace S (Free S X)) (PK-∘ (PK-T _ _ (Free-Trace S X)) (PK-T-μ _ _ X)))
proj₁ (Free-Trace-μ S X) (leaf t) (tt , i) = (tt , (i , tt)) , refl
proj₁ (Free-Trace-μ S X) (node σ ts) (tt , inj₁ (i , p))
  with proj₁ (Free-Trace-μ S X) (ts i) (tt , p)
... | (u , v , tt) , eq = ((inj₁ (i , u)) , (v , tt)) , (cong (act (σ , i)) eq)
proj₁ (Free-Trace-μ S X) (node σ ts) (tt , inj₂ tt) = ((inj₂ tt) , (tt , tt)) , refl
proj₂ (Free-Trace-μ S X) (leaf d) (tt , i , tt) = (tt , i) , refl
proj₂ (Free-Trace-μ S X) (node σ ts) (inj₁ (i , p) , j , tt)
  with proj₂ (Free-Trace-μ S X) (ts i) (p , (j , tt))
... | (tt , u) , eq = (tt , (inj₁ (i , u))) , (cong (act (σ , i)) eq)
proj₂ (Free-Trace-μ S X) (node σ ts) (inj₂ tt , tt , tt) = (tt , (inj₂ tt)) , refl


-- Maybe
Maybe : Set → Set
Maybe X = X ⊎ ⊤

PK-M : {X Y : Set} → (PK-Hom X Y) → (PK-Hom (Maybe X) (Maybe Y))
PK-M f (inj₁ x) = (proj₁ (f x)) , (λ i → inj₁ (proj₂ (f x) i))
PK-M f (inj₂ y) = ⊤ , (λ x → inj₂ tt)


PK-M-η : (X : Set) → PK-Hom X (Maybe X)
PK-M-η X = PK-Fun inj₁

PK-M-μ : (X : Set) → PK-Hom (Maybe (Maybe X)) (Maybe X)
PK-M-μ X (inj₁ x) = PK-Id _ x
PK-M-μ X (inj₂ y) = PK-Id _ (inj₂ tt)


-- Error
Error : Set → Set → Set
Error E X = X ⊎ E

PK-E : (E : Set) → {X Y : Set} → (PK-Hom X Y) → (PK-Hom (Error E X) (Error E Y))
PK-E E f (inj₁ x) = (proj₁ (f x)) , (λ i → inj₁ (proj₂ (f x) i))
PK-E E f (inj₂ e) = ⊤ , (λ x → inj₂ e)



PK-T-in : {A E X Y : Set} → (f : PK-Hom X Y) → (PK-Total f) → (t : Trace A E X)
  → proj₁ (PK-T A E f t)
PK-T-in f f-tot (ret x) = f-tot x
PK-T-in f f-tot (act x t) = PK-T-in f f-tot t
PK-T-in f f-tot (err x) = tt





-- -- Partial Runners
-- T-Runner : (A E S : Set) → Set₁
-- T-Runner A E S = (A → PK-Hom S (Maybe S))

-- T-Runner-Total : {A E S : Set} → T-Runner A E S → Set
-- T-Runner-Total {A} θ = (a : A) → PK-Total (θ a)

-- T-Runner-map : {A E : Set} → (S : Set) → (θ : T-Runner A E S)
--   → (X : Set) → (s : S) → PK-Hom (Trace A E X) (Maybe (S × X))
-- T-Runner-map S θ X s (ret x) = PK-Id _ (inj₁ (s , x))
-- T-Runner-map S θ X s (act a t) = Pow-κ _ _
--   (λ {(inj₁ z) → T-Runner-map S θ X z t ; (inj₂ tt) → PK-Id _ (inj₂ tt)}) (θ a s)
-- T-Runner-map S θ X s (err x) = PK-Id _ (inj₂ tt)



-- T-Runner-map-Total : {A E : Set} → (S : Set)
--   → (θ : T-Runner A E S) → (T-Runner-Total {A} {E} {S} θ)
--   → (X : Set) → (s : S) → PK-Total (T-Runner-map {A} {E} S θ X s)
-- T-Runner-map-Total S θ θ-tot X s (ret x) = tt
-- proj₁ (T-Runner-map-Total S θ θ-tot X s (act x t)) = θ-tot x s
-- proj₂ (T-Runner-map-Total S θ θ-tot X s (act x t)) with (proj₂ (θ x s) (θ-tot x s))
-- ... | inj₁ a = T-Runner-map-Total S θ θ-tot X a t
-- ... | inj₂ b = tt
-- T-Runner-map-Total S θ θ-tot X s (err x) = tt


-- T-Runner-map-nat< : {A E : Set} → (S : Set) → (θ : T-Runner A E S)
--   → {X Y : Set} → (f : PK-Hom X Y) → (s : S)
--   → Pow-< (PK-∘ (PK-T A E f) (T-Runner-map S θ Y s))
--           (PK-∘ (T-Runner-map S θ X s) (PK-M (PK-Id S ⊗ f)))
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
--   → {X Y : Set} → (f : PK-Hom X Y) → (PK-Total f) → (s : S)
--   → Pow-< (PK-∘ (T-Runner-map S θ X s) (PK-M (PK-Id S ⊗ f)))
--           (PK-∘ (PK-T A E f) (T-Runner-map S θ Y s))
          
-- T-Runner-map-T-nat> S θ f f-tot s (ret x) (tt , tt , j) = (j , tt) , refl
-- proj₁ (proj₁ (T-Runner-map-T-nat> S θ f f-tot s (act x t) ((i , j) , k)))
--   with proj₂ (θ x s) i
-- ... | inj₁ a = proj₁ (proj₁ (T-Runner-map-T-nat> S θ f f-tot a t (j , k)))
-- ... | inj₂ b = PK-T-in f f-tot t
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
--   → {X Y : Set} → (f : PK-Hom X Y) → (PK-Total f) → (s : S)
--   → PK-≡ (PK-∘ (PK-T A E f) (T-Runner-map S θ Y s))
--          (PK-∘ (T-Runner-map S θ X s) (PK-M (PK-Id S ⊗ f)))
-- T-Runner-map-T-nat S θ f f-tot s = T-Runner-map-nat< S θ f s ,
--                                    T-Runner-map-T-nat> S θ f f-tot s


-- T-Runner-map-η : {A E : Set} → (S : Set) → (θ : T-Runner A E S)
--   → (X : Set) → (s : S)
--   → PK-≡ (PK-∘ (PK-T-η A E X) (T-Runner-map S θ X s))
--          (PK-∘ (PK-Fun (λ x → (s , x))) (PK-M-η (S × X)))
-- proj₁ (T-Runner-map-η S θ X s) x i = (tt , tt) , refl
-- proj₂ (T-Runner-map-η S θ X s) x i = (tt , tt) , refl




-- T-Runner-map-μ : {A E : Set} → (S : Set) → (θ : T-Runner A E S)
--   → (X : Set) → (s : S)
--   → PK-≡ (PK-∘ (PK-T-μ A E X) (T-Runner-map S θ X s))
--          (PK-∘ (T-Runner-map S θ (Trace A E X) s)
--                (PK-∘ (PK-M (cur (T-Runner-map S θ X))) (PK-M-μ (S × X))))

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


-- -- PK-T-ε : (A E : Set) → (X : Set) → PK-Hom (Trace A E X) X
-- -- PK-T-ε A E X (ret x) = PK-Id X x
-- -- PK-T-ε A E X (act x t) = ⊥ , (λ ())

-- -- PK-T-η<>ε : (A E X : Set) → PK-≡ (PK-T-ε A E X) (PK-rev (PK-T-η A E X))
-- -- proj₁ (PK-T-η<>ε A E X) (ret x) tt = (x , (tt , refl)) , refl
-- -- proj₂ (PK-T-η<>ε A E X) (ret x) (.x , tt , refl) = tt , refl


-- -- PK-T-δ : (A E : Set) → (X : Set) → PK-Hom (Trace A E X) (Trace A E (Trace A E X))
-- -- PK-T-δ A E X (ret x) = PK-Id (Trace A E (Trace A E X)) (ret (ret x))
-- -- PK-T-δ A E X (act a t) = join (PK-Id (Trace A E (Trace A E X)) (ret (act a t)))
-- --                             (Pow-act a (Trace A E X) (PK-T-δ A E X t))


-- -- PK-T-μ<>δ : (A E X : Set) → PK-≡ (PK-T-δ A E X) (PK-rev (PK-T-μ A E X))
-- -- proj₁ (PK-T-μ<>δ A E X) (ret x) tt = (ret (ret x) , tt , refl) , refl
-- -- proj₁ (PK-T-μ<>δ A E X) (act a t) (inj₁ i) = ((ret (act a t)) , (tt , refl)) , refl
-- -- proj₁ (PK-T-μ<>δ A E X) (act a t) (inj₂ i) with (proj₁ (PK-T-μ<>δ A E X) t i)
-- -- ... | (d , p , v) , eq = (act a d , (p , cong (act a) v)) , cong (act a) eq
-- -- proj₂ (PK-T-μ<>δ A E X) (ret x) (ret .(ret x) , tt , refl) = tt , refl
-- -- proj₂ (PK-T-μ<>δ A E X) (act a t) (ret .(act a t) , tt , refl) = (inj₁ tt) , refl
-- -- proj₂ (PK-T-μ<>δ A E X) (act a .(proj₂ (PK-T-μ A E X d) i)) (act .a d , i , refl)
-- --   with proj₂ (PK-T-μ<>δ A E X) (proj₂ (PK-T-μ A E X d) i) (d , i , refl)
-- -- ... | j , eq = (inj₂ j) , (cong (act a) eq)
