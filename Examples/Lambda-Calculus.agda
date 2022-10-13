module Examples.Lambda-Calculus where

open import Data.Unit
open import Data.Empty
open import Data.Sum renaming (map to map⊎)
open import Data.Nat hiding (_⊔_)
open import Data.Product renaming (map to map×)
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Data.Bool

open import Slice.Base
open import Slice.Lattice
open import Slice-Functions.Base
open import Examples.Iterative

data Tm : Set where
  var : ℕ → Tm
  app : Tm → Tm → Tm
  lam : Tm → Tm

ℕ-max : ℕ → ℕ → ℕ
ℕ-max zero m = m
ℕ-max (suc n) zero = suc n
ℕ-max (suc n) (suc m) = suc (ℕ-max n m)

ℕ-pred : ℕ → ℕ
ℕ-pred zero = zero
ℕ-pred (suc n) = n

cont : Tm → ℕ
cont (var x) = suc x
cont (app t t₁) = ℕ-max (cont t) (cont t₁)
cont (lam t) = ℕ-pred (cont t)

closed : Tm → Set
closed t with cont t
... | zero = ⊤
... | suc k = ⊥

data ℕ-< : ℕ → ℕ → Set where
  zero-< : {n : ℕ} → ℕ-< zero (suc n)
  suc-< : {n m : ℕ} → ℕ-< n m  → ℕ-< (suc n) (suc m)

ℕ-comp : (n m : ℕ) → (ℕ-< n m) ⊎ (n ≡ m) ⊎ (ℕ-< m n)
ℕ-comp zero zero = inj₂ (inj₁ refl)
ℕ-comp zero (suc m) = inj₁ zero-<
ℕ-comp (suc n) zero = inj₂ (inj₂ zero-<)
ℕ-comp (suc n) (suc m) with ℕ-comp n m
... | inj₁ hyp = inj₁ (suc-< hyp)
... | inj₂ (inj₁ hyp) = inj₂ (inj₁ (cong suc hyp))
... | inj₂ (inj₂ hyp) = inj₂ (inj₂ (suc-< hyp))

lam-up : Tm → ℕ → Tm
lam-up (var x) n with ℕ-comp x n
... | inj₁ _ = var x
... | inj₂ _ = var (suc x)
lam-up (app t t₁) n = app (lam-up t n) (lam-up t₁ n)
lam-up (lam t) n = lam (lam-up t (suc n))

not-lambda : Tm → Set
not-lambda (var x) = ⊤
not-lambda (app t t₁) = ⊤
not-lambda (lam t) = ⊥


subs : Tm → Tm → ℕ → Tm
subs (var x) r n with ℕ-comp x n
... | inj₁ p = var x
... | inj₂ (inj₁ p) = r
... | inj₂ (inj₂ p) = var (ℕ-pred x)
subs (app t t₁) r n = app (subs t r n) (subs t₁ r n)
subs (lam t) r n = lam (subs t (lam-up r zero) (suc n))



reduc : SF Tm Tm
app-reduc : SF (Tm × Tm) Tm
reduc (var x) = SL-⊥ Tm
reduc (app t t₁) = join (app-reduc (t , t₁))
                  (join (SL-fun (λ z → app z t₁) (reduc t))
                        (SL-fun (app t) (reduc t₁)))
reduc (lam t) = SL-fun lam (reduc t)
app-reduc (var x , t₁) = SL-⊥ Tm
app-reduc (app t t₂ , t₁) = SL-⊥ Tm
app-reduc (lam t , t₁) = SL-η Tm (subs t t₁ zero)


reduc-∈ : Tm → Tm → Set
reduc-∈ t r = SL-∈ Tm t (reduc r)


normal-ext : Tm → Set
normal-ext t with reduc t
... | (I , f) = I → ⊥

data normal-int : Tm → Set where
  var-norm : {x : ℕ} → normal-int (var x)
  app-norm : {t t₁ : Tm}
    → not-lambda t → normal-int t → normal-int t₁ → normal-int (app t t₁)
  lam-norm : {t : Tm} → normal-int t → normal-int (lam t)

normal-sound1 : (t : Tm) → normal-int t → normal-ext t
normal-sound1 (var x) var-norm i = i
normal-sound1 (app (var x) t₁) (app-norm x₁ var-norm t-ni) (inj₂ (inj₂ i)) =
  normal-sound1 t₁ t-ni i
normal-sound1 (app (app t t₂) t₁) (app-norm tt t-ni t-ni₁) (inj₂ (inj₁ i)) =
  normal-sound1 (app t t₂) t-ni i
normal-sound1 (app (app t t₂) t₁) (app-norm tt t-ni t-ni₁) (inj₂ (inj₂ i)) =
  normal-sound1 t₁ t-ni₁ i
normal-sound1 (app (lam t) t₁) (app-norm () t-ni t-ni₁) i
normal-sound1 (lam t) (lam-norm t-ni) i = normal-sound1 t t-ni i

normal-sound2 : (t : Tm) → normal-ext t → normal-int t
normal-sound2 (var x) f = var-norm
normal-sound2 (app (var x) t₁) f =
  app-norm tt var-norm (normal-sound2 t₁ (λ i → f (inj₂ (inj₂ i))))
normal-sound2 (app (app t t₂) t₁) f = app-norm tt
  (normal-sound2 (app t t₂) (λ i → f (inj₂ (inj₁ i))))
  (normal-sound2 t₁ (λ i → f (inj₂ (inj₂ i))))
normal-sound2 (app (lam t) t₁) f with f (inj₁ tt)
... | ()
normal-sound2 (lam t) f = lam-norm (normal-sound2 t f)


ℕ-step : Tm → ℕ → SL Tm
ℕ-step t zero = SL-η Tm t
ℕ-step t (suc n) = SL-* (λ t' → ℕ-step t' n) (reduc t)

ω-step : Tm → SL Tm
ω-step t = SL-Stream (ℕ-step t)

reduc-∈-ω : Tm → Tm → Set
reduc-∈-ω t r = SL-∈ Tm t (ω-step r)

reduc-∈-ω-tran : {a b c : Tm} → reduc-∈-ω b a → reduc-∈-ω c b → reduc-∈-ω c a
reduc-∈-ω-tran ((zero , u) , refl) v = v
reduc-∈-ω-tran ((suc n , i , u) , eq) v with reduc-∈-ω-tran ((n , u) , eq) v
... | (k , w) , eq' = ((suc k) , (i , w)) , eq'

lam-ext : {t r : Tm} → (lam t ≡ lam r) → (t ≡ r)
lam-ext {t} {.t} refl = refl

lam-push : {a b : Tm} → reduc-∈-ω b (lam a) → Σ Tm λ c → (b ≡ lam c) × reduc-∈-ω c a
lam-push {a} {b} ((zero , k) , refl) = a , refl , (zero , tt) , refl
lam-push {a} {b} ((suc n , i , k) , eq) with lam-push {proj₂ (reduc a) i} {b} ((n , k) , eq)
... | u , (eq' , ((m , v) , w)) = u , (eq' , (((suc m) , (i , v)) , w))

lam-lift : {a b : Tm} → reduc-∈-ω a b → reduc-∈-ω (lam a) (lam b)
lam-lift ((zero , tt) , eq) = (zero , tt) , (cong lam eq)
lam-lift {a} {b} ((suc n , i , u) , eq)
  with lam-lift {a} {proj₂ (reduc b) i} ((n , u) , eq)
... | (m , v) , eq' = ((suc m) , (i , v)) , eq'



app-lift-right : (a : Tm) → {b b' : Tm} → reduc-∈-ω b' b
  → reduc-∈-ω (app a b') (app a b)
app-lift-right a ((zero , tt) , refl) = (zero , tt) , refl
app-lift-right a ((suc n , i , u) , eq)
  with app-lift-right a ((n , u) , eq)
... | (k , v) , eq' = ((suc k) , ((inj₂ (inj₂ i)) , v)) , eq'


app-lift : {a b a' b' : Tm} → reduc-∈-ω a' a → reduc-∈-ω b' b
  → reduc-∈-ω (app a' b') (app a b) 
app-lift ((zero , tt) , refl) u = app-lift-right _ u
app-lift {a} {b} {a'} {b'} ((suc n , i , u) , eq) w
  with app-lift {proj₂ (reduc a) i} {b} {a'} {b'} ((n , u) , eq) w
... | ((k , v) , eq') = ((suc k) , ((inj₂ (inj₁ i)) , v)) , eq'


lam-up-eq : (a a₁ : Tm) → (n : ℕ)
  → (subs (lam-up a (suc n)) (lam-up a₁ n) 0) ≡ (lam-up (subs a a₁ 0) n)
lam-up-eq (var x) a₁ n = {!x!}
lam-up-eq (app a a₂) a₁ n = {!!}
lam-up-eq (lam a) a₁ n = {!!}

lam-up-lift : {a b : Tm} → (n : ℕ) → reduc-∈-ω b a → reduc-∈-ω (lam-up b n) (lam-up a n)
lam-up-lift {a} {b} n ((zero , u) , eq) = (zero , tt) , (cong (λ z → lam-up z n) eq)
lam-up-lift {lam a} {b} n ((suc m , p) , eq)
  with lam-push {a} {b} ((suc m , p) , eq)
... | c , refl , w = lam-lift (lam-up-lift {a} {c} (suc n) w)
lam-up-lift {app (lam a) a₁} {b} n ((suc k , inj₁ tt , u) , eq)
  with lam-up-lift {subs a a₁ zero} {b} n ((k , u) , eq)
... | ((m , w) , eq') = ((suc m) , ((inj₁ tt) , {!w!})) , {!!}
lam-up-lift {app a a₁} {b} n ((suc k , inj₂ i , u) , refl) = {!!}





diamond : (a b c : Tm) → reduc-∈ b a → reduc-∈ c a
  → Σ Tm λ d → reduc-∈-ω d b × reduc-∈-ω d c
diamond-subs : (a b c : Tm) → (n : ℕ) → reduc-∈ c b → reduc-∈-ω (subs a c n) (subs a b n)
diamond (app a a₁) b c a→b a→c = {!!}
diamond (lam a) (lam b) (lam c) (i , a→b) (j , a→c)
  with diamond a b c (i , (lam-ext a→b)) (j , lam-ext a→c)
... | d , u , v = (lam d) , (lam-lift u , lam-lift v)
diamond-subs (var x) b .(proj₂ (reduc b) i) n (i , refl) with ℕ-comp x n
... | inj₁ low = (zero , tt) , refl
... | inj₂ (inj₁ refl) = (suc zero , i , tt) , refl
... | inj₂ (inj₂ y) = (zero , tt) , refl
diamond-subs (app a a₁) b .(proj₂ (reduc b) i) n (i , refl) =
  app-lift (diamond-subs a b (proj₂ (reduc b) i) n (i , refl))
           (diamond-subs a₁ b (proj₂ (reduc b) i) n (i , refl))
diamond-subs (lam a) b .(proj₂ (reduc b) i) n (i , refl) = lam-lift (diamond-subs a (lam-up b zero) (lam-up (proj₂ (reduc b) i) zero) (suc n) {!!})


