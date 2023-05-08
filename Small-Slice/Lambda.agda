module Small-Slice.Lambda where

-- standard library
open import Data.Unit
open import Data.Empty
open import Data.Sum renaming (map to map⊎)
open import Data.Nat
open import Data.Product
open import Data.Bool

open import Relation.Binary.PropositionalEquality

-- local
open import Small-Slice.Univ
open import Small-Slice.ND-functions
open import Small-Slice.Countable-Join
open import Small-Slice.Semi-Lattice

pattern val = true
pattern cpt = false

Cxt = ℕ

-- membership of a variable in a context
data cvar : Cxt → Set where
  czero : ∀{Γ} → cvar (suc Γ)
  csuc : ∀{Γ} → cvar Γ → cvar (suc Γ)

-- removal of a variable from context
_∖_ : ∀ Γ → cvar Γ → Cxt
(suc Γ) ∖ czero = Γ
(suc Γ) ∖ (csuc m) = suc (Γ ∖ m)

_⊖_ : ∀ Γ → cvar Γ → Cxt
(suc Γ) ⊖ czero = Γ
(suc Γ) ⊖ (csuc m) = (Γ ⊖ m)

-- subset relation between contexts
infix 6 _⊆_
data _⊆_ : Cxt → Cxt → Set where
  ε : zero ⊆ zero
  lift : ∀{Γ Δ} → Γ ⊆ Δ → suc Γ ⊆ suc Δ
  wk : ∀{Γ Δ} → Γ ⊆ Δ → Γ ⊆ suc Δ

id⊆ : ∀ {Γ} → Γ ⊆ Γ
id⊆ {zero} = ε
id⊆ {suc Γ} = lift (id⊆ {Γ})

∈⊆ : ∀{Γ Δ} → cvar Γ → Γ ⊆ Δ → cvar Δ
∈⊆ m (wk s) = csuc (∈⊆ m s)
∈⊆ czero (lift s) = czero
∈⊆ (csuc m) (lift s) = csuc (∈⊆ m s)


data Tm : ℕ → Bool → Set where
  var : ∀{Γ} → cvar Γ → Tm Γ val
  lam : ∀{Γ} → Tm (suc Γ) cpt → Tm Γ val
  return : ∀{Γ} → Tm Γ val → Tm Γ cpt
  app : ∀{Γ} → Tm Γ cpt → Tm Γ cpt → Tm Γ cpt
  or :  ∀{Γ} → Tm Γ cpt → Tm Γ cpt → Tm Γ cpt


-- admissibility of weakening 
weak : ∀{Γ Δ k} → Γ ⊆ Δ → Tm Γ k → Tm Δ k
weak s (var x) = var (∈⊆ x s)
weak s (lam M) = lam (weak (lift s) M)
weak s (return V) = return (weak s V)
weak s (app M N) = app (weak s M) (weak s N)
weak s (or M N) = or (weak s M) (weak s N)

weakLast : ∀{Γ k} → Tm Γ k → Tm (suc Γ) k
weakLast t = weak (wk id⊆) t


-- admissibility of value substitution
sub : ∀{Γ k}
  → Tm Γ k → (m : cvar Γ) → Tm (Γ ⊖ m) val
  → Tm (Γ ∖ m) k
sub (var czero) czero V = V
sub (var (csuc x)) czero V = var x
sub (var czero) (csuc m) V = var czero
sub (var (csuc x)) (csuc m) V = weakLast (sub (var x) m V)
sub (lam M) m V = lam (sub M (csuc m) V)
sub (return W) m V = return (sub W m V)
sub (app M N) m V = app (sub M m V) (sub N m V)
sub (or M N) m V = or (sub M m V) (sub N m V)

subLast : ∀{k Γ} → Tm (suc Γ) k → Tm Γ val → Tm Γ k
subLast t u = sub t czero u


lam-denot : Tm zero val → Tm zero val → Tm zero cpt
lam-denot (lam M) V = subLast M V

-- call by value evaluation
eval-cbv : ℕ → 𝕌Hom (Tm zero cpt) (Tm zero val)
eval-cbv zero t = 𝕌SL-⊥
eval-cbv (suc n) (return V) = 𝕌SL-η V
eval-cbv (suc n) (app M N) = 𝕌SL-κ (λ V → 𝕌SL-κ (λ W → eval-cbv n (lam-denot V W)) (eval-cbv n N)) (eval-cbv n M)
eval-cbv (suc n) (or M N) = 𝕌SL-∨ (eval-cbv n M) (eval-cbv n N)


cpt-denot : 𝕌Hom (Tm zero cpt) (Tm zero val)
cpt-denot = 𝕌Hom-⋁ 𝕌ℕ eval-cbv


eval-chain : 𝕌Hom-chain eval-cbv
eval-chain (suc n) (return V) i = tt , refl
proj₁ (proj₁ (eval-chain (suc n) (app M N) (i , j , k))) = (proj₁ (eval-chain n M i))
proj₁ (proj₂ (proj₁ (eval-chain (suc n) (app M N) (i , j , k)))) = (proj₁ (eval-chain n N j))
proj₂ (proj₂ (proj₁ (eval-chain (suc n) (app M N) (i , j , k))))
  rewrite (proj₂ (eval-chain n M i)) | (proj₂ (eval-chain n N j)) =
  proj₁ (eval-chain n (lam-denot (proj₂ (eval-cbv (suc n) M) (proj₁ (eval-chain n M i)))
       (proj₂ (eval-cbv (suc n) N) (proj₁ (eval-chain n N j)))) k)
proj₂ (eval-chain (suc n) (app M N) (i , j , k))
  rewrite (proj₂ (eval-chain n M i)) | (proj₂ (eval-chain n N j)) |
  proj₂ (eval-chain n (lam-denot (proj₂ (eval-cbv (suc n) M) (proj₁ (eval-chain n M i)))
       (proj₂ (eval-cbv (suc n) N) (proj₁ (eval-chain n N j)))) k) = refl
eval-chain (suc n) (or M N) (inj₁ i) = (inj₁ (proj₁ (eval-chain n M i))) , (proj₂ (eval-chain n M i))
eval-chain (suc n) (or M N) (inj₂ i) = (inj₂ (proj₁ (eval-chain n N i))) , (proj₂ (eval-chain n N i))


elmax = 𝕌Hom-chain-lmax eval-cbv eval-chain
ermax = 𝕌Hom-chain-rmax eval-cbv eval-chain



-- admissability of computation substitution in computations
sub-cpt : ∀{Γ}
  → Tm Γ cpt → (m : cvar Γ) → Tm (Γ ⊖ m) cpt
  → Tm (Γ ∖ m) cpt
sub-cpt (return (var czero)) czero M = M
sub-cpt (return (var (csuc x))) czero M = return (var x)
sub-cpt (return (var czero)) (csuc m) M = return (var czero)
sub-cpt (return (var (csuc x))) (csuc m) M = weakLast (sub-cpt (return (var x)) m M)
sub-cpt (return (lam N)) m M = return (lam (sub-cpt N (csuc m) M))
sub-cpt (app N K) m M = app (sub-cpt N m M) (sub-cpt K m M)
sub-cpt (or N K) m M = or (sub-cpt N m M) (sub-cpt K m M)

subLast-cpt : ∀{Γ} → Tm (suc Γ) cpt → Tm Γ cpt → Tm Γ cpt
subLast-cpt t u = sub-cpt t czero u


-- call-by-name evaluation
eval-cbn : Tm zero cpt → ℕ → 𝕌SL (Tm zero val)
eval-cbn-lam : Tm zero val → Tm zero cpt → ℕ → 𝕌SL (Tm zero val) 
eval-cbn t zero = 𝕌SL-⊥
eval-cbn (return V) (suc n) = 𝕌SL-η V
eval-cbn (app M N) (suc n) = 𝕌SL-κ (λ V → eval-cbn-lam V N n) (eval-cbn M n)
eval-cbn (or M N) (suc n) = 𝕌SL-∨ (eval-cbn M n) (eval-cbn N n)
eval-cbn-lam (lam V) M n = eval-cbn (subLast-cpt V M) n
