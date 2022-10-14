module Examples.Transition where

open import Data.Unit
open import Data.Empty
open import Data.Sum renaming (map to map⊎)
open import Data.Nat hiding (_⊔_)
open import Data.Product renaming (map to map×)
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Data.Bool

open import Slice.Base


-- Lists of labels
data Lis (A : Set) : Set where
  uni : Lis A
  act : A → Lis A → Lis A

append : {A : Set} → Lis A → Lis A → Lis A
append uni l = l
append (act a l) r = act a (append l r)


Lis-luni : {X : Set} → (a : Lis X) → (append uni a ≡ a)
Lis-luni a = refl

Lis-runi : {X : Set} → (a : Lis X) → (append a uni ≡ a)
Lis-runi uni = refl
Lis-runi (act x a) = cong (act x) (Lis-runi a)

Lis-asso : {X : Set} → (a b c : Lis X) → (append (append a b) c ≡ append a (append b c))
Lis-asso uni b c = refl
Lis-asso (act x a) b c = cong (act x) (Lis-asso a b c)



-- Labelled transition system
LTS : (A : Set) → Set₁
LTS A = Σ Set λ S → (S × A → SL S) × (S → Set)


-- Specifying accepting paths through the transition system
LTS-Path : (A : Set) → (l : LTS A) → (proj₁ l) → ℕ → Set
LTS-Path A (S , step , end) s zero = end s
LTS-Path A (S , step , end) s (suc n) = Σ A λ a → Σ (proj₁ (step (s , a)))
  λ i → LTS-Path A (S , step , end) (proj₂ (step (s , a)) i) n


-- Collecting all accepting lists
LTS-Col : (A : Set) → (l : LTS A) → (s : proj₁ l) → SL (Lis A)
proj₁ (LTS-Col A l s) = Σ ℕ λ n → LTS-Path A l s n
proj₂ (LTS-Col A (S , ste , end) s) (zero , p) = uni
proj₂ (LTS-Col A (S , ste , end) s) (suc n , a , (i , p)) =
  act a (proj₂ (LTS-Col A (S , ste , end) (proj₂ (ste (s , a)) i)) (n , p))


-- Check if list is accepting

LTS-accept : (A : Set) → (l : LTS A) → (s : proj₁ l) → Lis A → Set
LTS-accept A (S , ste , end) s uni = end s
LTS-accept A (S , ste , end) s (act a p) = Σ (proj₁ (ste (s , a))) λ z
  → LTS-accept A (S , ste , end) (proj₂ (ste (s , a)) z) p


-- Collected lists are exactly accepting lists
LTS-sound : (A : Set) → (l : LTS A) → (s : proj₁ l) → (p : Lis A)
  → LTS-accept A l s p → SL-∈ (Lis A) p (LTS-Col A l s)
proj₁ (proj₁ (LTS-sound A l s uni accep)) = 0
proj₂ (proj₁ (LTS-sound A (S , ste , end) s uni accep)) with end s
... | i = accep
proj₂ (LTS-sound A (S , ste , end) s uni accep)  with end s
... | i = refl
LTS-sound A (S , ste , end) s (act a p) (i , accep)
  with LTS-sound A (S , ste , end) (proj₂ (ste (s , a)) i) p accep
... | ((n , v) , eq) = ((suc n) , (a , i , v)) , (cong (act a) eq)


LTS-adeq : (A : Set) → (l : LTS A) → (s : proj₁ l) → (p : Lis A)
  → SL-∈ (Lis A) p (LTS-Col A l s) → LTS-accept A l s p
LTS-adeq A (S , ste , end) s uni ((zero , v) , eq) with end s
... | k = v
LTS-adeq A (S , ste , end) s (act a p) ((zero , v) , eq) with end s
LTS-adeq A (S , ste , end) s (act a p) ((zero , v) , ()) | k
LTS-adeq A (S , ste , end) s
  (act a .(proj₂ (LTS-Col A (S , ste , end) (proj₂ (ste (s , a)) i)) (n , v)))
  ((suc n , .a , i , v) , refl) = i ,
  (LTS-adeq A (S , ste , end) (proj₂ (ste (s , a)) i)
  (proj₂ (LTS-Col A (S , ste , end) (proj₂ (ste (s , a)) i)) (n , v))
  ((n , v) , refl))
