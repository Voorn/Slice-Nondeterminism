module Small-Slice.LTS where

open import Data.Unit
open import Data.Empty
open import Data.Sum renaming (map to map⊎)
open import Data.Nat hiding (_⊔_)
open import Data.Product renaming (map to map×)
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Data.Bool

open import Small-Slice.Univ
open import Small-Slice.ND-functions
open import Small-Slice.Countable-Join

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
LTS : (A : 𝕌) → Set₁
LTS A = Σ Set λ S → (𝕌Hom (S × (𝕌S A)) S) × (S → Bool)


-- Collecting all accepting lists
LTS-Col : (A : 𝕌) → ((S , t , e) : LTS A) → ℕ → 𝕌Hom S (Lis (𝕌S A))
LTS-Col A (S , t , e) zero s with e s
... | false = 𝕌SL-⊥
... | true = 𝕌SL-η uni
proj₁ (LTS-Col A (S , t , e) (suc n) s) = 𝕌Σ (A ,
  (λ a → 𝕌Σ (proj₁ (t (s , a)) ,
  λ i → proj₁ (LTS-Col A (S , t , e) n (proj₂ (t (s , a) ) i)) )))
proj₂ (LTS-Col A (S , t , e) (suc n) s) (a , (i , j)) =
  act a (proj₂ (LTS-Col A (S , t , e) n (proj₂ (t (s , a) ) i)) j)

LTS-Colω : (A : 𝕌) → ((S , t , e) : LTS A) → 𝕌Hom S (Lis (𝕌S A))
LTS-Colω A (S , t , e) = 𝕌Hom-⋁ (LTS-Col A (S , t , e))


-- Check if list is accepting

LTS-accept : (A : 𝕌) → (l : LTS A) → (s : proj₁ l) → Lis (𝕌S A) → Set
LTS-accept A (S , t , e) s uni with e s
... | false = ⊥
... | true = ⊤
LTS-accept A (S , t , e) s (act a p) = Σ (𝕌S (proj₁ (t (s , a))))
  λ i → LTS-accept A (S , t , e) (proj₂ (t (s , a)) i) p


-- Collected lists are exactly accepting lists
LTS-sound : (A : 𝕌) → ((S , t , e) : LTS A) → (s : S) → (p : Lis (𝕌S A))
  → LTS-accept A (S , t , e) s p → 𝕌SL-∈ p (LTS-Colω A (S , t , e) s)
proj₁ (proj₁ (LTS-sound A (S , t , e) s uni accep)) = 0
proj₂ (proj₁ (LTS-sound A (S , t , e) s uni accep)) with e s
... | true = tt
proj₂ (LTS-sound A (S , t , e) s uni accep) with e s
... | true = refl
LTS-sound A (S , t , e) s (act a p) (i , accep)
  with LTS-sound A (S , t , e) (proj₂ (t (s , a)) i) p accep
... | ((n , v) , eq) = ((suc n) , (a , (i , v))) , (cong (act a) eq)

LTS-adeq : (A : 𝕌) → (l : LTS A) → (s : proj₁ l) → (p : Lis (𝕌S A))
  → 𝕌SL-∈ p (LTS-Colω A l s) → LTS-accept A l s p
LTS-adeq A (S , t , e) s uni ((zero , v) , eq) with e s
... | true = tt
LTS-adeq A (S , t , e) s (act a p) ((zero , v) , eq) with e s
LTS-adeq A (S , t , e) s (act a p) ((zero , ()) , eq) | false
LTS-adeq A (S , t , e) s (act a p) ((zero , tt) , ()) | true
LTS-adeq A (S , t , e) s (act .a .(proj₂ (LTS-Col A (S , t , e) n (proj₂ (t (s , a)) i)) v))
  ((suc n , a , i , v) , refl) = i , (LTS-adeq A (S , t , e) (proj₂ (t (s , a)) i)
  (proj₂ (LTS-Colω A (S , t , e) (proj₂ (t (s , a)) i)) (n , v)) ((n , v) , refl))

