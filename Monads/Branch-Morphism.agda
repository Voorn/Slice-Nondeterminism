module Monads.Branch-Morphism where

open import Data.Unit
open import Data.Empty
open import Data.Sum renaming (map to map⊎)
open import Data.Nat hiding (_⊔_)
open import Data.Product renaming (map to map×)
open import Relation.Binary.PropositionalEquality hiding ([_])


open import Slice.Base

open import Slice-Functions.Base
open import Slice-Functions.Subcategories
open import Slice-Functions.Monoidal

open import Monads.Free-Monad
open import Monads.Trace



-- Capturing trees
-- For each operation and continuation pair, an action
-- For each operation, an error (signifying potentially not receiving a response)

Sig-Act : Sig → Set
Sig-Act (S , ar) = Σ S λ σ → ar σ

Trace-F : Sig → Set → Set
Trace-F S X = Trace (Sig-Act S) (proj₁ S) X

Free-Trace : (S : Sig) → (X : Set) → SF (Free S X) (Trace-F S X)
Free-Trace (S , ar) X (leaf x) = SF-id _ (ret x)
proj₁ (Free-Trace (S , ar) X (node σ ts)) =
  (Σ (ar σ) λ i → proj₁ (Free-Trace (S , ar) X (ts i))) ⊎ ⊤
proj₂ (Free-Trace (S , ar) X (node σ ts)) (inj₁ (i , c)) =
  act (σ , i) (proj₂ (Free-Trace (S , ar) X (ts i)) c)
proj₂ (Free-Trace (S , ar) X (node σ ts)) (inj₂ tt) = err σ


Free-Trace-nat< : (S : Sig) → {X Y : Set} → (f : SF X Y)
  → SF≤ (SF-∘ (SF-F S f) (Free-Trace S Y))
          (SF-∘ (Free-Trace S X) (SF-T _ _ f))
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
  → (f : SF X Y) → (f-tot : SF-Total f)
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
  → (f : SF X Y) → (SF-Total f)
  → SF≤ (SF-∘ (Free-Trace S X) (SF-T _ _ f))
          (SF-∘ (SF-F S f) (Free-Trace S Y))
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
  → (f : SF X Y) → (SF-Total f)
  → SF≡ (SF-∘ (SF-F S f) (Free-Trace S Y))
         (SF-∘ (Free-Trace S X) (SF-T _ _ f))
Free-Trace-T-nat S Sd f f-tot = Free-Trace-nat< S f , Free-Trace-T-nat> S Sd f f-tot




Free-Trace-η : (S : Sig) → (X : Set) → SF≡ (SF-∘ (SF-F-η S X) (Free-Trace S X))
                                            (SF-T-η _ _ X)
proj₁ (Free-Trace-η S X) x (tt , tt) = tt , refl
proj₂ (Free-Trace-η S X) x tt = (tt , tt) , refl

Free-Trace-μ : (S : Sig) → (X : Set) → SF≡ (SF-∘ (SF-F-μ S X) (Free-Trace S X))
  (SF-∘ (Free-Trace S (Free S X)) (SF-∘ (SF-T _ _ (Free-Trace S X)) (SF-T-μ _ _ X)))
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


