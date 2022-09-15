module Slice.Lattice where

open import Data.Unit
open import Data.Empty
open import Data.Sum renaming (map to map⊎)
open import Data.Nat hiding (_⊔_)
open import Data.Product renaming (map to map×)
open import Relation.Binary.PropositionalEquality hiding ([_])

open import Slice.Base


-- Structure of powerdomain
SL-⊤ : (X : Set) → SL X
SL-⊤ X = X , (λ x → x)

SL-⊤-top : {X : Set} → (U : SL X) → SL→ X U (SL-⊤ X)
SL-⊤-top (I , f) i = (f i) , refl


SL-⊥ : (X : Set) → SL X
SL-⊥ X = ⊥ , (λ {()})

SL-⊥-bot : {X : Set} → (U : SL X) → SL→ X (SL-⊥ X) U
SL-⊥-bot (I , f) ()


join : {X : Set} → SL X → SL X → SL X
join (I , l) (J , r) = (I ⊎ J) , (λ { (inj₁ i) → l i ; (inj₂ j) → r j})

join-< : {X : Set} → {a b c d : SL X}
  → SL→ X a b → SL→ X c d → SL→ X (join a c) (join b d)
join-< a<b c<d (inj₁ i) = (inj₁ (proj₁ (a<b i))) , (proj₂ (a<b i))
join-< a<b c<d (inj₂ j) = (inj₂ (proj₁ (c<d j))) , (proj₂ (c<d j))

join-idem : {X : Set} → (a : SL X) → SL-sim X (join a a) a 
proj₁ (join-idem a) (inj₁ i) = i , refl
proj₁ (join-idem a) (inj₂ i) = i , refl
proj₂ (join-idem a) i = (inj₁ i) , refl

join-symm : {X : Set} → (f g : SL X) → SL-sim X (join f g) (join g f)
proj₁ (join-symm f g) (inj₁ i) = (inj₂ i) , refl
proj₁ (join-symm f g) (inj₂ j) = inj₁ j , refl
proj₂ (join-symm f g) (inj₁ i) = (inj₂ i) , refl
proj₂ (join-symm f g) (inj₂ j) = inj₁ j , refl

join-asso : {X : Set} → (a b c : SL X) → SL-sim X (join (join a b) c) (join a (join b c))
proj₁ (join-asso a b c) (inj₁ (inj₁ i)) = (inj₁ i) , refl
proj₁ (join-asso a b c) (inj₁ (inj₂ j)) = (inj₂ (inj₁ j)) , refl
proj₁ (join-asso a b c) (inj₂ k) = (inj₂ (inj₂ k)) , refl
proj₂ (join-asso a b c) (inj₁ i) = (inj₁ (inj₁ i)) , refl
proj₂ (join-asso a b c) (inj₂ (inj₁ j)) = inj₁ (inj₂ j) , refl
proj₂ (join-asso a b c) (inj₂ (inj₂ k)) = inj₂ k , refl

meet : {X : Set} → SL X → SL X → SL X
meet (I , l) (J , r) = Σ (I × J) (λ {(i , j) → l i ≡ r j}) ,
  λ {((i , j) , eq) → l i} 

meet-< : {X : Set} → {a b c d : SL X}
  → SL→ X a b → SL→ X c d → SL→ X (meet a c) (meet b d)
meet-< a<b c<d ((i , j) , eq) = (((proj₁ (a<b i)) , (proj₁ (c<d j))) ,
  (trans (sym (proj₂ (a<b i))) (trans eq (proj₂ (c<d j))))) ,
  (proj₂ (a<b i))

meet-idem : {X : Set} → (a : SL X) → SL-sim X (meet a a) a
proj₁ (meet-idem a) ((i , j) , eq) = i , refl
proj₂ (meet-idem a) i = ((i , i) , refl) , refl

meet-symm : {X : Set} → (a b : SL X) → SL-sim X (meet a b) (meet b a)
proj₁ (meet-symm a b) ((i , j) , eq) = ((j , i) , (sym eq)) , eq
proj₂ (meet-symm a b) ((i , j) , eq) = ((j , i) , (sym eq)) , eq

meet-asso : {X : Set} → (a b c : SL X) → SL-sim X (meet (meet a b) c) (meet a (meet b c)) 
proj₁ (meet-asso a b c) ((((i , j) , eq) , k) , eq') =
  ((i , (j , k) , trans (sym eq) eq') , eq) , refl
proj₂ (meet-asso a b c) ((i , (j , k) , eq) , eq') =
  ((((i , j) , eq') , k) , (trans eq' eq)) , refl

