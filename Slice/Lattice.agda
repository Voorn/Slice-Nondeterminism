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

-- Absorption laws
SL-lat1 : {X : Set} → (a b : SL X) → SL-sim X (join a (meet a b)) a
proj₁ (SL-lat1 a b) (inj₁ i) = i , refl
proj₁ (SL-lat1 a b) (inj₂ ((i , j) , eq)) = i , refl
proj₂ (SL-lat1 a b) i = (inj₁ i) , refl

SL-lat2 : {X : Set} → (a b : SL X) → SL-sim X (meet a (join a b)) a
proj₁ (SL-lat2 a b) ((i , j) , eq) = i , refl
proj₂ (SL-lat2 a b) i = ((i , (inj₁ i)) , refl) , refl


-- complement (almost)
SL-comp : {X : Set} → SL X → SL X
SL-comp {X} (I , f) = (Σ X λ x → (i : I) → (f i ≡ x) → ⊥) , proj₁


SL-double-comp : {X : Set} → (a : SL X) → SL→ X a (SL-comp (SL-comp a))
SL-double-comp (I , f) i = ((f i) , (λ H eq → proj₂ H i (sym eq))) , refl


-- arbitrary join
SL-⋁ : {X U : Set} → (U → SL X) → SL X
SL-⋁ {X} {U} f = (Σ U λ u → proj₁ (f u)) , (λ {(u , i) → proj₂ (f u) i})


SL-⋁-union : {X U V : Set} → (f : U → SL X) → (g : V → SL X)
  → SL-sim X (SL-⋁ [ f , g ]) (join (SL-⋁ f) (SL-⋁ g))
proj₁ (SL-⋁-union f g) (inj₁ u , i) = (inj₁ (u , i)) , refl
proj₁ (SL-⋁-union f g) (inj₂ v , j) = (inj₂ (v , j)) , refl
proj₂ (SL-⋁-union f g) (inj₁ (u , i)) = (inj₁ u , i) , refl
proj₂ (SL-⋁-union f g) (inj₂ (v , j)) = (inj₂ v , j) , refl


-- arbitrary meet
SL-⋀ : {X U : Set} → (U → SL X) → SL X
SL-⋀ {X} {U} f = (Σ X λ x → (u : U) → Σ (proj₁ (f u)) λ i → proj₂ (f u) i ≡ x) ,
  λ {(x , H) → x}


SL-⋀-union : {X U V : Set} → (f : U → SL X) → (g : V → SL X)
  → SL-sim X (SL-⋀ [ f , g ]) (meet (SL-⋀ f) (SL-⋀ g))
proj₁ (SL-⋀-union f g) (x , H) = (((x , (λ u → (H (inj₁ u)))) , x , (λ v → H (inj₂ v))) ,
  refl) , refl
proj₂ (SL-⋀-union f g) (((x , H) , .x , K) , refl) =
  (x , (λ { (inj₁ u) → H u ; (inj₂ v) → K v})) , refl


SL-dist : {X U : Set} → {V : U → Set} → (F : (u : U) → (v : V u) → SL X)
  → SL-sim X (SL-⋀ (λ u → SL-⋁ (F u)))
             (SL-⋁ {X} {(u : U) → V u} λ h → SL-⋀ {X} {U} λ u → F u (h u))
proj₁ (SL-dist F) (x , H) = ((λ u → proj₁ (proj₁ (H u))) , x ,
  (λ u → (proj₂ (proj₁ (H u))) , (proj₂ (H u)))) , refl
proj₂ (SL-dist F) (H , x , K) = (x , (λ u → ((H u) , (proj₁ (K u))) , (proj₂ (K u)))) , refl


-- Second distribution law does not appear to work constructively

--SL-dist2 : {X U : Set} → {V : U → Set} → (F : (u : U) → (v : V u) → SL X)
--  → SL-sim X (SL-⋁ (λ u → SL-⋀ (F u)))
--             (SL-⋀ {X} {(u : U) → V u} λ h → SL-⋁ {X} {U} λ u → F u (h u))
--proj₁ (SL-dist2 F) (u , x , H) =
--  (x , (λ f → (u , (proj₁ (H (f u)))) , proj₂ (H (f u)))) , refl
--proj₂ (SL-dist2 F) (x , H) = ({!!} , {!!}) , {!!}
