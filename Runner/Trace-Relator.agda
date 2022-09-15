module Runner.Trace-Relator where


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

open import Monads.Trace
open import Runner.Trace-Runner



Rel : (X Y : Set) → Set₁
Rel X Y = X → Y → Set

Rel₁ : (X Y : Set₁) → Set₁
Rel₁ X Y = X → Y → Set

Rel× : {A B C D : Set} → Rel A B → Rel C D → Rel (A × C) (B × D)
Rel× S R (a , c) (b , d) = S a b × R c d


Rela-id : (X : Set) → Rel X X
Rela-id X = _≡_

Rela-comp : {X Y Z : Set} → Rel X Y → Rel Y Z → Rel X Z
Rela-comp S R x z = Σ _ λ y → S x y × R y z

Rela-sub : {X Y : Set} → Rel₁ (Rel X Y) (Rel X Y)
Rela-sub S R = (x : _) → (y : _) → S x y → R x y

Rela-eq : {X Y : Set} → Rel₁ (Rel X Y) (Rel X Y)
Rela-eq S R = Rela-sub S R × Rela-sub R S

Rela-tp : {X Y X' Y' : Set} → (f : X → X') → (g : Y → Y') → Rel X' Y' → Rel X Y
Rela-tp f g R x y = R (f x) (g y) 



Rela-refl : {X : Set} → Rel X X → Set
Rela-refl R = (x : _) → R x x

Rela-trans : {X : Set} → Rel X X → Set
Rela-trans R = {x y z : _} → R x y → R y z → R x z

Rela-preo : {X : Set} → Rel X X → Set
Rela-preo R = Rela-refl R × Rela-trans R





Trace-Relator : (A E : Set) → Set₁
Trace-Relator A E = {X Y : Set} → Rel X Y → Rel (Trace A E X) (Trace A E Y)

Trace-Relator-sub : {A E : Set} → (Trace-Relator A E) → (Trace-Relator A E) → Set₁
Trace-Relator-sub Γ Γ' = {X Y : Set} → (R : Rel X Y) → Rela-sub (Γ R) (Γ' R)




TRel-id : {A E : Set} → Trace-Relator A E → Set₁
TRel-id Γ = (X : Set) → Rela-sub (Rela-id (Trace _ _ X)) (Γ (Rela-id X))

TRel-comp : {A E : Set} → Trace-Relator A E → Set₁
TRel-comp Γ = {X Y Z : Set} → (S : Rel X Y) → (R : Rel Y Z)
  → Rela-sub (Rela-comp (Γ S) (Γ R)) (Γ (Rela-comp S R))

TRel-sub : {A E : Set} → Trace-Relator A E → Set₁
TRel-sub Γ = {X Y : Set} → (S R : Rel X Y) → Rela-sub S R → Rela-sub (Γ S) (Γ R)

TRel-nat< : {A E : Set} → Trace-Relator A E → Set₁
TRel-nat< Γ = {X Y X' Y' : Set} → (R : Rel X' Y') → (f : X → X') → (g : Y → Y')
  → Rela-sub (Rela-tp (Trace-map _ _ f) (Trace-map _ _ g) (Γ R)) (Γ (Rela-tp f g R))

TRel-nat> : {A E : Set} → Trace-Relator A E → Set₁
TRel-nat> Γ = {X Y X' Y' : Set} → (R : Rel X' Y') → (f : X → X') → (g : Y → Y')
  → Rela-sub (Γ (Rela-tp f g R)) (Rela-tp (Trace-map _ _ f) (Trace-map _ _ g) (Γ R))


record TRel-prop {A E : Set} (Γ : Trace-Relator A E) : Set₁ where
  field
    Γ-id : TRel-id Γ
    Γ-comp : TRel-comp Γ
    Γ-sub : TRel-sub Γ
    Γ-nat< : TRel-nat< Γ
    Γ-nat> : TRel-nat> Γ



TRel-η : {A E : Set} → Trace-Relator A E → Set₁
TRel-η Γ = {X Y : Set} → (R : Rel X Y) → Rela-sub R (λ x y → Γ R (ret x) (ret y))

TRel-μ : {A E : Set} → Trace-Relator A E → Set₁
TRel-μ Γ = {X Y : Set} → (R : Rel X Y)
  → Rela-sub (Γ (Γ R)) (λ d d' → Γ R (Trace-μ _ _ X d) (Trace-μ _ _ Y d')) 

TRel-κ : {A E : Set} → Trace-Relator A E → Set₁
TRel-κ Γ = {X Y X' Y' : Set} → (S : Rel X Y) → (R : Rel X' Y')
  → (f : X → Trace _ _ X') → (g : Y → Trace _ _ Y')
  → (l : Trace _ _ X) → (r : Trace _ _ Y)
  → ((x : X) → (y : Y) → (S x y) → (Γ R (f x) (g y)))
  → (Γ S l r) → Γ R (Trace-κ _ _ X X' f l) (Trace-κ _ _ Y Y' g r)



-- Nondeterminism
SL-Relator : {A E : Set} → (Γ : Trace-Relator A E) → {X Y : Set}
  → Rel X Y → Rel₁ (SL (Trace A E X)) (SL (Trace A E Y))
SL-Relator Γ R (I , V) (J , W) = (i : I) → Σ J λ j → Γ R (V i) (W j) 


-- This property combine Pow-distributivity and μ-property
TRel-SL : {A E : Set} → (Trace-Relator A E) → Set₁
TRel-SL Γ = {X Y X' Y' : Set} → (R : Rel X' Y')
  → (f : SF X (Trace _ _ X')) → (g : SF Y (Trace _ _ Y'))
  → (SF-Total g)
  → (t : Trace _ _ X) → (r : Trace _ _ Y)
  → Γ (λ a b → SL-Relator Γ R (f a) (g b)) t r
  → SL-Relator Γ R (SF-∘ (SF-T _ _ f) (SF-T-μ _ _ _) t)
                    (SF-∘ (SF-T _ _ g) (SF-T-μ _ _ _) r)
