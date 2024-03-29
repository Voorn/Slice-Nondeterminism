module Slice.Relator where

open import Data.Unit
open import Data.Empty
open import Data.Sum renaming (map to map⊎)
open import Data.Nat hiding (_⊔_)
open import Data.Product renaming (map to map×)
open import Relation.Binary.PropositionalEquality hiding ([_])

open import Slice.Base
open import Relations.Ext-Rel


-- The three relators for nondeterministic computation

SL-relat : Set₁
SL-relat = {X Y : Set} → ER X Y → SL X → SL Y → Set

-- properties
SL-relat-id : SL-relat → Set₁
SL-relat-id Γ = {X : Set} → (a : SL X) → Γ (_≡_) a a 

SL-relat-⊂ : SL-relat → Set₁
SL-relat-⊂ Γ = {X Y : Set} → (R S : ER X Y) → ER≤ R S
  → (a : SL X) → (b : SL Y) → Γ R a b → Γ S a b

SL-relat-comp : SL-relat → Set₁
SL-relat-comp Γ = {X Y Z : Set} → (R : ER X Y) → (S : ER Y Z)
  → (a : SL X) → (b : SL Y) → (c : SL Z) → Γ R a b → Γ S b c → Γ (ER-∘ R S) a c

SL-relat-nat : SL-relat → Set₁
SL-relat-nat Γ = {X X' Y Y' : Set} → (R : ER Y Y')
  → (f : X → Y) → (g : X' → Y') → (a : SL X) → (b : SL X')
  → Γ R (SL-fun f a) (SL-fun g b) ≡ Γ (λ x x' → R (f x) (g x')) a b

-- Monad
SL-relat-η : SL-relat → Set₁
SL-relat-η Γ = {X Y : Set} → (R : ER X Y) → (x : X) → (y : Y) → (R x y) → Γ R (SL-η X x) (SL-η Y y)

SL-relat-κ : SL-relat → Set₁
SL-relat-κ Γ = {X X' Y Y' : Set} → (R : ER X X') → (S : ER Y Y') → (a : SL X) → (b : SL X') → (Γ R a b)
  → (f : X → SL Y) → (g : X' → SL Y') → ((x : X) → (x' : X') → R x x' → Γ S (f x) (g x'))
  → Γ S (SL-* f a) (SL-* g b)


-- Angelic nondeterminism
Ang-Relat : SL-relat
Ang-Relat R (I , f) (J , g) = Σ (I → J) λ K → (i : I) → R (f i) (g (K i))

AR-left-sim : {X Y : Set} → (R : ER X Y) → (U U' : SL X) → (V : SL Y)
  → Ang-Relat R U V → SL-sim X U U' → Ang-Relat R U' V
proj₁ (AR-left-sim R U U' V (K , rel) (U⊂U' , U'⊂U)) = (λ i → K (proj₁ (U'⊂U i)))
proj₂ (AR-left-sim R U U' V (K , rel) (U⊂U' , U'⊂U)) i rewrite proj₂ (U'⊂U i) = rel (proj₁ (U'⊂U i))

AR-right-sim : {X Y : Set} → (R : ER X Y) → (U : SL X) → (V V' : SL Y)
  → Ang-Relat R U V → SL-sim Y V V' → Ang-Relat R U V'
proj₁ (AR-right-sim R U V V' (K , rel) (V⊂V' , V'⊂V)) i = proj₁ (V⊂V' (K i))
proj₂ (AR-right-sim R U V V' (K , rel) (V⊂V' , V'⊂V)) i rewrite sym (proj₂ (V⊂V' (K i))) = rel i


AR-id : SL-relat-id (Ang-Relat)
AR-id a = (λ i → i) , λ i → refl

AR-comp : SL-relat-comp (Ang-Relat)
AR-comp R S a b c (F , rel) (G , rel') = (λ i → G (F i)) ,
  λ i → (proj₂ b (F i)) , rel i , rel' (F i)

AR-⊂ : SL-relat-⊂ (Ang-Relat)
AR-⊂ R S R<S a b (F , rel) = F , λ i → R<S _ _ (rel i)

AR-nat : SL-relat-nat (Ang-Relat)
AR-nat R f g a b = refl

AR-η : SL-relat-η (Ang-Relat)
AR-η R x y xRy = (λ i → tt) , λ i → xRy

AR-κ : SL-relat-κ (Ang-Relat)
proj₁ (AR-κ R S a b a<b f g f<g) (i , j) = (proj₁ a<b i) ,
  (proj₁ (f<g (proj₂ a i) (proj₂ b (proj₁ a<b i)) (proj₂ a<b i)) j)
proj₂ (AR-κ R S a b a<b f g f<g) (i , j) =
  proj₂ (f<g (proj₂ a i) (proj₂ b (proj₁ a<b i)) (proj₂ a<b i)) j


-- Demonic nondeterminism
Dem-Relat : SL-relat
Dem-Relat R (I , f) (J , g) = Σ (J → I) λ K → (j : J) → R (f (K j)) (g j)


DR-id : SL-relat-id (Dem-Relat)
DR-id a = (λ i → i) , λ i → refl

DR-comp : SL-relat-comp (Dem-Relat)
DR-comp R S a b c (F , rel) (G , rel') = (λ j → F (G j)) ,
  λ j → (proj₂ b (G j)) , rel (G j) , rel' j

DR-⊂ : SL-relat-⊂ (Dem-Relat)
DR-⊂ R S R<S a b (F , rel) = F , (λ j → R<S _ _ (rel j))

DR-nat : SL-relat-nat (Dem-Relat)
DR-nat R f g a b = refl

DR-η : SL-relat-η (Dem-Relat)
DR-η R x y xRy = (λ i → tt) , λ i → xRy

DR-κ : SL-relat-κ (Dem-Relat)
proj₁ (DR-κ R S a b a<b f g f<g) (j , i) = (proj₁ a<b j) ,
  (proj₁ (f<g (proj₂ a (proj₁ a<b j)) (proj₂ b j) (proj₂ a<b j)) i)
proj₂ (DR-κ R S a b a<b f g f<g) (j , i) = proj₂ (f<g (proj₂ a (proj₁ a<b j)) (proj₂ b j) (proj₂ a<b j)) i


-- Convex nondeterminism relator
Con-Relat : SL-relat
Con-Relat R a b = Ang-Relat R a b × Dem-Relat R a b


CR-id : SL-relat-id (Con-Relat)
CR-id a = (AR-id a) , (DR-id a)

CR-comp : SL-relat-comp (Con-Relat)
CR-comp R S a b c (aARb , aDRb) (bASc , bDSc) =
  (AR-comp R S a b c aARb bASc) , (DR-comp R S a b c aDRb bDSc)

CR-⊂ : SL-relat-⊂ (Con-Relat)
CR-⊂ R S R<S a b (aARb , aDRb) = (AR-⊂ R S R<S a b aARb) , DR-⊂ R S R<S a b aDRb

CR-nat : SL-relat-nat (Con-Relat)
CR-nat R f g a b = refl

CR-η : SL-relat-η (Con-Relat)
CR-η R x y xRy = (AR-η R x y xRy) , (DR-η R x y xRy)

CR-κ : SL-relat-κ (Con-Relat)
CR-κ R S a b (a-A-b , a-D-b) f g f<g =
  AR-κ R S a b a-A-b f g (λ x x' xRx' → proj₁ (f<g x x' xRx')) ,
  DR-κ R S a b a-D-b f g (λ x x' xRx' → proj₂ (f<g x x' xRx'))
