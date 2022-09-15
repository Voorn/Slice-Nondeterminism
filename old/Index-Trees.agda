module Index-Trees where

open import Data.Unit
open import Data.Empty
open import Data.Sum renaming (map to map⊎)
open import Data.Nat hiding (_⊔_)
open import Data.Product renaming (map to map×)
open import Relation.Binary.PropositionalEquality hiding ([_])

postulate fun-ext : {X Y : Set} → {f g : X → Y} → ((x : X) → f x ≡ g x) → (f ≡ g)

postulate dep-ext : {X : Set} → {F : X → Set} → {f g : (x : X) → F x} → ((x : X) → f x ≡ g x) → f ≡ g

postulate fun-ext₁ : {X : Set} → {Y : Set₁} → {f g : X → Y} → ((x : X) → f x ≡ g x) → (f ≡ g)


data IT (X : Set) : Set₁ where
  retu : X → IT X
  choi : (I : Set) → (ts : I → IT X) → IT X


IT-κ : {X Y : Set} → (X → IT Y) → (IT X → IT Y)
IT-κ f (retu x) = f x
IT-κ f (choi I ts) = choi I (λ i → IT-κ f (ts i))


IT-κ1 : (X : Set) → (a : IT X) → IT-κ (retu {X}) a ≡ a
IT-κ1 X (retu x) = refl
IT-κ1 X (choi I ts) = cong (choi I) (fun-ext₁ (λ i → IT-κ1 X (ts i)))


IT-κ2 : {X Y : Set} → (f : X → IT Y) → (λ a → ((IT-κ f) (retu {X} a))) ≡ f 
IT-κ2 f = refl


IT-κ3 : {X Y Z : Set} → (f : X → IT Y) → (g : Y → IT Z) → (a : IT X)
  → (IT-κ g (IT-κ f a) ≡ IT-κ (λ x → IT-κ g (f x)) a)
IT-κ3 f g (retu x) = refl
IT-κ3 f g (choi I ts) = cong (choi I) (fun-ext₁ (λ i → IT-κ3 f g (ts i)))


open import Coslice

IT→CS : (X : Set) → IT X → CS X
IT→CS X (retu x) = ⊤ , (λ i → x)
IT→CS X (choi I ts) = (Σ I λ i → proj₁ (IT→CS X (ts i))) ,
  (λ {(i , j) → proj₂ (IT→CS X (ts i)) j})


IT→CS-κ : {X Y : Set} → (f : X → IT Y) → (a : IT X)
  → CS-sim Y (IT→CS Y (IT-κ f a)) (CS-* (λ x → IT→CS Y (f x)) (IT→CS X a))
IT→CS-κ f (retu x) = (λ i → (tt , i) , refl) ,
                     (λ {(tt , i) → i , refl})
IT→CS-κ f (choi I ts) = (λ {(i , j) → ((i , (proj₁ (proj₁ (proj₁ (IT→CS-κ f (ts i)) j)))) ,
  (proj₂ (proj₁ (proj₁ (IT→CS-κ f (ts i)) j)))) , (proj₂ (proj₁ (IT→CS-κ f (ts i)) j))}) ,
    λ {((i , j) , k) → (i , (proj₁ (proj₂ (IT→CS-κ f (ts i)) (j , k)) )) ,
      (proj₂ (proj₂ (IT→CS-κ f (ts i)) (j , k)) )}
