module Slice-Functions.Structure where

open import Data.Unit
open import Data.Empty
open import Data.Sum renaming (map to map⊎)
open import Data.Nat hiding (_⊔_)
open import Data.Product renaming (map to map×)
open import Relation.Binary.PropositionalEquality hiding ([_])


open import Slice-Functions.Base
open import Slice-Functions.Subcategories
open import Slice-Functions.Monoidal
open import Slice-Functions.Dagger



-- Spawn, a.k.a. the unit for ×
SF-η : (X : Set) → SF ⊤ X
SF-η X tt = X , (λ x → x)


SF-η-nat> : {X Y : Set} → (f : SF X Y) → SF≤ (SF-∘ (SF-η X) f) (SF-η Y)
SF-η-nat> f tt (x , i) = (proj₂ (f x) i) , refl


SF-η-nat<-Surje : {X Y : Set} → (f : SF X Y)
  → SF≤ (SF-η Y) (SF-∘ (SF-η X) f) → SF-Surje f
SF-η-nat<-Surje f rel y with rel tt y
... | ((x , i) , eq) = x , i , sym eq


SF-Surje-η-nat< : {X Y : Set} → (f : SF X Y)
  → SF-Surje f → SF≤ (SF-η Y) (SF-∘ (SF-η X) f)
SF-Surje-η-nat< f fsur tt y with fsur y
... | x , i , eq = (x , i) , sym eq


-- Corollary, η is natural in the category of surjective relations

SF-Surje-η-nat : {X Y : Set} → (f : SF X Y)
  → SF-Surje f → SF≡ (SF-η Y) (SF-∘ (SF-η X) f)
SF-Surje-η-nat f fsur = (SF-Surje-η-nat< f fsur) , (SF-η-nat> f)

SF-η-nat⇒Surje : {X Y : Set} → (f : SF X Y)
  → SF≡ (SF-η Y) (SF-∘ (SF-η X) f) → SF-Surje f
SF-η-nat⇒Surje f (i , j) y with i tt y
... | (x , u) , refl = x , (u , refl)


-- Comparitor, a.k.a. multiplication
SF-μ : (X : Set) → SF (X × X) X
SF-μ X (x , y) = (x ≡ y) , (λ i → x)


SF-μ-nat> : {X Y : Set} → (f : SF X Y) → SF≤ (SF-∘ (SF-μ X) f) (SF-∘ (f ⊗ f) (SF-μ Y))
SF-μ-nat> f (x , .x) (refl , i) = ((i , i) , refl) , refl


SF-μ-nat<-Injec : {X Y : Set} → (f : SF X Y)
  → (SF≤ (SF-∘ (f ⊗ f) (SF-μ Y)) (SF-∘ (SF-μ X) f)) → SF-Injec f 
SF-μ-nat<-Injec f rel x x' i j eq = proj₁ (proj₁ (rel (x , x') ((i , j) , eq))) 


SF-Injec-μ-nat< : {X Y : Set} → (f : SF X Y)
  → SF-Injec f → (SF≤ (SF-∘ (f ⊗ f) (SF-μ Y)) (SF-∘ (SF-μ X) f))
SF-Injec-μ-nat< f finje (x , x') ((i , i') , eq) = (finje x x' i i' eq , i) , refl


-- Corollary: μ is natural in the category of Injective relations

SF-Injec-μ-nat : {X Y : Set} → (f : SF X Y)
  → SF-Injec f → (SF≡ (SF-∘ (f ⊗ f) (SF-μ Y)) (SF-∘ (SF-μ X) f))
SF-Injec-μ-nat f finje = (SF-Injec-μ-nat< f finje) , (SF-μ-nat> f)

SF-μ-nat⇒Injec : {X Y : Set} → (f : SF X Y)
  → (SF≡ (SF-∘ (f ⊗ f) (SF-μ Y)) (SF-∘ (SF-μ X) f)) → SF-Injec f
SF-μ-nat⇒Injec f (a , b) x y i j eq = proj₁ (proj₁ (a (x , y) ((i , j) , eq)))


-- Delete, or the co-unit operation for ×
SF-ε : (X : Set) → SF X ⊤
SF-ε X x = ⊤ , (λ i → tt)


SF-η-dag : (X : Set) → SF≡ (SF-dag (SF-η X)) (SF-ε X)
proj₁ (SF-η-dag X) x (tt , .x , refl) = tt , refl
proj₂ (SF-η-dag X) x tt = (tt , (x , refl)) , refl



SF-ε-nat< : {X Y : Set} → (f : SF X Y) → SF≤ (SF-∘ f (SF-ε Y)) (SF-ε X)
SF-ε-nat< f x (i , tt) = tt , refl


SF-ε-nat>-Total : {X Y : Set} → (f : SF X Y)
  → SF≤ (SF-ε X) (SF-∘ f (SF-ε Y)) → SF-Total f
SF-ε-nat>-Total f rel x = proj₁ (proj₁ (rel x tt))


SF-Total-ε-nat> : {X Y : Set} → (f : SF X Y)
  → SF-Total f → SF≤ (SF-ε X) (SF-∘ f (SF-ε Y))
SF-Total-ε-nat> f ftot x tt = ((ftot x) , tt) , refl


-- Corollary: ε is natural in the category of total relations

SF-Total-ε-nat : {X Y : Set} → (f : SF X Y)
  → SF-Total f → SF≡ (SF-∘ f (SF-ε Y)) (SF-ε X)
SF-Total-ε-nat f ftot = (SF-ε-nat< f) , (SF-Total-ε-nat> f ftot)

SF-ε-nat⇒Total : {X Y : Set} → (f : SF X Y)
  → SF≡ (SF-∘ f (SF-ε Y)) (SF-ε X) → SF-Total f
SF-ε-nat⇒Total f (i , j) x = proj₁ (proj₁ (j x tt))



-- Copy, or comultiplication operation for ×
SF-δ : (X : Set) → SF X (X × X)
SF-δ X x = SF-id _ (x , x)


SF-μ-dag : (X : Set) → SF≡ (SF-dag (SF-μ X)) (SF-δ X)
proj₁ (SF-μ-dag X) x ((.x , .x) , refl , refl) = tt , refl
proj₂ (SF-μ-dag X) x tt = ((x , x) , (refl , refl)) , refl



SF-δ-nat< : {X Y : Set} → (f : SF X Y)
  → (SF≤ (SF-∘ f (SF-δ Y)) (SF-∘ (SF-δ X) (f ⊗ f)))
SF-δ-nat< f x (i , tt) = (tt , (i , i)) , refl


SF-δ-nat>-Onele : {X Y : Set} → (f : SF X Y)
  → SF≤ (SF-∘ (SF-δ X) (f ⊗ f)) (SF-∘ f (SF-δ Y)) → SF-Onele f
SF-δ-nat>-Onele f rel x i j with proj₂ (rel x (tt , i , j))
... | k = trans (cong proj₁ k) (sym (cong proj₂ k))


SF-Onele-δ-nat> : {X Y : Set} → (f : SF X Y)
  → SF-Onele f → SF≤ (SF-∘ (SF-δ X) (f ⊗ f)) (SF-∘ f (SF-δ Y))
SF-Onele-δ-nat> f fone x (tt , i , j) = (i , tt) ,
  (cong (λ k → (proj₂ (f x) i , k)) (fone x j i))


-- Corollary, δ is natural in the category of partial maps

SF-Onele-δ-nat : {X Y : Set} → (f : SF X Y)
  → SF-Onele f → SF≡ (SF-∘ f (SF-δ Y)) (SF-∘ (SF-δ X) (f ⊗ f))
SF-Onele-δ-nat f fone =  (SF-δ-nat< f) , (SF-Onele-δ-nat> f fone)

SF-δ-nat⇒Onele : {X Y : Set} → (f : SF X Y)
  → SF≡ (SF-∘ f (SF-δ Y)) (SF-∘ (SF-δ X) (f ⊗ f)) → SF-Onele f
SF-δ-nat⇒Onele f (a , b) x i j with b x (tt , i , j)
...| ((u , tt) , eq) = trans (cong proj₁ eq) (sym (cong proj₂ eq))


-- Equations
SF-μ-assoc : (X : Set) → SF≡ (SF-∘ ((SF-μ X) ⊗ (SF-id _)) (SF-μ X))
                             (SF-∘ (⊗-α X X X) (SF-∘ ((SF-id _) ⊗ (SF-μ X)) (SF-μ X)))
proj₁ (SF-μ-assoc X) ((x , .x) , .x) ((refl , tt) , refl) =
  (tt , ((tt , refl) , refl)) , refl
proj₂ (SF-μ-assoc X) ((x , .x) , .x) (tt , (tt , refl) , refl) =
  ((refl , tt) , refl) , refl


SF-μ-symm : (X : Set) → SF≡ (SF-∘ (⊗-γ X X) (SF-μ X)) (SF-μ X)
proj₁ (SF-μ-symm X) (x , .x) (tt , refl) = refl , refl
proj₂ (SF-μ-symm X) (x , .x) refl = (tt , refl) , refl


SF-χ : (X : Set) → SF (X × X) (X × X)
SF-χ X = SF-∘ (SF-μ X) (SF-δ X)


SF-Frob-l : (X : Set) → SF≡ (SF-∘ (SF-δ X ⊗ SF-id X) (SF-∘ (⊗-α X X X) (SF-id X ⊗ SF-μ X)))
                             (SF-χ X)
proj₁ (SF-Frob-l X) (x , .x) ((tt , tt) , tt , tt , refl) = (refl , tt) , refl
proj₂ (SF-Frob-l X) (x , .x) (refl , tt) = ((tt , tt) , tt , tt , refl) , refl


SF-Frob-r : (X : Set)
  → SF≡ (SF-∘ (SF-id X ⊗ SF-δ X) (SF-∘ (⊗-α' X X X) (SF-μ X ⊗ SF-id X)))
         (SF-χ X)
proj₁ (SF-Frob-r X) (x , .x) ((tt , tt) , tt , refl , tt) = (refl , tt) , refl
proj₂ (SF-Frob-r X) (x , .x) (refl , tt) = ((tt , tt) , tt , refl , tt) , refl


SF-δμ : (X : Set) → SF≡ (SF-∘ (SF-δ X) (SF-μ X)) (SF-id X)
proj₁ (SF-δμ X) x (tt , refl) = tt , refl
proj₂ (SF-δμ X) x tt = (tt , refl) , refl
