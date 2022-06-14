module Structure where

open import Data.Unit
open import Data.Empty
open import Data.Sum renaming (map to map⊎)
open import Data.Nat hiding (_⊔_)
open import Data.Product renaming (map to map×)
open import Relation.Binary.PropositionalEquality hiding ([_])


open import Index-Nondeterminism
open import Monoidal



-- Spawn, a.k.a. the unit for ×
PK-η : (X : Set) → PK-Hom ⊤ X
PK-η X tt = X , (λ x → x)


PK-η-nat> : {X Y : Set} → (f : PK-Hom X Y) → Pow-< (PK-∘ (PK-η X) f) (PK-η Y)
PK-η-nat> f tt (x , i) = (proj₂ (f x) i) , refl


PK-η-nat<-Surje : {X Y : Set} → (f : PK-Hom X Y)
  → Pow-< (PK-η Y) (PK-∘ (PK-η X) f) → PK-Surje f
PK-η-nat<-Surje f rel y with rel tt y
... | ((x , i) , eq) = x , i , sym eq


PK-Surje-η-nat< : {X Y : Set} → (f : PK-Hom X Y)
  → PK-Surje f → Pow-< (PK-η Y) (PK-∘ (PK-η X) f)
PK-Surje-η-nat< f fsur tt y with fsur y
... | x , i , eq = (x , i) , sym eq


-- Corollary, η is natural in the category of surjective relations

PK-Surje-η-nat : {X Y : Set} → (f : PK-Hom X Y)
  → PK-Surje f → PK-≡ (PK-η Y) (PK-∘ (PK-η X) f)
PK-Surje-η-nat f fsur = (PK-Surje-η-nat< f fsur) , (PK-η-nat> f)



-- Comparitor, a.k.a. multiplication
PK-μ : (X : Set) → PK-Hom (X × X) X
PK-μ X (x , y) = (x ≡ y) , (λ i → x)


PK-μ-nat> : {X Y : Set} → (f : PK-Hom X Y) → Pow-< (PK-∘ (PK-μ X) f) (PK-∘ (f ⊗ f) (PK-μ Y))
PK-μ-nat> f (x , .x) (refl , i) = ((i , i) , refl) , refl


PK-μ-nat<-Injec : {X Y : Set} → (f : PK-Hom X Y)
  → (Pow-< (PK-∘ (f ⊗ f) (PK-μ Y)) (PK-∘ (PK-μ X) f)) → PK-Injec f 
PK-μ-nat<-Injec f rel x x' i j eq = proj₁ (proj₁ (rel (x , x') ((i , j) , eq))) 


PK-Injec-μ-nat< : {X Y : Set} → (f : PK-Hom X Y)
  → PK-Injec f → (Pow-< (PK-∘ (f ⊗ f) (PK-μ Y)) (PK-∘ (PK-μ X) f))
PK-Injec-μ-nat< f finje (x , x') ((i , i') , eq) = (finje x x' i i' eq , i) , refl


-- Corollary: μ is natural in the category of Injective relations

PK-Injec-μ-nat : {X Y : Set} → (f : PK-Hom X Y)
  → PK-Injec f → (PK-≡ (PK-∘ (f ⊗ f) (PK-μ Y)) (PK-∘ (PK-μ X) f))
PK-Injec-μ-nat f finje = (PK-Injec-μ-nat< f finje) , (PK-μ-nat> f)



-- Delete, or the co-unit operation for ×
PK-ε : (X : Set) → PK-Hom X ⊤
PK-ε X x = ⊤ , (λ i → tt)


PK-η-rev : (X : Set) → PK-≡ (PK-rev (PK-η X)) (PK-ε X)
proj₁ (PK-η-rev X) x (tt , .x , refl) = tt , refl
proj₂ (PK-η-rev X) x tt = (tt , (x , refl)) , refl



PK-ε-nat< : {X Y : Set} → (f : PK-Hom X Y) → Pow-< (PK-∘ f (PK-ε Y)) (PK-ε X)
PK-ε-nat< f x (i , tt) = tt , refl


PK-ε-nat>-Total : {X Y : Set} → (f : PK-Hom X Y)
  → Pow-< (PK-ε X) (PK-∘ f (PK-ε Y)) → PK-Total f
PK-ε-nat>-Total f rel x = proj₁ (proj₁ (rel x tt))


PK-Total-ε-nat> : {X Y : Set} → (f : PK-Hom X Y)
  → PK-Total f → Pow-< (PK-ε X) (PK-∘ f (PK-ε Y))
PK-Total-ε-nat> f ftot x tt = ((ftot x) , tt) , refl


-- Corollary: ε is natural in the category of total relations

PK-Total-ε-nat : {X Y : Set} → (f : PK-Hom X Y)
  → PK-Total f → PK-≡ (PK-∘ f (PK-ε Y)) (PK-ε X)
PK-Total-ε-nat f ftot = (PK-ε-nat< f) , (PK-Total-ε-nat> f ftot)





-- Copy, or comultiplication operation for ×
PK-δ : (X : Set) → PK-Hom X (X × X)
PK-δ X x = PK-Id _ (x , x)


PK-μ-rev : (X : Set) → PK-≡ (PK-rev (PK-μ X)) (PK-δ X)
proj₁ (PK-μ-rev X) x ((.x , .x) , refl , refl) = tt , refl
proj₂ (PK-μ-rev X) x tt = ((x , x) , (refl , refl)) , refl



PK-δ-nat< : {X Y : Set} → (f : PK-Hom X Y)
  → (Pow-< (PK-∘ f (PK-δ Y)) (PK-∘ (PK-δ X) (f ⊗ f)))
PK-δ-nat< f x (i , tt) = (tt , (i , i)) , refl


PK-δ-nat>-Onele : {X Y : Set} → (f : PK-Hom X Y)
  → Pow-< (PK-∘ (PK-δ X) (f ⊗ f)) (PK-∘ f (PK-δ Y)) → PK-Onele f
PK-δ-nat>-Onele f rel x i j with proj₂ (rel x (tt , i , j))
... | k = trans (cong proj₁ k) (sym (cong proj₂ k))


PK-Onele-δ-nat> : {X Y : Set} → (f : PK-Hom X Y)
  → PK-Onele f → Pow-< (PK-∘ (PK-δ X) (f ⊗ f)) (PK-∘ f (PK-δ Y))
PK-Onele-δ-nat> f fone x (tt , i , j) = (i , tt) ,
  (cong (λ k → (proj₂ (f x) i , k)) (fone x j i))


-- Corollary, δ is natural in the category of partial maps

PK-Onele-δ-nat : {X Y : Set} → (f : PK-Hom X Y)
  → PK-Onele f → PK-≡ (PK-∘ f (PK-δ Y)) (PK-∘ (PK-δ X) (f ⊗ f))
PK-Onele-δ-nat f fone =  (PK-δ-nat< f) , (PK-Onele-δ-nat> f fone)





-- To do: equations
PK-μ-assoc : (X : Set) → PK-≡ (PK-∘ ((PK-μ X) ⊗ (PK-Id _)) (PK-μ X))
                              (PK-∘ (⊗-α X X X) (PK-∘ ((PK-Id _) ⊗ (PK-μ X)) (PK-μ X)))
proj₁ (PK-μ-assoc X) ((x , .x) , .x) ((refl , tt) , refl) =
  (tt , ((tt , refl) , refl)) , refl
proj₂ (PK-μ-assoc X) ((x , .x) , .x) (tt , (tt , refl) , refl) =
  ((refl , tt) , refl) , refl


PK-μ-symm : (X : Set) → PK-≡ (PK-∘ (⊗-γ X X) (PK-μ X)) (PK-μ X)
proj₁ (PK-μ-symm X) (x , .x) (tt , refl) = refl , refl
proj₂ (PK-μ-symm X) (x , .x) refl = (tt , refl) , refl


PK-χ : (X : Set) → PK-Hom (X × X) (X × X)
PK-χ X = PK-∘ (PK-μ X) (PK-δ X)


PK-Frob-l : (X : Set) → PK-≡ (PK-∘ (PK-δ X ⊗ PK-Id X) (PK-∘ (⊗-α X X X) (PK-Id X ⊗ PK-μ X)))
                             (PK-χ X)
proj₁ (PK-Frob-l X) (x , .x) ((tt , tt) , tt , tt , refl) = (refl , tt) , refl
proj₂ (PK-Frob-l X) (x , .x) (refl , tt) = ((tt , tt) , tt , tt , refl) , refl


PK-Frob-r : (X : Set)
  → PK-≡ (PK-∘ (PK-Id X ⊗ PK-δ X) (PK-∘ (⊗-α' X X X) (PK-μ X ⊗ PK-Id X)))
         (PK-χ X)
proj₁ (PK-Frob-r X) (x , .x) ((tt , tt) , tt , refl , tt) = (refl , tt) , refl
proj₂ (PK-Frob-r X) (x , .x) (refl , tt) = ((tt , tt) , tt , refl , tt) , refl


PK-δμ : (X : Set) → PK-≡ (PK-∘ (PK-δ X) (PK-μ X)) (PK-Id X)
proj₁ (PK-δμ X) x (tt , refl) = tt , refl
proj₂ (PK-δμ X) x tt = (tt , refl) , refl
