module Examples.Process-Algebra where

open import Data.Unit
open import Data.Empty
open import Data.Sum renaming (map to map⊎)
open import Data.Nat hiding (_⊔_)
open import Data.Product renaming (map to map×)
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Data.Bool

open import Slice.Base
open import Slice.Lattice

open import Slice-Functions.Base

open import Examples.Transition


data PA (A : Set) : Set where
  at : A → PA A
  _⊕_ : PA A → PA A → PA A
  _·_ : PA A → PA A → PA A
  _𝕀_ : PA A → PA A → PA A
  _𝕃_ : PA A → PA A → PA A


SL-2* : {X Y Z : Set} → (X → Y → SL Z) → (SL X → SL Y → SL Z)
SL-2* f a b = SL-* (λ p → SL-* (f p) b) a

Cong-SL-2* : {X Y Z : Set} → (f : X → Y → SL Z) → (x x' : SL X) → (y y' : SL Y)
  → SL→ X x x' → SL→ Y y y' → SL→ Z (SL-2* f x y) (SL-2* f x' y')
proj₁ (proj₁ (Cong-SL-2* f x x' y y' x→x' y→y' (ix , iy , c))) = proj₁ (x→x' ix)
proj₁ (proj₂ (proj₁ (Cong-SL-2* f x x' y y' x→x' y→y' (ix , iy , c)))) = proj₁ (y→y' iy)
proj₂ (proj₂ (proj₁ (Cong-SL-2* f x x' y y' x→x' y→y' (ix , iy , c)))) 
  rewrite proj₂ (x→x' ix) | proj₂ (y→y' iy) = c
proj₂ (Cong-SL-2* f x x' y y' x→x' y→y' (ix , iy , c)) 
  rewrite proj₂ (x→x' ix) | proj₂ (y→y' iy) = refl

append* : {A : Set} → SL (Lis A) → SL (Lis A) → SL (Lis A)
append* l r = SL-* (λ a → SL-fun (append a) r) l

Cong-append : {A : Set} → (x x' y y' : SL (Lis A)) → SL→ (Lis A) x x' → SL→ (Lis A) y y'
  → SL→ (Lis A) (SL-* (λ a → SL-fun (append a) y) x) (SL-* (λ a → SL-fun (append a) y') x')
Cong-append x x' y y' x→x' y→y' (ix , iy) with (x→x' ix , y→y' iy)
... | (ix' , eq-x) , (iy' , eq-y) rewrite eq-x | eq-y = (ix' , iy') , refl

Lis-𝕀 : {A : Set} → Lis A → Lis A → SL (Lis A)
Lis-𝕃 : {A : Set} → Lis A → Lis A → SL (Lis A)
Lis-𝕀 p q = join (Lis-𝕃 p q) (Lis-𝕃 q p)
Lis-𝕃 uni q = SL-η _ q
Lis-𝕃 (act a p) q = SL-fun (act a) (Lis-𝕀 p q)

Lis-𝕀* : {A : Set} → SL (Lis A) → SL (Lis A) → SL (Lis A)
Lis-𝕃* : {A : Set} → SL (Lis A) → SL (Lis A) → SL (Lis A)
Lis-𝕀* = SL-2* Lis-𝕀
Lis-𝕃* = SL-2* Lis-𝕃


Lis-𝕃-con : {A : Set} → (l : Lis A) → (i : proj₁ (Lis-𝕃 l uni))
  → proj₂ (Lis-𝕃 l uni) i ≡ l
Lis-𝕃-con uni tt = refl
Lis-𝕃-con (act a l) (inj₁ x) = cong (act a) (Lis-𝕃-con l x)
Lis-𝕃-con (act a l) (inj₂ tt) = refl



-- A model for Process algebra by evaluation
PA-eval : {A : Set} → SF (PA A) (Lis A)
PA-eval (at a) = SL-η (Lis _) (act a uni)
PA-eval (P ⊕ Q) = join (PA-eval P) (PA-eval Q)
PA-eval (P · Q) = append* (PA-eval P) (PA-eval Q)
PA-eval (P 𝕀 Q) = Lis-𝕀* (PA-eval P) (PA-eval Q)
PA-eval (P 𝕃 Q) = Lis-𝕃* (PA-eval P) (PA-eval Q)

_PA≡_ : {A : Set} → PA A → PA A → Set
_PA≡_ {A} a b = SL-sim (Lis A) (PA-eval a) (PA-eval b)




-- Congruences
Cong-at : {A : Set} → (a : A) → ((at a) PA≡ (at a))
Cong-at a = (λ i → tt , refl) , (λ i → tt , refl)

Cong-⊕ : {A : Set} → (x x' y y' : PA A) → (x PA≡ x') → (y PA≡ y') → ((x ⊕ y) PA≡ (x' ⊕ y'))
Cong-⊕ x x' y y' (x≤x' , x'≤x) (y≤y' , y'≤y) = (join-< x≤x' y≤y') , (join-< x'≤x y'≤y)

Cong-· : {A : Set} → (x x' y y' : PA A) → (x PA≡ x') → (y PA≡ y') → ((x · y) PA≡ (x' · y'))
Cong-· x x' y y' (x≤x' , x'≤x) (y≤y' , y'≤y) =
  Cong-append (PA-eval x) (PA-eval x') (PA-eval y) (PA-eval y') x≤x' y≤y' ,
  Cong-append (PA-eval x') (PA-eval x) (PA-eval y') (PA-eval y) x'≤x y'≤y

Cong-𝕀 : {A : Set} → (x x' y y' : PA A) → (x PA≡ x') → (y PA≡ y') → ((x 𝕀 y) PA≡ (x' 𝕀 y'))
Cong-𝕀 x x' y y' (x≤x' , x'≤x) (y≤y' , y'≤y) =
  (Cong-SL-2* Lis-𝕀 (PA-eval x) (PA-eval x') (PA-eval y) (PA-eval y') x≤x' y≤y') ,
  (Cong-SL-2* Lis-𝕀 (PA-eval x') (PA-eval x) (PA-eval y') (PA-eval y) x'≤x y'≤y)

Cong-𝕃 : {A : Set} → (x x' y y' : PA A) → (x PA≡ x') → (y PA≡ y') → ((x 𝕃 y) PA≡ (x' 𝕃 y'))
Cong-𝕃 x x' y y' (x≤x' , x'≤x) (y≤y' , y'≤y) =
  (Cong-SL-2* Lis-𝕃 (PA-eval x) (PA-eval x') (PA-eval y) (PA-eval y') x≤x' y≤y') ,
  (Cong-SL-2* Lis-𝕃 (PA-eval x') (PA-eval x) (PA-eval y') (PA-eval y) x'≤x y'≤y)

-- Bergstra and Klop: Process Algebra for Communication, Table II equations

-- Table I BPA equations
A1-eq : {A : Set} → (x y : PA A) → (x ⊕ y) PA≡ (y ⊕ x)
A1-eq x y = join-symm (PA-eval x) (PA-eval y)

A2-eq : {A : Set} → (x y z : PA A) → (x ⊕ (y ⊕ z)) PA≡ ((x ⊕ y) ⊕ z)
A2-eq x y z = (λ { (inj₁ ix) → inj₁ (inj₁ ix) , refl ;
      (inj₂ (inj₁ iy)) → (inj₁ (inj₂ iy)) , refl ; (inj₂ (inj₂ iz)) → inj₂ iz , refl}) ,
  λ { (inj₁ (inj₁ ix)) → inj₁ ix , refl ; (inj₁ (inj₂ iy)) → inj₂ (inj₁ iy) , refl ;
      (inj₂ iz) → inj₂ (inj₂ iz) , refl}
-- Note: the above could be proven using SL-* properties and associativity of join,
-- but sometimes its just easier to analyse cases

A3-eq : {A : Set} → (x : PA A) → (x ⊕ x) PA≡ x
A3-eq x = join-idem (PA-eval x)

A4-eq : {A : Set} → (x y z : PA A) → ((x ⊕ y) · z) PA≡ ((x · z) ⊕ (y · z))
A4-eq x y z =
  (λ {(inj₁ ix , iz) → inj₁ (ix , iz) , refl ; (inj₂ iy , iz) → inj₂ (iy , iz) , refl}) ,
   λ {(inj₁ (ix , iz)) → (inj₁ ix , iz) , refl ; (inj₂ (iy , iz)) → (inj₂ iy , iz) , refl}
-- The equation for x · (y ⊕ z) also holds, but isn't assumed for PA's and is more difficult
-- to prove as well

A5-eq : {A : Set} → (x y z : PA A) → ((x · y) · z) PA≡ (x · (y · z))
A5-eq x y z = (λ {((ix , iy) , iz) → (ix , (iy , iz)) ,
         Lis-asso (proj₂ (PA-eval x) ix) (proj₂ (PA-eval y) iy) (proj₂ (PA-eval z) iz)}) ,
  λ {(ix , iy , iz) → ((ix , iy) , iz) ,
    sym (Lis-asso (proj₂ (PA-eval x) ix) (proj₂ (PA-eval y) iy) (proj₂ (PA-eval z) iz))}


-- Table II PA specific equations
M1-eq : {A : Set} → (x y : PA A) → (x 𝕀 y) PA≡ ((x 𝕃 y) ⊕ (y 𝕃 x))
M1-eq x y = (λ { (ix , iy , inj₁ l) → (inj₁ (ix , iy , l)) , refl ;
                 (ix , iy , inj₂ r) → (inj₂ (iy , ix , r)) , refl}) ,
             λ { (inj₁ (ix , iy , l)) → (ix , iy , inj₁ l) , refl ;
                 (inj₂ (iy , ix , r)) → (ix , iy , inj₂ r) , refl}

M2-eq : {A : Set} → (a : A) → (x : PA A) → ((at a) 𝕃 x) PA≡ ((at a) · x)
M2-eq a x = (λ { (tt , ix , inj₁ tt) → (tt , ix) , refl ;
                 (tt , ix , inj₂ c) → (tt , ix) ,
                 cong (act a) (Lis-𝕃-con (proj₂ (PA-eval x) ix) c) }) ,
            λ { (tt , ix) → (tt , ix , inj₁ tt) , refl}

M3-eq : {A : Set} → (a : A) → (x y : PA A) → (((at a) · x) 𝕃 y) PA≡ ((at a) · (x 𝕀 y))
M3-eq a x y = (λ {((tt , ix) , iy , c) → (tt , ix , iy , c) , refl}) ,
  λ {(tt , ix , iy , c) → ((tt , ix) , iy , c) , refl}

M4-eq : {A : Set} → (x y z : PA A) → ((x ⊕ y) 𝕃 z) PA≡ ((x 𝕃 z) ⊕ (y 𝕃 z))
M4-eq x y z = (λ {(inj₁ ix , c) → (inj₁ (ix , c)) , refl ;
                  (inj₂ iy , c) → (inj₂ (iy , c)) , refl}) ,
              λ { (inj₁ (ix , c)) → ((inj₁ ix) , c) , refl ;
                  (inj₂ (iy , c)) → ((inj₂ iy) , c) , refl}



-- ACP
-- We do ACP's but by using a symmetric monoid structure on A

data ACP (A : Set) : Set where
  at : A → ACP A
  _⊕_ : ACP A → ACP A → ACP A
  _·_ : ACP A → ACP A → ACP A
  _𝕀_ : ACP A → ACP A → ACP A
  _𝕃_ : ACP A → ACP A → ACP A
  _ℙ_ : ACP A → ACP A → ACP A


Lis-ℙ : {A : Set} → (A → A → A) → Lis A → Lis A → SL (Lis A)
Lis-ℙ p uni r = SL-⊥ (Lis _)
Lis-ℙ p (act a l) uni = SL-⊥ (Lis _)
Lis-ℙ p (act a uni) (act b r) = SL-η (Lis _) (act (p a b) r)
Lis-ℙ p (act a (act a₁ l)) (act b uni) = SL-η (Lis _) (act (p a b) (act a₁ l))
Lis-ℙ p (act a (act a₁ l)) (act b (act b₁ r)) = SL-fun (act (p a b)) (Lis-𝕀 l r)

Lis-ℙ𝕀 : {A : Set} → (A → A → A) → Lis A → Lis A → SL (Lis A)
Lis-ℙ𝕃 : {A : Set} → (A → A → A) → Lis A → Lis A → SL (Lis A)
Lis-ℙ𝕀 m p q = join (Lis-ℙ m p q) (join (Lis-ℙ𝕃 m p q) (Lis-ℙ𝕃 m q p))
Lis-ℙ𝕃 m uni q = SL-η _ q
Lis-ℙ𝕃 m (act a p) q = SL-fun (act a) (Lis-ℙ𝕀 m p q)

Lis-ℙ𝕀* : {A : Set} → (A → A → A) → SL (Lis A) → SL (Lis A) → SL (Lis A)
Lis-ℙ𝕃* : {A : Set} → (A → A → A) → SL (Lis A) → SL (Lis A) → SL (Lis A)
Lis-ℙ* : {A : Set} → (A → A → A) → SL (Lis A) → SL (Lis A) → SL (Lis A)
Lis-ℙ𝕀* m = SL-2* (Lis-ℙ𝕀 m)
Lis-ℙ𝕃* m = SL-2* (Lis-ℙ𝕃 m)
Lis-ℙ* m = SL-2* (Lis-ℙ m)


ACP-eval : {A : Set} → (A → A → A) → SF (ACP A) (Lis A)
ACP-eval m (at a) = SL-η _ (act a uni)
ACP-eval m (P ⊕ P₁) = join (ACP-eval m P) (ACP-eval m P₁)
ACP-eval m (P · P₁) = append* (ACP-eval m P) (ACP-eval m P₁)
ACP-eval m (P 𝕀 P₁) = Lis-ℙ𝕀* m (ACP-eval m P) (ACP-eval m P₁)
ACP-eval m (P 𝕃 P₁) = Lis-ℙ𝕃* m (ACP-eval m P) (ACP-eval m P₁)
ACP-eval m (P ℙ P₁) = Lis-ℙ* m (ACP-eval m P) (ACP-eval m P₁)
