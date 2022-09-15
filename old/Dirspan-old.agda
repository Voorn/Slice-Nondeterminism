module Dirspan where

open import Data.Unit
open import Data.Empty
open import Data.Sum renaming (map to map⊎)
open import Data.Nat hiding (_⊔_)
open import Data.Product renaming (map to map×)
open import Relation.Binary.PropositionalEquality hiding ([_])

open import Slice

postulate fun-ext : {X Y : Set} → {f g : X → Y} → ((x : X) → f x ≡ g x) → (f ≡ g)

postulate dep-ext : {X : Set} → {F : X → Set} → {f g : (x : X) → F x} → ((x : X) → f x ≡ g x) → f ≡ g


-- Bicategory:

-- Objects sets
DS-Obj = Set


-- Morphism, equivalence classes of functions:
DS→ : (X Y : Set) → Set₁
DS→ X Y = X → SL Y

-- 2-morphisms: a function
DS⇒ : {X Y : Set} → DS→ X Y → DS→ X Y → Set
DS⇒ {X} {Y} f g = (x : X) → proj₁ (f x) → proj₁ (g x)

-- such that
DS⇒prop : {X Y : Set} → (f g : DS→ X Y) → DS⇒ f g → Set
DS⇒prop {X} {Y} f g α = (x : X) → (i : proj₁ (f x))
  → proj₂ (f x) i ≡ proj₂ (g x) (α x i) 


-- the identities
DS-id : (X : Set) → DS→ X X
DS-id X x = ⊤ , (λ i → x)


DS-ID : {X Y : Set} → (f : DS→ X Y) → DS⇒ f f 
DS-ID f x i = i

DS-ID-prop : {X Y : Set} → (f : DS→ X Y) → DS⇒prop f f (DS-ID f)
DS-ID-prop f x i = refl



-- compositions
DS-∘ : {X Y Z : Set} → DS→ X Y → DS→ Y Z → DS→ X Z
DS-∘ f g x = (Σ (proj₁ (f x)) (λ i → proj₁ (g (proj₂ (f x) i)))) ,
             λ {(i , j) → proj₂ (g (proj₂ (f x) i)) j}


DS-● : {X Y : Set} → (f g h : DS→ X Y) → DS⇒ f g → DS⇒ g h → DS⇒ f h
DS-● f g h α β x i = β x (α x i)

DS-●-prop : {X Y : Set} → (f g h : DS→ X Y)
  → (α : DS⇒ f g) → (DS⇒prop f g α) → (β : DS⇒ g h) → (DS⇒prop g h β)
  → DS⇒prop f h (DS-● f g h α β)
DS-●-prop f g h α αp β βp x i = trans (αp x i) (βp x (α x i))


-- isomorphism: if the underlying map is a bijection, its an isomorphism
bijection : {X Y : Set} → (X → Y) → Set
bijection {X} {Y} f = ((x x' : X) → f x ≡ f x' → x ≡ x') × ((y : Y) → Σ X λ x → f x ≡ y)

DS⇒bij : {X Y : Set} → (f g : DS→ X Y) → DS⇒ f g → Set
DS⇒bij {X} {Y} f g α = (x : X) → bijection (α x)

DS⇒inv : {X Y : Set} → (f g : DS→ X Y) → (α : DS⇒ f g) → DS⇒bij f g α → DS⇒ g f 
DS⇒inv f g α αb x i = proj₁ (proj₂ (αb x) i)

DS⇒inv-prop : {X Y : Set} → (f g : DS→ X Y) → (α : DS⇒ f g) → (DS⇒prop f g α)
  → (αb : DS⇒bij f g α) → DS⇒prop g f (DS⇒inv f g α αb)
DS⇒inv-prop f g α αp αb x i = sym (trans (αp x (proj₁ (proj₂ (αb x) i)))
  (cong (proj₂ (g x)) (proj₂ (proj₂ (αb x) i)))) 

DS⇒inv-1 : {X Y : Set} → (f g : DS→ X Y) → (α : DS⇒ f g)
  → (αb : DS⇒bij f g α) → DS-● f g f α (DS⇒inv f g α αb) ≡ DS-ID f
DS⇒inv-1 f g α αb =  dep-ext (λ x → fun-ext (λ i →
  proj₁ (αb x) (proj₁ (proj₂ (αb x) (α x i))) i (proj₂ (proj₂ (αb x) (α x i)))))

DS⇒inv-2 : {X Y : Set} → (f g : DS→ X Y) → (α : DS⇒ f g)
  → (αb : DS⇒bij f g α) → DS-● g f g (DS⇒inv f g α αb) α ≡ DS-ID g
DS⇒inv-2 f g α αb = dep-ext (λ x → fun-ext (λ i → proj₂ (proj₂ (αb x) i)))



-- category on morphisms
DS-LUNI : {X Y : Set} → (f g : DS→ X Y) → (α : DS⇒ f g) → DS-● f f g (DS-ID f) α ≡ α
DS-LUNI f g α = refl

DS-RUNI : {X Y : Set} → (f g : DS→ X Y) → (α : DS⇒ f g) → DS-● f g g α (DS-ID g) ≡ α
DS-RUNI f g α = refl

DS-ASSO : {X Y : Set} → (f g h k : DS→ X Y)
  → (α : DS⇒ f g) → (β : DS⇒ g h) → (γ : DS⇒ h k)
  → DS-● f h k (DS-● f g h α β) γ ≡ DS-● f g k α (DS-● g h k β γ)
DS-ASSO f g h k α β γ = refl


-- whiskering
open import transport

DS-lwhis : {X Y Z : Set} → (f g : DS→ X Y) → (h : DS→ Y Z) → (α : DS⇒ f g)
  → (DS⇒prop f g α) → DS⇒ (DS-∘ f h) (DS-∘ g h)
DS-lwhis f g h α αp x (i , j) = (α x i) ,
  transp (λ u → proj₁ (h u)) (proj₂ (f x) i) (proj₂ (g x) (α x i)) (αp x i) j

DS-lwhis-prop : {X Y Z : Set} → (f g : DS→ X Y) → (h : DS→ Y Z) → (α : DS⇒ f g)
   → (αp : DS⇒prop f g α) → DS⇒prop (DS-∘ f h) (DS-∘ g h) (DS-lwhis f g h α αp)
DS-lwhis-prop f g h α αp x (i , j) rewrite (αp x i) = refl

DS-lwhis-ID : {X Y Z : Set} → (f : DS→ X Y) → (g : DS→ Y Z) →
  DS-lwhis f f g (DS-ID f) (DS-ID-prop f) ≡ DS-ID (DS-∘ f g)
DS-lwhis-ID f g = refl

DS-lwhis-∘ : {X Y Z : Set} → (f g h : DS→ X Y) → (k : DS→ Y Z)
  → (α : DS⇒ f g) → (αp : DS⇒prop f g α) → (β : DS⇒ g h) → (βp : DS⇒prop g h β)
  → DS-lwhis f h k (DS-● f g h α β) (DS-●-prop f g h α αp β βp)
    ≡ DS-● (DS-∘ f k) (DS-∘ g k) (DS-∘ h k) (DS-lwhis f g k α αp) (DS-lwhis g h k β βp)
DS-lwhis-∘ f g h k α αp β βp = dep-ext (λ x' → fun-ext (λ i' → cong (λ u → β x' (α x' (proj₁ i')) , u)
    (trans
       (transp-comp (λ u → proj₁ (k u)) (proj₂ (f x') (proj₁ i'))
       (proj₂ (g x') (α x' (proj₁ i')))
        (proj₂ (h x') (β x' (α x' (proj₁ i')))) (αp x' (proj₁ i'))
        (βp x' (α x' (proj₁ i'))) (proj₂ i'))
       refl)))


DS-rwhis : {X Y Z : Set} → (f : DS→ X Y) → (g h : DS→ Y Z) → (α : DS⇒ g h)
  → (DS⇒prop g h α) → DS⇒ (DS-∘ f g) (DS-∘ f h)
DS-rwhis f g h α αp x (i , j) = i , (α (proj₂ (f x) i) j)

DS-rwhis-prop : {X Y Z : Set} → (f : DS→ X Y) → (g h : DS→ Y Z) → (α : DS⇒ g h)
   → (αp : DS⇒prop g h α) → DS⇒prop (DS-∘ f g) (DS-∘ f h) (DS-rwhis f g h α αp)
DS-rwhis-prop f g h α αp x (i , j) = αp (proj₂ (f x) i) j

DS-rwhis-ID : {X Y Z : Set} → (f : DS→ X Y) → (g : DS→ Y Z) →
  DS-rwhis f g g (DS-ID g) (DS-ID-prop g) ≡ DS-ID (DS-∘ f g)
DS-rwhis-ID f g = refl

DS-rwhis-∘ : {X Y Z : Set} → (f : DS→ X Y) → (g h k : DS→ Y Z)
  → (α : DS⇒ g h) → (αp : DS⇒prop g h α) → (β : DS⇒ h k) → (βp : DS⇒prop h k β)
  → DS-rwhis f g k (DS-● g h k α β) (DS-●-prop g h k α αp β βp)
    ≡ DS-● (DS-∘ f g) (DS-∘ f h) (DS-∘ f k) (DS-rwhis f g h α αp) (DS-rwhis f h k β βp)
DS-rwhis-∘ f g h k α αp β βp = refl


-- weak category on sets

-- Left unitor natural isomorphism
DS-luni : {X Y : Set} → (f : DS→ X Y) → DS⇒ (DS-∘ (DS-id X) f) f
DS-luni f x  (tt , i) = i

DS-luni-prop : {X Y : Set} → (f : DS→ X Y) → DS⇒prop (DS-∘ (DS-id X) f) f (DS-luni f)
DS-luni-prop f x (tt , i) = refl

DS-luni-nat : {X Y : Set} → (f g : DS→ X Y) → (α : DS⇒ f g) → (αp : DS⇒prop f g α)
  → DS-● (DS-∘ (DS-id X) f) (DS-∘ (DS-id X) g) g (DS-rwhis (DS-id X) f g α αp) (DS-luni g)
  ≡ DS-● (DS-∘ (DS-id X) f) f g (DS-luni f) α
DS-luni-nat f g α αp = refl

DS-luni-bij : {X Y : Set} → (f : DS→ X Y) → DS⇒bij (DS-∘ (DS-id X) f) f (DS-luni f)
DS-luni-bij f x = (λ {i .i refl → refl}) , λ y → (tt , y) , refl

--DS-iluni : {X Y : Set} → (f : DS→ X Y) → DS⇒ f (DS-∘ (DS-id X) f)
--DS-iluni f x i = tt , i

--DS-iluni-prop : {X Y : Set} → (f : DS→ X Y) → DS⇒prop (DS-∘ (DS-id X) f) f (DS-luni f)
--DS-iluni-prop f x (tt , i) = refl



DS-runi : {X Y : Set} → (f : DS→ X Y) → DS⇒ (DS-∘ f (DS-id Y)) f
DS-runi f x (i , tt) = i

DS-runi-prop : {X Y : Set} → (f : DS→ X Y) → DS⇒prop (DS-∘ f (DS-id Y)) f (DS-runi f)
DS-runi-prop f x (i , tt) = refl

DS-runi-nat : {X Y : Set} → (f g : DS→ X Y) → (α : DS⇒ f g) → (αp : DS⇒prop f g α)
  → DS-● (DS-∘ f (DS-id Y)) (DS-∘ g (DS-id Y)) g (DS-lwhis f g (DS-id Y) α αp) (DS-runi g)
  ≡ DS-● (DS-∘ f (DS-id Y)) f g (DS-runi f) α
DS-runi-nat f g α αp = refl

DS-runi-bij : {X Y : Set} → (f : DS→ X Y) → DS⇒bij (DS-∘ f (DS-id Y)) f (DS-runi f)
DS-runi-bij f x = (λ {i .i refl → refl}) , λ y → (y , tt) , refl



DS-asso : {X Y Z W : Set} → (f : DS→ X Y) → (g : DS→ Y Z) → (h : DS→ Z W)
  → DS⇒ (DS-∘ (DS-∘ f g) h) (DS-∘ f (DS-∘ g h))
DS-asso f g h x ((i , j) , k) = i , j , k

DS-asso-prop : {X Y Z W : Set} → (f : DS→ X Y) → (g : DS→ Y Z) → (h : DS→ Z W)
  → DS⇒prop (DS-∘ (DS-∘ f g) h) (DS-∘ f (DS-∘ g h)) (DS-asso f g h)
DS-asso-prop f g h x ((i , j) , k) = refl

DS-asso-nat-1 : {X Y Z W : Set} → (f f' : DS→ X Y) → (g : DS→ Y Z) → (h : DS→ Z W)
  → (α : DS⇒ f f') → (αp : DS⇒prop f f' α)
  → (x : X) → (i : proj₁ (DS-∘ (DS-∘ f g) h x))
  → DS-● (DS-∘ (DS-∘ f g) h) (DS-∘ (DS-∘ f' g) h) (DS-∘ f' (DS-∘ g h))
  (DS-lwhis (DS-∘ f g) (DS-∘ f' g) h (DS-lwhis f f' g α αp) (DS-lwhis-prop f f' g α αp))
  (DS-asso f' g h) x i
  ≡ DS-● (DS-∘ (DS-∘ f g) h) (DS-∘ f (DS-∘ g h)) (DS-∘ f' (DS-∘ g h))
  (DS-asso f g h) (DS-lwhis f f' (DS-∘ g h) α αp) x i
DS-asso-nat-1 f f' g h α αp x i = {!!}


-- whiskering away
