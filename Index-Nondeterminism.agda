module Index-Nondeterminism where

open import Data.Unit
open import Data.Empty
open import Data.Sum renaming (map to map⊎)
open import Data.Nat hiding (_⊔_)
open import Data.Product renaming (map to map×)
open import Relation.Binary.PropositionalEquality hiding ([_])


postulate fun-ext : {X Y : Set} → {f g : X → Y} → ((x : X) → f x ≡ g x) → (f ≡ g)


 
Rel : Set → Set → Set₁
Rel X Y = X → Y → Set

Rel₁ : Set₁ → Set₁ → Set₁
Rel₁ X Y = X → Y → Set

Pow : (X : Set) → Set₁
Pow X = Σ Set λ I → I → X



Pow→ : {X Y : Set} → (X → Y) → (Pow X → Pow Y)
Pow→ f (I , a) = I , (λ i → f (a i))

id : (X : Set) → X → X
id X x = x



-- A notion of function equality
Pow-Γ : {X Y : Set} → Rel X Y → Rel₁ (Pow X) (Pow Y)
Pow-Γ R (I , a) (J , b) = (i : I) → Σ J λ j → R (a i) (b j)

Pow-Γ≡ : (X : Set) → Rel₁ (Pow X) (Pow X)
Pow-Γ≡ X = Pow-Γ (_≡_)

Pow-< : {X Y : Set} → Rel₁ (X → Pow Y) (X → Pow Y)
Pow-< {X} {Y} f g  = (x : X) → Pow-Γ≡ Y (f x) (g x)


Pow-refl : {X Y : Set} → (f : X → Pow Y) → Pow-< f f
Pow-refl f x i = i , refl

Pow-trans : {X Y : Set} → {f g h : X → Pow Y} → Pow-< f g → Pow-< g h → Pow-< f h
Pow-trans f<g g<h x i = proj₁ (g<h x (proj₁ (f<g x i))) ,
  trans (proj₂ (f<g x i)) (proj₂ (g<h x (proj₁ (f<g x i))))

-- Membership
Pow-∈ : (X : Set) → X → Pow X → Set
Pow-∈ X x (I , s) = Σ I λ i → s i ≡ x


-- Kleisli structure

-- Objects are Sets
-- Morphisms are:
PK-Hom : (X Y : Set) → Set₁
PK-Hom X Y = X → Pow Y

PK-≡ : {X Y : Set} → Rel₁ (PK-Hom X Y) (PK-Hom X Y)
PK-≡ f g = Pow-< f g × Pow-< g f


PK-≡-refl : {X Y : Set} → (f : PK-Hom X Y) → PK-≡ f f
PK-≡-refl f = Pow-refl f , Pow-refl f

PK-≡-sym : {X Y : Set} → {f g : PK-Hom X Y} → PK-≡ f g → PK-≡ g f
PK-≡-sym (f<g , g<f) = (g<f , f<g)

PK-≡-trans : {X Y : Set} → {f g h : PK-Hom X Y} → PK-≡ f g → PK-≡ g h → PK-≡ f h
PK-≡-trans f≡g g≡h = Pow-trans (proj₁ f≡g) (proj₁ g≡h)  , Pow-trans (proj₂ g≡h) (proj₂ f≡g)


PK-Id : (X : Set) → PK-Hom X X
PK-Id X x = ⊤ , (λ _ → x)


Pow-κ : (X Y : Set) → (X → Pow Y) → (Pow X → Pow Y)
Pow-κ X Y f (I , a) = (Σ I λ i → proj₁ (f (a i))) ,
  (λ {(i , j) → proj₂ (f (a i)) j})

PK-∘ : {X Y Z : Set} → PK-Hom X Y → PK-Hom Y Z → PK-Hom X Z
PK-∘ {X} {Y} {Z} f g x = Pow-κ Y Z g (f x)

abstract
  PKA-∘ = PK-∘

PK-luni : {X Y : Set} → (f : PK-Hom X Y) → PK-≡ (PK-∘ (PK-Id X) f) f
proj₁ (PK-luni f) x (tt , j) = j , refl
proj₂ (PK-luni f) x j = (tt , j) , refl

PK-runi : {X Y : Set} → (f : PK-Hom X Y) → PK-≡ (PK-∘ f (PK-Id Y)) f
proj₁ (PK-runi f) x (i , tt) = i , refl
proj₂ (PK-runi f) x i = (i , tt) , refl

PK-asso : {X Y Z W : Set} → (f : PK-Hom X Y) → (g : PK-Hom Y Z) → (h : PK-Hom Z W)
  → PK-≡ (PK-∘ (PK-∘ f g) h) (PK-∘ f (PK-∘ g h))
proj₁ (PK-asso f g h) x ((i , j) , k) = (i , (j , k)) , refl
proj₂ (PK-asso f g h) x (i , (j , k)) = ((i , j) , k) , refl



PK-∘-l≡ :  {X Y Z : Set} → (f g : PK-Hom X Y) → (h : PK-Hom Y Z) → PK-≡ f g
  → PK-≡ (PK-∘ f h) (PK-∘ g h)
proj₁ (PK-∘-l≡ f g h (f<g , g<f)) x (i , j) with (f<g x i)
... | k , eq rewrite eq = (k , j) , refl
proj₂ (PK-∘-l≡ f g h (f<g , g<f)) x (i , j) with (g<f x i)
... | k , eq rewrite eq = (k , j) , refl

PK-∘-r≡ :  {X Y Z : Set} → (f : PK-Hom X Y) → (g h : PK-Hom Y Z) → PK-≡ g h
  → PK-≡ (PK-∘ f g) (PK-∘ f h)
proj₁ (PK-∘-r≡ f g h (g<h , h<f)) x (i , j) = (i , (proj₁ (g<h (proj₂ (f x) i) j))) ,
  (proj₂ (g<h (proj₂ (f x) i) j))
proj₂ (PK-∘-r≡ f g h (g<h , h<g)) x (i , j) = (i , proj₁ (h<g (proj₂ (f x) i) j)) ,
  proj₂ (h<g (proj₂ (f x) i) j)

PK-∘-≡ : {X Y Z : Set} → (f f' : PK-Hom X Y) → (g g' : PK-Hom Y Z)
  → PK-≡ f f' → PK-≡ g g' → PK-≡ (PK-∘ f g) (PK-∘ f' g')
PK-∘-≡ f f' g g' f≡f' g≡g' = PK-≡-trans (PK-∘-l≡ f f' g f≡f') (PK-∘-r≡ f' g g' g≡g')





-- Functor of Set into Rel
PK-Fun : {X Y : Set} → (X → Y) → PK-Hom X Y
PK-Fun f x = PK-Id _ (f x)


PK-Fun-id : (X : Set) → PK-≡ (PK-Fun {X} {X} (id X)) (PK-Id X)
proj₁ (PK-Fun-id X) x tt = tt , refl
proj₂ (PK-Fun-id X) x tt = tt , refl

PK-Fun-∘ : {X Y Z : Set} → (f : X → Y) → (g : Y → Z)
  → PK-≡ (PK-Fun (λ x → g (f x))) (PK-∘ (PK-Fun f) (PK-Fun g))
proj₁ (PK-Fun-∘ f g) x tt = (tt , tt) , refl
proj₂ (PK-Fun-∘ f g) x (tt , tt) = tt , refl


-- Reverse map: Dagger for Rel
PK-rev : {X Y : Set} → PK-Hom X Y → PK-Hom Y X
PK-rev {X} {Y} f y = (Σ X λ x → Σ (proj₁ (f x)) λ i → proj₂ (f x) i ≡ y) , proj₁


PK-rr : {X Y : Set} → (f : PK-Hom X Y) → PK-≡ (PK-rev (PK-rev f)) f
proj₁ (PK-rr f) x (y , (.x , i , eq') , refl) = i , (sym eq')
proj₂ (PK-rr f) x i = ((proj₂ (f x) i) , ((x , (i , refl)) , refl)) , refl


PK-rev-id : (X : Set) → PK-≡ (PK-rev (PK-Id X)) (PK-Id X)
proj₁ (PK-rev-id X) x (x' , i , eq) = tt , eq
proj₂ (PK-rev-id X) x i = (x , (tt , refl)) , refl


PK-rev-∘ : {X Y Z : Set} → (f : PK-Hom X Y) → (g : PK-Hom Y Z)
  → PK-≡ (PK-rev (PK-∘ f g)) (PK-∘ (PK-rev g) (PK-rev f))
proj₁ (PK-rev-∘ f g) z (x , (i , j) , g<fxi>j≡z ) =
  (((proj₂ (f x) i) , j , g<fxi>j≡z ) , (x , i , refl)) , refl
proj₂ (PK-rev-∘ f g) z ((.(proj₂ (f x) i) , j , gyj≡z) , x , i , refl) =
  (x , ((i , j) , gyj≡z)) , refl


PK-rev-≡ : {X Y : Set} → (f g : PK-Hom X Y) → PK-≡ f g → PK-≡ (PK-rev g) (PK-rev f)
proj₁ (PK-rev-≡ f g (f<g , g<f)) y (x , i , gxi≡y) =
  (x , ((proj₁ (g<f x i)) , (trans (sym (proj₂ (g<f x i))) gxi≡y))) , refl
proj₂ (PK-rev-≡ f g (f<g , g<f)) y (x , i , fxi≡y) =
  (x , (proj₁ (f<g x i) , trans (sym (proj₂ (f<g x i))) fxi≡y)) , refl




-- Structure of powerdomain
Pow-⊤ : (X : Set) → Pow X
Pow-⊤ X = X , (λ x → x)

Pow-⊥ : (X : Set) → Pow X
Pow-⊥ X = ⊥ , (λ {()})


join : {X : Set} → Pow X → Pow X → Pow X
join (I , l) (J , r) = (I ⊎ J) , (λ { (inj₁ i) → l i ; (inj₂ j) → r j})

join-< : {X : Set} → {a b c d : Pow X}
  → Pow-Γ≡ X a b → Pow-Γ≡ X c d → Pow-Γ≡ X (join a c) (join b d)
join-< a<b c<d (inj₁ i) = (inj₁ (proj₁ (a<b i))) , (proj₂ (a<b i))
join-< a<b c<d (inj₂ j) = (inj₂ (proj₁ (c<d j))) , (proj₂ (c<d j))



PK-join : {X Y : Set} → PK-Hom X Y → PK-Hom X Y → PK-Hom X Y
PK-join f g x = join (f x) (g x)

PK-join-sym : {X Y : Set} → (f g : PK-Hom X Y) → PK-≡ (PK-join f g) (PK-join g f)
proj₁ (PK-join-sym f g) x (inj₁ i) = (inj₂ i) , refl
proj₁ (PK-join-sym f g) x (inj₂ j) = inj₁ j , refl
proj₂ (PK-join-sym f g) x (inj₁ i) = (inj₂ i) , refl
proj₂ (PK-join-sym f g) x (inj₂ j) = inj₁ j , refl

PK-join-l< : {X Y : Set} → (f g h : PK-Hom X Y)
  → Pow-< f g → Pow-< (PK-join f h) (PK-join g h)
PK-join-l< f g h f<g x (inj₁ i) = (inj₁ (proj₁ (f<g x i))) , (proj₂ (f<g x i))
PK-join-l< f g h f<g x (inj₂ j) = (inj₂ j) , refl

PK-join-r< :  {X Y : Set} → (f g h : PK-Hom X Y)
  → Pow-< g h → Pow-< (PK-join f g) (PK-join f h)
PK-join-r< f g h g<h = Pow-trans (proj₁ (PK-join-sym _ _))
  (Pow-trans (PK-join-l< _ _ _ g<h) (proj₁ (PK-join-sym _ _)))

PK-join-≡ : {X Y : Set} → (f g h k : PK-Hom X Y) → PK-≡ f g → PK-≡ h k
  → PK-≡ (PK-join f h) (PK-join g k)
proj₁ (PK-join-≡ f g h k (f<g , g<f) (h<k , k<h)) =
  Pow-trans (PK-join-l< f g h f<g) (PK-join-r< g h k h<k)
proj₂ (PK-join-≡ f g h k (f<g , g<f) (h<k , k<h)) =
  Pow-trans (PK-join-l< g f k g<f) (PK-join-r< f k h k<h)


-- Subcategories
-- Total relations
PK-Total : {X Y : Set} → PK-Hom X Y → Set
PK-Total {X} f = (x : X) → proj₁ (f x)

PK-Total-Id : (X : Set) → PK-Total (PK-Id X)
PK-Total-Id X x = tt

PK-Total-∘ : {X Y Z : Set} → (f : PK-Hom X Y) → (g : PK-Hom Y Z)
  → PK-Total f → PK-Total g → PK-Total (PK-∘ f g)
PK-Total-∘ f g if ig x = (if x) , (ig (proj₂ (f x) (if x)))



-- One or less valued
PK-Onele : {X Y : Set} → PK-Hom X Y → Set
PK-Onele {X} f = (x : X) → (i j : proj₁ (f x)) → proj₂ (f x) i ≡ proj₂ (f x) j

PK-Onele-Id : (X : Set) → PK-Onele (PK-Id X)
PK-Onele-Id X x i j = refl

PK-Onele-∘ : {X Y Z : Set} → (f : PK-Hom X Y) → (g : PK-Hom Y Z)
  → PK-Onele f → PK-Onele g → PK-Onele (PK-∘ f g)
PK-Onele-∘ f g lf lg x (i , j) (i' , j') rewrite lf x i i' = lg (proj₂ (f x) i') j j'



-- Injective
PK-Injec : {X Y : Set} → PK-Hom X Y → Set
PK-Injec {X} f = (x y : X) → (i : proj₁ (f x)) → (j : proj₁ (f y))
  → proj₂ (f x) i ≡ proj₂ (f y) j → x ≡ y

PK-Injec-Id : (X : Set) → PK-Injec (PK-Id X)
PK-Injec-Id X x y i j eq = eq

PK-Injec-∘ : {X Y Z : Set} → (f : PK-Hom X Y) → (g : PK-Hom Y Z)
  → PK-Injec f → PK-Injec g → PK-Injec (PK-∘ f g)
PK-Injec-∘ f g of og x y (i , j) (i' , j') eq =
  of x y i i' (og (proj₂ (f x) i) (proj₂ (f y) i') j j' eq)


-- Surjective
PK-Surje : {X Y : Set} → PK-Hom X Y → Set
PK-Surje {X} {Y} f = (y : Y) → Σ X λ x → Σ (proj₁ (f x)) λ i → proj₂ (f x) i ≡ y

PK-Surje-Id : (X : Set) → PK-Surje (PK-Id X)
PK-Surje-Id X x = x , (tt , refl)

PK-Surje-∘ : {X Y Z : Set} → (f : PK-Hom X Y) → (g : PK-Hom Y Z)
  → PK-Surje f → PK-Surje g → PK-Surje (PK-∘ f g)
PK-Surje-∘ f g sf sg z with sg z
... | y , j , refl with sf y
... | x , i , refl = x , ((i , j) , refl)




-- Reversing swaps properties
PK-rev-Total : {X Y : Set} → (f : PK-Hom X Y) → PK-Total f → PK-Surje (PK-rev f)
PK-rev-Total f tf x = (proj₂ (f x) (tf x)) , ((x , ((tf x) , refl)) , refl)

PK-rev-Surje : {X Y : Set} → (f : PK-Hom X Y) → PK-Surje f → PK-Total (PK-rev f)
PK-rev-Surje f sf y = (proj₁ (sf y)) , ((proj₁ (proj₂ (sf y))) , (proj₂ (proj₂ (sf y))))

PK-rev-Lone : {X Y : Set} → (f : PK-Hom X Y) → PK-Onele f → PK-Injec (PK-rev f)
PK-rev-Lone f of x y (x₀ , i , eq₀) (.x₀ , j , eq₁) refl =
  trans (sym eq₀) (trans (of x₀ i j) eq₁)

PK-rev-Injec : {X Y : Set} → (f : PK-Hom X Y) → PK-Injec f → PK-Onele (PK-rev f)
PK-rev-Injec f if y (x , i , eq) (x' , j , eq') = if x x' i j (trans eq (sym eq'))



-- Set is the subcategory of Onele and Total relations
PK-Fun-Onele : {X Y : Set} → (f : X → Y) → PK-Onele (PK-Fun f)
PK-Fun-Onele f x i j = refl

PK-Fun-Total : {X Y : Set} → (f : X → Y) → PK-Total (PK-Fun f)
PK-Fun-Total f x = tt

--Note: Since Set's notion of equality is the eternal equivalence of Agda,
--PK-Fun trivially preserves equivalence


--Showing that the Functor PK-Fun is bijective on morphisms (function extensionality)
PK-Fun-inv≡ : {X Y : Set} → (f g : X → Y) → PK-≡ (PK-Fun f) (PK-Fun g) → (f ≡ g)
PK-Fun-inv≡ f g (f<g , g<f) = fun-ext λ x → proj₂ (f<g x tt)

PK-Fun-inv : {X Y : Set} → (f : PK-Hom X Y) → PK-Onele f → PK-Total f
  → Σ (X → Y) λ h → PK-≡ (PK-Fun h) f
proj₁ (PK-Fun-inv f fone ftot) x = proj₂ (f x) (ftot x)
proj₂ (PK-Fun-inv f fone ftot) = (λ x i → (ftot x) , refl) ,
                                  λ x i → tt , (fone x i (ftot x))

