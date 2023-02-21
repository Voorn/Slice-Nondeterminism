module Small-Slice.Substructure where

-- standard library
open import Data.Unit
open import Data.Empty
open import Data.Sum 
open import Data.Nat
open import Data.Product 

open import Relation.Binary.Core
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.Structures
open import Relation.Binary.Definitions

-- local
open import Small-Slice.Univ
open import Small-Slice.ND-functions


-- E-category of external relations
ERel : (X Y : Set) → Set₁
ERel X Y = X → Y → Set

ERel-id : (X : Set) → ERel X X
ERel-id X x y = x ≡ y

ERel-∘ : {X Y Z : Set} → ERel Y Z → ERel X Y → ERel X Z
ERel-∘ S R x z = Σ _ λ y → R x y × S y z

ERel-≡ : {X Y : Set} → (ERel X Y) → (ERel X Y) → Set
ERel-≡ R S = (x : _) → (y : _) → ((R x y → S x y) × (S x y → R x y))


ERel-≡-prop : (X Y : Set) → IsEquivalence (ERel-≡ {X} {Y}) 
ERel-≡-prop X Y =
  record {
    refl = λ x y → (λ xRy → xRy) , λ yRx → yRx ;
    sym = λ R≡S x y → (λ xSy → proj₂ (R≡S x y) xSy) , λ xRy → proj₁ (R≡S x y) xRy ;
    trans = λ R≡S S≡U x y → (λ xRy → proj₁ (S≡U x y) (proj₁ (R≡S x y) xRy)) ,
                            λ xUy → proj₂ (R≡S x y) (proj₂ (S≡U x y) xUy)
  }

ERel-luni : {X Y : Set} → (R : ERel X Y) → ERel-≡ (ERel-∘ R (ERel-id X)) R
proj₁ (ERel-luni R x y) (.x , refl , xRy) = xRy
proj₂ (ERel-luni R x y) xRy = x , (refl , xRy)

ERel-runi : {X Y : Set} → (R : ERel X Y) → ERel-≡ (ERel-∘ (ERel-id Y) R) R
proj₁ (ERel-runi R x y) (.y , xRy , refl) = xRy
proj₂ (ERel-runi R x y) xRy = y , (xRy , refl)

ERel-asso : {X Y Z W : Set} → (R : ERel X Y) → (S : ERel Y Z) → (U : ERel Z W)
  → ERel-≡ (ERel-∘ (ERel-∘ U S) R) (ERel-∘ U (ERel-∘ S R))
proj₁ (ERel-asso R S U x w) (y , xRy , z , ySz , zUw) = z , (y , xRy , ySz) , zUw
proj₂ (ERel-asso R S U x w) (z , (y , xRy , ySz) , zUw) = y , xRy , z , ySz , zUw


-- Functor of E-categories
𝕌→Rel-Hom : {X Y : Set} → 𝕌Hom X Y → ERel X Y
𝕌→Rel-Hom f x y = Σ (𝕌S (proj₁ (f x))) (λ i → proj₂ (f x) i ≡ y)

𝕌→Rel-id : (X : Set) → ERel-≡ (𝕌→Rel-Hom (𝕌Hom-id X)) (ERel-id X)
𝕌→Rel-id X x x' = (λ p → proj₂ p) , λ p → tt , p

𝕌→Rel-∘ : {X Y Z : Set} → (f : 𝕌Hom X Y) → (g : 𝕌Hom Y Z)
  → ERel-≡ (𝕌→Rel-Hom (𝕌Hom-∘ g f)) (ERel-∘ (𝕌→Rel-Hom g) (𝕌→Rel-Hom f))
proj₁ (𝕌→Rel-∘ f g x .(proj₂ (g (proj₂ (f x) i)) j)) ((i , j) , refl)
  = (proj₂ (f x) i) , ((i , refl) , (j , refl))
proj₂ (𝕌→Rel-∘ f g x .(proj₂ (g (proj₂ (f x) i)) j))
  (.(proj₂ (f x) i) , (i , refl) , j , refl)
  = (i , j) , refl


-- Total relations
𝕌-Total : {X Y : Set} → 𝕌Hom X Y → Set
𝕌-Total {X} f = (x : X) → 𝕌S (proj₁ (f x))

𝕌-Total-id : (X : Set) → 𝕌-Total (𝕌Hom-id X)
𝕌-Total-id X x = tt

𝕌-Total-∘ : {X Y Z : Set} → (f : 𝕌Hom X Y) → (g : 𝕌Hom Y Z)
  → 𝕌-Total f → 𝕌-Total g → 𝕌-Total (𝕌Hom-∘ g f)
𝕌-Total-∘ f g f-tot g-tot x = (f-tot x) , (g-tot (proj₂ (f x) (f-tot x)))

𝕌-Total-≡ : {X Y : Set} → (f g : 𝕌Hom X Y) → 𝕌Hom-≡ f g → 𝕌-Total f → 𝕌-Total g
𝕌-Total-≡ f g (f<g , g<f) f-tot x = proj₁ (f<g x (f-tot x))


-- Deterministic (single-valued)
𝕌-Deter : {X Y : Set} → 𝕌Hom X Y → Set
𝕌-Deter {X} f = (x : X) → (i j : 𝕌S (proj₁ (f x))) → proj₂ (f x) i ≡ proj₂ (f x) j

𝕌-Deter-id : (X : Set) → 𝕌-Deter (𝕌Hom-id X)
𝕌-Deter-id X x tt tt = refl

𝕌-Deter-∘ : {X Y Z : Set} → (f : 𝕌Hom X Y) → (g : 𝕌Hom Y Z)
  → 𝕌-Deter f → 𝕌-Deter g → 𝕌-Deter (𝕌Hom-∘ g f)
𝕌-Deter-∘ f g f-det g-det x (i , j) (i' , j') rewrite f-det x i i' = g-det (proj₂ (f x) i') j j'

𝕌-Deter-≡ : {X Y : Set} → (f g : 𝕌Hom X Y) → 𝕌Hom-≡ f g → 𝕌-Deter f → 𝕌-Deter g
𝕌-Deter-≡ f g (f<g , g<f) f-det x i j = trans (proj₂ (g<f x i))
  (trans (f-det x (proj₁ (g<f x i)) (proj₁ (g<f x j))) (sym (proj₂ (g<f x j))))


-- Injective (modest)
𝕌-Injec : {X Y : Set} → 𝕌Hom X Y → Set
𝕌-Injec {X} f = (x y : X) → (i : 𝕌S (proj₁ (f x))) → (j : 𝕌S (proj₁ (f y)))
  → proj₂ (f x) i ≡ proj₂ (f y) j → x ≡ y

𝕌-Injec-id : (X : Set) → 𝕌-Injec (𝕌Hom-id X)
𝕌-Injec-id X x .x tt tt refl = refl

𝕌-Injec-∘ : {X Y Z : Set} → (f : 𝕌Hom X Y) → (g : 𝕌Hom Y Z)
  → 𝕌-Injec f → 𝕌-Injec g → 𝕌-Injec (𝕌Hom-∘ g f)
𝕌-Injec-∘ f g f-inj g-inj x y (i , j) (i' , j') eq = f-inj x y i i'
  (g-inj (proj₂ (f x) i) (proj₂ (f y) i') j j' eq)

𝕌-Injec-≡ : {X Y : Set} → (f g : 𝕌Hom X Y) → 𝕌Hom-≡ f g → 𝕌-Injec f → 𝕌-Injec g
𝕌-Injec-≡ f g (f<g , g<f) f-inj x x' i i' eq = f-inj x x' (proj₁ (g<f x i)) (proj₁ (g<f x' i'))
  (trans (sym (proj₂ (g<f x i))) (trans eq (proj₂ (g<f x' i'))))


-- Surjective (covering)
𝕌-Surje : {X Y : Set} → 𝕌Hom X Y → Set
𝕌-Surje {X} {Y} f = (y : Y) → Σ X λ x → 𝕌SL-∈ y (f x)

𝕌-Surje-id : (X : Set) → 𝕌-Surje (𝕌Hom-id X)
𝕌-Surje-id X x = x , (tt , refl)

𝕌-Surje-∘ : {X Y Z : Set} → (f : 𝕌Hom X Y) → (g : 𝕌Hom Y Z)
  → 𝕌-Surje f → 𝕌-Surje g → 𝕌-Surje (𝕌Hom-∘ g f)
𝕌-Surje-∘ f g f-sur g-sur z with g-sur z
...| y , j , refl with f-sur y
...| x , i , refl = x , ((i , j) , refl)

𝕌-Surje-≡ : {X Y : Set} → (f g : 𝕌Hom X Y) → 𝕌Hom-≡ f g → 𝕌-Surje f → 𝕌-Surje g
𝕌-Surje-≡ f g (f<g , g<f) f-sur y with f-sur y
... | (x , (i , eq)) = x , (proj₁ (f<g x i) , trans (sym (proj₂ (f<g x i))) eq)


-- Comparing with set
Set-Total : {X Y : Set} → (f : X → Y) → 𝕌-Total (𝕌Hom-fun f)
Set-Total f x = tt

Set-Deter : {X Y : Set} → (f : X → Y) → 𝕌-Deter (𝕌Hom-fun f)
Set-Deter f x tt tt = refl


Total→Set : {X Y : Set} → (f : 𝕌Hom X Y) → (𝕌-Total f) → (X → Y)
Total→Set f f-tot x = proj₂ (f x) (f-tot x)

𝕊Hom-≡ : {X Y : Set} → (f g : X → Y) → Set
𝕊Hom-≡ {X} f g = (x : X) → f x ≡ g x

𝕊→𝕌→𝕊 : {X Y : Set} → (f : X → Y) → 𝕊Hom-≡ (Total→Set (𝕌Hom-fun f) (Set-Total f)) f
𝕊→𝕌→𝕊 f x = refl

𝕌→𝕊→𝕌 : {X Y : Set} → (f : 𝕌Hom X Y) → (f-tot : 𝕌-Total f) → 𝕌-Deter f
  → 𝕌Hom-≡ (𝕌Hom-fun (Total→Set f f-tot)) f
proj₁ (𝕌→𝕊→𝕌 f f-tot f-det) x tt = (f-tot x) , refl
proj₂ (𝕌→𝕊→𝕌 f f-tot f-det) x i = tt , (f-det x i (f-tot x))



-- Substructure of dagger-able morphisms

-- semi dagger checks if: f† ⊂ g
𝕌-is-†' : {X Y : Set} → 𝕌Hom X Y → 𝕌Hom Y X → Set
𝕌-is-†' {X} {Y} f g = (x : X) → (i : (𝕌S (proj₁ (f x)))) → 𝕌SL-∈ x (g (proj₂ (f x) i))

𝕌-is-†'-Id : {X : Set} → 𝕌-is-†' (𝕌Hom-id X) (𝕌Hom-id X)
𝕌-is-†'-Id x tt = tt , refl

𝕌-is-†'-∘ : {X Y Z : Set} → (f : 𝕌Hom X Y) → (f† : 𝕌Hom Y X) → (g : 𝕌Hom Y Z) → (g† : 𝕌Hom Z Y)
  → 𝕌-is-†' f f† → 𝕌-is-†' g g† → 𝕌-is-†' (𝕌Hom-∘ g f) (𝕌Hom-∘ f† g†)
proj₁ (proj₁ (𝕌-is-†'-∘ f f† g g† f-prop g-prop x (i , j))) = proj₁ (g-prop (proj₂ (f x) i) j)
proj₂ (proj₁ (𝕌-is-†'-∘ f f† g g† f-prop g-prop x (i , j)))
  rewrite proj₂ (g-prop (proj₂ (f x) i) j) = proj₁ (f-prop x i)
proj₂ (𝕌-is-†'-∘ f f† g g† f-prop g-prop x (i , j))
  rewrite proj₂ (g-prop (proj₂ (f x) i) j) = proj₂ (f-prop x i)


𝕌-†'-⊂ : {X Y : Set} → (f f' : 𝕌Hom X Y) → (f† : 𝕌Hom Y X) → 𝕌-is-†' f f† → 𝕌-is-†' f† f'
  → 𝕌Hom-⊂ f f'
𝕌-†'-⊂ f f' f† f-† †-f' x i with f-† x i
... | j , eq with †-f' (proj₂ (f x) i) j
... | k , eq' rewrite eq = k , (sym eq')

𝕌-is-†'-r≡ : {X Y : Set} → (f : 𝕌Hom X Y) → (g h : 𝕌Hom Y X) → 𝕌Hom-≡ g h → 𝕌-is-†' f g → 𝕌-is-†' f h
𝕌-is-†'-r≡ f g h (g<h , h<g) f†g x i with f†g x i
... | j , eq = proj₁ (g<h (proj₂ (f x) i) j) , trans (sym (proj₂ (g<h (proj₂ (f x) i) j))) eq

𝕌-is-†'-l≡ : {X Y : Set} → (f g : 𝕌Hom X Y) → (h : 𝕌Hom Y X) → 𝕌Hom-≡ f g → 𝕌-is-†' f h → 𝕌-is-†' g h
𝕌-is-†'-l≡ f g h (f<g , g<f) f†h x i rewrite (proj₂ (g<f x i)) = f†h x (proj₁ (g<f x i))

-- is dagger
𝕌-is-† : {X Y : Set} → 𝕌Hom X Y → 𝕌Hom Y X → Set
𝕌-is-† f g = 𝕌-is-†' f g × 𝕌-is-†' g f


-- daggerable
𝕌-Dagger : {X Y : Set} → 𝕌Hom X Y → Set
𝕌-Dagger {X} {Y} f = Σ (𝕌Hom Y X) λ f† → 𝕌-is-† f f†

𝕌-Dagger-id : (X : Set) → 𝕌-Dagger (𝕌Hom-id X)
𝕌-Dagger-id X = (𝕌Hom-id X) , (𝕌-is-†'-Id , 𝕌-is-†'-Id)

𝕌-Dagger-∘ : {X Y Z : Set} → (f : 𝕌Hom X Y) → (g : 𝕌Hom Y Z)
  → 𝕌-Dagger f → 𝕌-Dagger g → 𝕌-Dagger (𝕌Hom-∘ g f)
𝕌-Dagger-∘ f g (f† , fr , fl) (g† , gr , gl) = (𝕌Hom-∘ f† g†) ,
  ((𝕌-is-†'-∘ f f† g g† fr gr) , (𝕌-is-†'-∘ g† g f† f gl fl)) 

𝕌-Dagger-≡ : {X Y : Set} → (f g : 𝕌Hom X Y) → 𝕌Hom-≡ f g → (𝕌-Dagger f) → 𝕌-Dagger g 
𝕌-Dagger-≡ f g f≡g (h , f†h , h†f) = h , (𝕌-is-†'-l≡ f g h f≡g f†h ,
  𝕌-is-†'-r≡ h f g f≡g h†f)


-- bijections are daggerable
𝕊-Injec : {X Y : Set} → (X → Y) → Set
𝕊-Injec {X} f = (x x' : X) → (f x ≡ f x') → (x ≡ x')

𝕊-Surje : {X Y : Set} → (X → Y) → Set
𝕊-Surje {X} {Y} f = (y : Y) → Σ X λ x → (f x ≡ y)



𝕌-Bij-Dagger : {X Y : Set} → (f : X → Y) → 𝕊-Injec f → 𝕊-Surje f → 𝕌-Dagger (𝕌Hom-fun f)
𝕌-Bij-Dagger f f-inj f-sur = (λ y → 𝕌SL-η (proj₁ (f-sur y))) ,
  (λ x i → tt , (f-inj (proj₁ (f-sur (f x))) x (proj₂ (f-sur (proj₂ (𝕌Hom-fun f x) i))))) ,
  λ y i → tt , proj₂ (f-sur y)

-- There will be dagger consequences! 
𝕌-dagger-Total-Surje : {X Y : Set} → (f : 𝕌Hom X Y) → (g : 𝕌Hom Y X) → 𝕌-is-† f g
  → 𝕌-Total f → 𝕌-Surje g
𝕌-dagger-Total-Surje f g (f†g , g†f) f-tot x = proj₂ (f x) (f-tot x) , f†g x (f-tot x)

𝕌-dagger-Surje-Total : {X Y : Set} → (f : 𝕌Hom X Y) → (g : 𝕌Hom Y X) → 𝕌-is-† f g
  → 𝕌-Surje f → 𝕌-Total g
𝕌-dagger-Surje-Total f g (f†g , g†f) f-sur y with f-sur y
... | x , i , refl = proj₁ (f†g x i)

𝕌-dagger-Deter-Injec : {X Y : Set} → (f : 𝕌Hom X Y) → (g : 𝕌Hom Y X) → 𝕌-is-† f g
  → 𝕌-Deter f → 𝕌-Injec g
𝕌-dagger-Deter-Injec f g (f†g , g†f) f-det y y' j j' eq with (g†f y j , g†f y' j')
... | ((i , eq₀) , (i' , eq₁)) rewrite eq = trans (sym eq₀) (trans (f-det (proj₂ (g y') j') i i') eq₁)

𝕌-dagger-Injec-Deter : {X Y : Set} → (f : 𝕌Hom X Y) → (g : 𝕌Hom Y X) → 𝕌-is-† f g
  → 𝕌-Injec f → 𝕌-Deter g
𝕌-dagger-Injec-Deter f g (f†g , g†f) f-inj y j j' with (g†f y j , g†f y j')
... | ((i , eq₀) , (i' , eq₁)) = f-inj (proj₂ (g y) j) (proj₂ (g y) j') i i' (trans eq₀ (sym eq₁))

-- inverses
𝕌-dagger-post : {X Y : Set} → (f : 𝕌Hom X Y) → (g : 𝕌Hom Y X) → 𝕌-is-† f g
  → 𝕌-Total f → 𝕌-Injec f → 𝕌Hom-≡ (𝕌Hom-∘ g f) (𝕌Hom-id X) 
proj₁ (𝕌-dagger-post f g (f†g , g†f) f-tot f-inj) x (i , j) with g†f (proj₂ (f x) i) j
... | k , eq = tt , f-inj (proj₂ (g (proj₂ (f x) i)) j) x k i eq
proj₂ (𝕌-dagger-post f g (f†g , g†f) f-tot f-inj) x tt with f†g x (f-tot x)
... | k , eq = ((f-tot x) , k) , sym eq

𝕌-dagger-pre : {X Y : Set} → (f : 𝕌Hom X Y) → (g : 𝕌Hom Y X) → 𝕌-is-† f g
  → 𝕌-Surje f → 𝕌-Deter f → 𝕌Hom-≡ (𝕌Hom-∘ f g) (𝕌Hom-id Y) 
𝕌-dagger-pre f g (f†g , g†f) f-sur f-det = 𝕌-dagger-post g f (g†f , f†g)
  (𝕌-dagger-Surje-Total f g (f†g , g†f) f-sur) (𝕌-dagger-Deter-Injec f g (f†g , g†f) f-det)


𝕌-inv-Total : {X Y : Set} → (f : 𝕌Hom X Y) → (g : 𝕌Hom Y X) → (𝕌Hom-⊂ (𝕌Hom-id X) (𝕌Hom-∘ g f)) → 𝕌-Total f
𝕌-inv-Total f g id⊂fg x = proj₁ (proj₁ (id⊂fg x tt))

-- epis and mono's

𝕌-epi : {X Y : Set} → 𝕌Hom X Y → Set₁
𝕌-epi {X} {Y} f = {Z : Set} → (g₀ g₁ : 𝕌Hom Y Z) → 𝕌Hom-⊂ (𝕌Hom-∘ g₀ f) (𝕌Hom-∘ g₁ f) → 𝕌Hom-⊂ g₀ g₁

𝕌-epi-con : {X Y Z : Set} → (f : 𝕌Hom X Y) → (𝕌-Surje f) → (𝕌-Deter f) → 𝕌-epi f
𝕌-epi-con f f-sur f-det g₀ g₁ fg₀⊂fg₁ y i with f-sur y
... | x , j , refl with fg₀⊂fg₁ x (j , i)
... | (j' , i') , eq with f-det x j j'
... | eq' rewrite eq' = i' , eq

𝕌-mono : {X Y : Set} → 𝕌Hom X Y → Set₁
𝕌-mono {X} {Y} f = {Z : Set} → (g₀ g₁ : 𝕌Hom Z X) → 𝕌Hom-⊂  (𝕌Hom-∘ f g₀) (𝕌Hom-∘ f g₁) → 𝕌Hom-⊂ g₀ g₁

𝕌-mono-con : {X Y : Set} → (f : 𝕌Hom X Y) → (𝕌-Injec f) → (𝕌-Total f) → 𝕌-mono f
𝕌-mono-con f f-inj f-tot g₀ g₁ g₀f⊂g₁f z i with f-tot (proj₂ (g₀ z) i)
... | j with g₀f⊂g₁f z (i , j)
... | (i' , j') , eq with f-inj (proj₂ (g₀ z) i) (proj₂ (g₁ z) i') j j' eq
... | eq' rewrite eq' = i' , refl
