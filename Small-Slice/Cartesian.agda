module Small-Slice.Cartesian where

-- standard library
open import Data.Unit
open import Data.Empty
open import Data.Sum 
open import Data.Nat
open import Data.Product

open import Relation.Binary.PropositionalEquality

-- local
open import Small-Slice.Univ
open import Small-Slice.ND-functions


-- terminal
𝕌-termin : {A : Set} → 𝕌Hom A ⊥
𝕌-termin a = 𝕌SL-⊥

𝕌-termin-unique : {A : Set} → (f : 𝕌Hom A ⊥) → 𝕌Hom-≡ 𝕌-termin f
proj₂ (𝕌-termin-unique f) a i with proj₂ (f a) i
... | ()

-- initial
𝕌-initia : {A : Set} → 𝕌Hom ⊥ A
𝕌-initia ()

𝕌-initia-unique : {A : Set} → (f : 𝕌Hom ⊥ A) → 𝕌Hom-≡ 𝕌-initia f
𝕌-initia-unique f = (λ {()}) , λ {()}


𝕌-void : {A B : Set} → 𝕌Hom A B
𝕌-void {A} {B} = 𝕌Hom-∘ (𝕌-initia {B}) (𝕌-termin {A})

-- product
𝕌-prod-proj₁ : {A B : Set} → 𝕌Hom (A ⊎ B) A
𝕌-prod-proj₁ (inj₁ a) = 𝕌SL-η a
𝕌-prod-proj₁ (inj₂ b) = 𝕌SL-⊥

𝕌-prod-proj₂ : {A B : Set} → 𝕌Hom (A ⊎ B) B
𝕌-prod-proj₂ (inj₁ a) = 𝕌SL-⊥
𝕌-prod-proj₂ (inj₂ b) = 𝕌SL-η b

𝕌-prod-glue : {A B C : Set} → 𝕌Hom C A → 𝕌Hom C B → 𝕌Hom C (A ⊎ B)
𝕌-prod-glue f g c = (𝕌⊎ (proj₁ (f c)) (proj₁ (g c))) ,
  λ { (inj₁ i) → inj₁ (proj₂ (f c) i) ; (inj₂ j) → inj₂ (proj₂ (g c) j)}

𝕌-prod-glue-proj₁ : {A B C : Set} → {f : 𝕌Hom C A} → {g : 𝕌Hom C B}
  → 𝕌Hom-≡ (𝕌Hom-∘ 𝕌-prod-proj₁ (𝕌-prod-glue f g)) f
proj₁ 𝕌-prod-glue-proj₁ c (inj₁ i , tt) = i , refl
proj₂ 𝕌-prod-glue-proj₁ c i = (inj₁ i , tt) , refl

𝕌-prod-glue-proj₂ : {A B C : Set} → {f : 𝕌Hom C A} → {g : 𝕌Hom C B}
  → 𝕌Hom-≡ (𝕌Hom-∘ 𝕌-prod-proj₂ (𝕌-prod-glue f g)) g
proj₁ 𝕌-prod-glue-proj₂ c (inj₂ j , tt) = j , refl
proj₂ 𝕌-prod-glue-proj₂ c i = (inj₂ i , tt) , refl

𝕌-prod-glue-inv : {A B : Set} →
  𝕌Hom-≡ (𝕌-prod-glue (𝕌-prod-proj₁ {A} {B}) (𝕌-prod-proj₂ {A} {B})) (𝕌Hom-id (A ⊎ B))
proj₁ 𝕌-prod-glue-inv (inj₁ a) (inj₁ i) = tt , refl
proj₁ 𝕌-prod-glue-inv (inj₂ b) (inj₂ j) = tt , refl
proj₂ 𝕌-prod-glue-inv (inj₁ a) i = inj₁ tt , refl
proj₂ 𝕌-prod-glue-inv (inj₂ b) j = inj₂ tt , refl

𝕌-prod-glue-⊂ : {A B C : Set} → {f f' : 𝕌Hom C A} → {g g' : 𝕌Hom C B}
  → 𝕌Hom-⊂ f f' → 𝕌Hom-⊂ g g' → 𝕌Hom-⊂ (𝕌-prod-glue f g) (𝕌-prod-glue f' g')
𝕌-prod-glue-⊂ f⊂f' g⊂g' c (inj₁ i) =
  (inj₁ (proj₁ (f⊂f' c i))) , (cong inj₁ (proj₂ (f⊂f' c i)))
𝕌-prod-glue-⊂ f⊂f' g⊂g' c (inj₂ j) =
  (inj₂ (proj₁ (g⊂g' c j))) , (cong inj₂ (proj₂ (g⊂g' c j)))

𝕌-prod-glue-≡ : {A B C : Set} → {f f' : 𝕌Hom C A} → {g g' : 𝕌Hom C B}
  → 𝕌Hom-≡ f f' → 𝕌Hom-≡ g g' → 𝕌Hom-≡ (𝕌-prod-glue f g) (𝕌-prod-glue f' g')
𝕌-prod-glue-≡ (f⊂f' , f'⊂f) (g⊂g' , g'⊂g) =
  (𝕌-prod-glue-⊂ f⊂f' g⊂g') , (𝕌-prod-glue-⊂ f'⊂f g'⊂g)

𝕌-prod-glue-nat : {A B C D : Set} → {f : 𝕌Hom C A} → {g : 𝕌Hom C B} → {h : 𝕌Hom D C}
  → 𝕌Hom-≡ (𝕌-prod-glue (𝕌Hom-∘ f h) (𝕌Hom-∘ g h)) (𝕌Hom-∘ (𝕌-prod-glue f g) h)
proj₁ 𝕌-prod-glue-nat d (inj₁ (i , j)) = (i , inj₁ j) , refl
proj₁ 𝕌-prod-glue-nat d (inj₂ (i , j)) = (i , inj₂ j) , refl
proj₂ 𝕌-prod-glue-nat d (i , inj₁ j) = inj₁ (i , j) , refl
proj₂ 𝕌-prod-glue-nat d (i , inj₂ j) = inj₂ (i , j) , refl

𝕌-prod-glue-unique : {A B C : Set} → {f : 𝕌Hom C A} → {g : 𝕌Hom C B} → (h : 𝕌Hom C (A ⊎ B))
  → 𝕌Hom-≡ (𝕌Hom-∘ 𝕌-prod-proj₁ h) f → 𝕌Hom-≡ (𝕌Hom-∘ 𝕌-prod-proj₂ h) g
  → 𝕌Hom-≡ (𝕌-prod-glue f g) h
𝕌-prod-glue-unique {A} {B} {C} {f} {g} h h₁≡f h₂≡g =
  𝕌Hom-≡-Trans {_} {_}
               {𝕌-prod-glue f g}
               {𝕌-prod-glue (𝕌Hom-∘ 𝕌-prod-proj₁ h) (𝕌Hom-∘ 𝕌-prod-proj₂ h)}
               {h}
      (𝕌-prod-glue-≡ (𝕌Hom-≡-Symm {_} {_} {𝕌Hom-∘ 𝕌-prod-proj₁ h} {f} h₁≡f)
                     (𝕌Hom-≡-Symm {_} {_} {𝕌Hom-∘ 𝕌-prod-proj₂ h} {g} h₂≡g))
  (𝕌Hom-≡-Trans {_} {_}
                {𝕌-prod-glue (𝕌Hom-∘ 𝕌-prod-proj₁ h) (𝕌Hom-∘ 𝕌-prod-proj₂ h)}
                {𝕌Hom-∘ (𝕌-prod-glue 𝕌-prod-proj₁ 𝕌-prod-proj₂) h}
                {h}
      (𝕌-prod-glue-nat {_} {_} {_} {_} {𝕌-prod-proj₁} {𝕌-prod-proj₂} {h})
  (𝕌Hom-≡-Trans {_} {_}
                {𝕌Hom-∘ (𝕌-prod-glue 𝕌-prod-proj₁ 𝕌-prod-proj₂) h}
                {𝕌Hom-∘ (𝕌Hom-id (A ⊎ B)) h}
                {h}
      (𝕌Hom-∘l≡ h 𝕌-prod-glue-inv)
      (𝕌Hom-lid h)))



-- coproduct
𝕌-copr-inj₁ : {A B : Set} → 𝕌Hom A (A ⊎ B)
𝕌-copr-inj₁ a = 𝕌SL-η (inj₁ a)

𝕌-copr-inj₂ : {A B : Set} → 𝕌Hom B (A ⊎ B)
𝕌-copr-inj₂ a = 𝕌SL-η (inj₂ a)

𝕌-copr-glue : {A B C : Set} → 𝕌Hom A C → 𝕌Hom B C → 𝕌Hom (A ⊎ B) C
𝕌-copr-glue f g (inj₁ a) = f a
𝕌-copr-glue f g (inj₂ b) = g b

𝕌-copr-glue-inj₁ : {A B C : Set} → {f : 𝕌Hom A C} → {g : 𝕌Hom B C}
  → 𝕌Hom-≡ (𝕌Hom-∘ (𝕌-copr-glue f g) 𝕌-copr-inj₁) f
𝕌-copr-glue-inj₁ = (λ x i → (proj₂ i) , refl) , (λ x i → (tt , i) , refl)

𝕌-copr-glue-inj₂ : {A B C : Set} → {f : 𝕌Hom A C} → {g : 𝕌Hom B C}
  → 𝕌Hom-≡ (𝕌Hom-∘ (𝕌-copr-glue f g) 𝕌-copr-inj₂) g
𝕌-copr-glue-inj₂ = (λ x i → (proj₂ i) , refl) , (λ x i → (tt , i) , refl)

𝕌-copr-glue-inv : {A B : Set}
  → 𝕌Hom-≡ (𝕌-copr-glue (𝕌-copr-inj₁ {A} {B}) (𝕌-copr-inj₂ {A} {B})) (𝕌Hom-id (A ⊎ B))
𝕌-copr-glue-inv = (λ {(inj₁ a) i → tt , refl ; (inj₂ b) i → tt , refl}) ,
                   λ {(inj₁ a) i → tt , refl ; (inj₂ b) i → tt , refl}

𝕌-copr-glue-unique : {A B C : Set} → {f : 𝕌Hom A C} → {g : 𝕌Hom B C} → (h : 𝕌Hom (A ⊎ B) C)
  → 𝕌Hom-≡ (𝕌Hom-∘ h 𝕌-copr-inj₁) f → 𝕌Hom-≡ (𝕌Hom-∘ h 𝕌-copr-inj₂) g
  → 𝕌Hom-≡ (𝕌-copr-glue f g) h
proj₁ (𝕌-copr-glue-unique h (h₁⊂f , f⊂h₁) (h₂⊂g , g⊂h₂)) (inj₁ a) i =
  (proj₂ (proj₁ (f⊂h₁ a i))) , (proj₂ (f⊂h₁ a i))
proj₁ (𝕌-copr-glue-unique h (h₁⊂f , f⊂h₁) (h₂⊂g , g⊂h₂)) (inj₂ b) i =
  (proj₂ (proj₁ (g⊂h₂ b i))) , (proj₂ (g⊂h₂ b i))
proj₂ (𝕌-copr-glue-unique h (h₁⊂f , f⊂h₁) (h₂⊂g , g⊂h₂)) (inj₁ a) i = h₁⊂f a (tt , i)
proj₂ (𝕌-copr-glue-unique h (h₁⊂f , f⊂h₁) (h₂⊂g , g⊂h₂)) (inj₂ b) i = h₂⊂g b (tt , i)

𝕌-copr-glue-≡ : {A B C : Set} → {f f' : 𝕌Hom A C} → {g g' : 𝕌Hom B C} →
  𝕌Hom-≡ f f' → 𝕌Hom-≡ g g' → 𝕌Hom-≡ (𝕌-copr-glue f g) (𝕌-copr-glue f' g')
𝕌-copr-glue-≡ (f⊂f' , f'⊂f) (g⊂g' , g'⊂g) = (λ {(inj₁ x) → f⊂f' x ; (inj₂ y) → g⊂g' y}) ,
  λ {(inj₁ x) → f'⊂f x ; (inj₂ y) → g'⊂g y}



-- coherences
𝕌-inj₁-proj₁ : {A B : Set} → 𝕌Hom-≡ (𝕌Hom-∘ (𝕌-prod-proj₁ {A} {B}) (𝕌-copr-inj₁ {A} {B})) (𝕌Hom-id A)
proj₁ (𝕌-inj₁-proj₁) x i = tt , refl
proj₂ (𝕌-inj₁-proj₁) x i = (tt , tt) , refl

𝕌-inj₂-proj₂ : {A B : Set} → 𝕌Hom-≡ (𝕌Hom-∘ (𝕌-prod-proj₂ {A} {B}) (𝕌-copr-inj₂ {A} {B})) (𝕌Hom-id B)
proj₁ (𝕌-inj₂-proj₂) x i = tt , refl
proj₂ (𝕌-inj₂-proj₂) x i = (tt , tt) , refl

𝕌-inj₁-glue-def : {A B : Set} → 𝕌Hom-≡ (𝕌-prod-glue (𝕌Hom-id A) (𝕌-void {A} {B})) (𝕌-copr-inj₁ {A} {B})
proj₁ 𝕌-inj₁-glue-def x (inj₁ i) = tt , refl
proj₂ 𝕌-inj₁-glue-def x i = (inj₁ tt) , refl 

𝕌-inj₂-glue-def : {A B : Set} → 𝕌Hom-≡ (𝕌-prod-glue (𝕌-void {B} {A}) (𝕌Hom-id B)) (𝕌-copr-inj₂ {A} {B})
proj₁ 𝕌-inj₂-glue-def x (inj₂ i) = tt , refl
proj₂ 𝕌-inj₂-glue-def x i = (inj₂ tt) , refl 

𝕌-proj₁-glue-def : {A B : Set} → 𝕌Hom-≡ (𝕌-copr-glue (𝕌Hom-id A) (𝕌-void {B} {A})) (𝕌-prod-proj₁ {A} {B})
proj₁ 𝕌-proj₁-glue-def (inj₁ x) i = tt , refl
proj₂ 𝕌-proj₁-glue-def (inj₁ x) i = tt , refl

𝕌-proj₂-glue-def : {A B : Set} → 𝕌Hom-≡ (𝕌-copr-glue (𝕌-void {A} {B}) (𝕌Hom-id B)) (𝕌-prod-proj₂ {A} {B})
proj₁ 𝕌-proj₂-glue-def (inj₂ x) i = tt , refl
proj₂ 𝕌-proj₂-glue-def (inj₂ x) i = tt , refl


-- closedness one way

Curry : {X Y Z : Set} → 𝕌Hom X (𝕌Hom Y Z) → 𝕌Hom (X × Y) Z
Curry f (x , y) = (𝕌Σ (proj₁ (f x) , λ i → proj₁ (proj₂ (f x) i y))) , λ {(i , j) → proj₂ (proj₂ (f x) i y) j}


Curry-≡ : {X Y Z : Set} → (f g : 𝕌Hom X (𝕌Hom Y Z)) → 𝕌Hom-≡ f g → 𝕌Hom-≡ (Curry f) (Curry g)
proj₁ (proj₁ (proj₁ (Curry-≡ f g (f<g , g<f)) (x , y) (i , j))) = proj₁ (f<g x i)
proj₂ (proj₁ (proj₁ (Curry-≡ f g (f<g , g<f)) (x , y) (i , j))) rewrite proj₂ (f<g x i) = j
proj₂ (proj₁ (Curry-≡ f g (f<g , g<f)) (x , y) (i , j)) rewrite proj₂ (f<g x i) = refl
proj₁ (proj₁ (proj₂ (Curry-≡ f g (f<g , g<f)) (x , y) (i , j))) = proj₁ (g<f x i)
proj₂ (proj₁ (proj₂ (Curry-≡ f g (f<g , g<f)) (x , y) (i , j))) rewrite proj₂ (g<f x i) = j
proj₂ (proj₂ (Curry-≡ f g (f<g , g<f)) (x , y) (i , j)) rewrite proj₂ (g<f x i) = refl


open import Small-Slice.Substructure

-- daggers
𝕌-inj₁†proj₁ : {A B : Set} → 𝕌-is-† (𝕌-copr-inj₁ {A} {B}) (𝕌-prod-proj₁ {A} {B})
proj₁ 𝕌-inj₁†proj₁ x i = tt , refl
proj₂ 𝕌-inj₁†proj₁ (inj₁ x) i = tt , refl

𝕌-inj₂†proj₂ : {A B : Set} → 𝕌-is-† (𝕌-copr-inj₂ {A} {B}) (𝕌-prod-proj₂ {A} {B})
proj₁ 𝕌-inj₂†proj₂ x i = tt , refl
proj₂ 𝕌-inj₂†proj₂ (inj₂ x) i = tt , refl

𝕌-glue-† : {A B C : Set} → (f : 𝕌Hom A B) → (f† : 𝕌Hom B A) → (g : 𝕌Hom A C) → (g† : 𝕌Hom C A)
  → 𝕌-is-† f f† → 𝕌-is-† g g† → 𝕌-is-† (𝕌-prod-glue f g) (𝕌-copr-glue f† g†)
proj₁ (𝕌-glue-† f f' g g' f†f' g†g') a (inj₁ i) = proj₁ f†f' a i
proj₁ (𝕌-glue-† f f' g g' f†f' g†g') a (inj₂ j) = proj₁ g†g' a j
proj₂ (𝕌-glue-† f f' g g' f†f' g†g') (inj₁ b) i = inj₁ (proj₁ (proj₂ f†f' b i)) , cong inj₁ (proj₂ (proj₂ f†f' b i))
proj₂ (𝕌-glue-† f f' g g' f†f' g†g') (inj₂ c) i = inj₂ (proj₁ (proj₂ g†g' c i)) , cong inj₂ (proj₂ (proj₂ g†g' c i))
