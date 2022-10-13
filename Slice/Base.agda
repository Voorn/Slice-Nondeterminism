module Slice.Base where

open import Data.Unit
open import Data.Empty
open import Data.Sum renaming (map to map⊎)
open import Data.Nat hiding (_⊔_)
open import Data.Product renaming (map to map×)
open import Relation.Binary.PropositionalEquality hiding ([_])

-- Slice objects
SL : (X : Set) → Set₁
SL X = Σ Set λ I → I → X


-- Slice morphism
SL→ : (X : Set) → (IA JB : SL X) → Set
SL→ X (I , A) (J , B) = (i : I) → Σ J λ j → A i ≡ B j


-- The index map of the slice morphism
SL→ex : {X : Set} → {IA JB : SL X} → SL→ X IA JB → (proj₁ IA → proj₁ JB)
SL→ex f i = proj₁ (f i)

-- The triangle equality of the slice morphism
SL→≡ : (X : Set) → (IA JB : SL X) → (SL→ X IA JB) → (SL→ X IA JB) → Set
SL→≡ X (I , A) (J , B) f g = (i : I) → proj₁ (f i) ≡ proj₁ (g i)



-- Categorical structure

-- Identity morphism
SL→id : (X : Set) → (IA : SL X) → SL→ X IA IA
SL→id X (I , A) i = i , refl

-- Morphism composition
SL→∘ : (X : Set) → {IA JB KC : SL X} → SL→ X IA JB → SL→ X JB KC → SL→ X IA KC
SL→∘ X f g i =  proj₁ (g (proj₁ (f i))) ,
  trans (proj₂ (f i)) (proj₂ (g (proj₁ (f i))))


-- Category properties
SL-asso : (X : Set) → {IA JB KC LD : SL X}
  → (f : SL→ X IA JB) → (g : SL→ X JB KC) → (h : SL→ X KC LD)
  → SL→≡ X IA LD (SL→∘ X {IA} {KC} {LD} (SL→∘ X {IA} {JB} {KC} f g) h)
                 (SL→∘ X {IA} {JB} {LD} f (SL→∘ X {JB} {KC} {LD} g h))
SL-asso X f g h i = refl

SL-luni : (X : Set) → {IA JB : SL X} → (f : SL→ X IA JB)
  → SL→≡ X IA JB (SL→∘ X {IA} {IA} {JB} (SL→id X IA) f) f
SL-luni X f i = refl

SL-runi : (X : Set) → {IA JB : SL X} → (f : SL→ X IA JB)
  → SL→≡ X IA JB (SL→∘ X {IA} {JB} {JB} f (SL→id X JB)) f
SL-runi X f i = refl





-- Extensional Endo Relations
ERel₁ : Set₁ → Set₁
ERel₁ X = X → X → Set

Refl₁ : {X : Set₁} → (ERel₁ X) → Set₁
Refl₁ {X} R = (x : X) → R x x

Tran₁ : {X : Set₁} → (ERel₁ X) → Set₁
Tran₁ {X} R = (x y z : X) → (R x y) → (R y z) → (R x z)

Symm₁ : {X : Set₁} → (ERel₁ X) → Set₁
Symm₁ {X} R = (x y : X) → R x y → R y x


-- Isomorphism
injec : {X Y : Set} → (X → Y) → Set
injec {X} f = (x x' : X) → (f x ≡ f x') → (x ≡ x')

surje : {X Y : Set} → (X → Y) → Set
surje {X} {Y} f = (y : Y) → Σ X λ x → (f x ≡ y)


SL∼ : (X : Set) → (ERel₁ (SL X))
SL∼ X IA JB = Σ (SL→ X IA JB) λ f → injec (SL→ex f) × surje (SL→ex f)

SL-iso : (X : Set) → (ERel₁ (SL X))
SL-iso X IA JB = Σ (SL→ X IA JB) λ f → Σ (SL→ X JB IA) λ g →
    SL→≡ X IA IA (SL→∘ X {IA} {JB} {IA} f g) (SL→id X IA)
  × SL→≡ X JB JB (SL→∘ X {JB} {IA} {JB} g f) (SL→id X JB)


SL∼Refl : (X : Set) → Refl₁ (SL∼ X)
SL∼Refl X (I , A) = (λ i → i , refl) , ((λ x x' eq → eq) , λ i → i , refl)

SL-iso-Refl : (X : Set) → Refl₁ (SL-iso X)
SL-iso-Refl X (I , A) = (λ i → (i , refl)) , (λ i → i , refl) ,
  (λ i → refl) , (λ i → refl)


SL∼Tran : (X : Set) → Tran₁ (SL∼ X)
SL∼Tran X (I , A) (J , B) (K , C) (f , fin , fsu) (g , gin , gsu) =
  (λ i → (proj₁ (g (proj₁ (f i)))) , (trans (proj₂ (f i)) (proj₂ (g (proj₁ (f i)))))) ,
  ((λ i i' eq → fin i i' (gin (proj₁ (f i)) (proj₁ (f i')) eq)) ,
  λ k → (proj₁ (fsu (proj₁ (gsu k)))) ,
        (trans (cong (λ z → proj₁ (g z)) (proj₂ (fsu (proj₁ (gsu k))))) (proj₂ (gsu k))))

SL-iso-Tran : (X : Set) → Tran₁ (SL-iso X)
SL-iso-Tran X (I , A) (J , B) (K , C)
  (f , f' , ff' , f'f) (g , g' , gg' , g'g)
  = (λ i → (proj₁ (g (proj₁ (f i)))) , (trans (proj₂ (f i)) (proj₂ (g (proj₁ (f i)))))) ,
  ((λ i → (proj₁ (f' (proj₁ (g' i)))) , (trans (proj₂ (g' i)) (proj₂ (f' (proj₁ (g' i)))))) ,
  (λ i → trans (cong (λ z → proj₁ (f' z)) (gg' (proj₁ (f i)))) (ff' i)) ,
  (λ i → trans (cong (λ z → proj₁ (g z)) (f'f (proj₁ (g' i)))) (g'g i)))


SL∼Symm : (X : Set) → Symm₁ (SL∼ X)
SL∼Symm X (I , A) (J , B) (f , fin , fsu) =
  (λ j → (proj₁ (fsu j)) ,
         (sym (trans (proj₂ (f (proj₁ (fsu j)))) (cong B (proj₂ (fsu j)))))) ,
  (λ j j' eq → trans (sym (proj₂ (fsu j))) (trans (cong (λ z → (proj₁ (f z))) eq)
                                                  (proj₂ (fsu j')))) ,
  λ i → (proj₁ (f i)) , (fin (proj₁ (fsu (proj₁ (f i)))) i (proj₂ (fsu (proj₁ (f i)))))

SL-iso-Symm : (X : Set) → Symm₁ (SL-iso X)
SL-iso-Symm X (I , A) (J , B) (IA→JB , JB→IA , prop₁ , prop₂)
  = JB→IA , IA→JB , prop₂ , prop₁
  

-- Similarity
SL-sim : (X : Set) → (ERel₁ (SL X))
SL-sim X IA JB = SL→ X IA JB × SL→ X JB IA


SL-sim-Refl : (X : Set) → Refl₁ (SL-sim X)
SL-sim-Refl X (I , A) = (λ i → i , refl) , (λ i → i , refl)


SL-sim-Tran : (X : Set) → Tran₁ (SL-sim X)
SL-sim-Tran X (I , A) (J , B) (K , C)  (f , f') (g , g')
  = (λ i → (proj₁ (g (proj₁ (f i)))) , (trans (proj₂ (f i)) (proj₂ (g (proj₁ (f i)))))) ,
  ((λ i → (proj₁ (f' (proj₁ (g' i)))) , (trans (proj₂ (g' i)) (proj₂ (f' (proj₁ (g' i)))))))


-- Membership

SL-∈ : (X : Set) → X → SL X → Set
SL-∈ X x (I , A) = Σ I λ i → A i ≡ x

SL-⊂ : (X : Set) → ERel₁ (SL X)
SL-⊂ X IA JB = (x : X) → SL-∈ X x IA → SL-∈ X x JB

SL→⊂ : (X : Set) → (IA JB : SL X) → (SL→ X IA JB) → SL-⊂ X IA JB
SL→⊂ X (I , A) (J , B) f x (i , eq) = proj₁ (f i) , trans (sym (proj₂ (f i))) eq

SL⊂→ : (X : Set) → (IA JB : SL X) → SL-⊂ X IA JB → (SL→ X IA JB)
SL⊂→ X (I , A) (J , B) u i = (proj₁ (u (A i) (i , refl))) ,
  sym (proj₂ (u (A i) (i , refl)))




--
SL-fun : {X Y : Set} → (X → Y) → SL X → SL Y
SL-fun f (I , F) = I , (λ i → f (F i))


-- Kleisli triple

SL-η : (X : Set) → X → SL X
SL-η X x = ⊤ , (λ i → x)

SL-* : {X Y : Set} → (X → SL Y) → (SL X → SL Y)
SL-* f (I , A) = (Σ I λ i → proj₁ (f (A i))) ,  λ { (i , k) → proj₂ (f (A i)) k}


SL∼η* : (X : Set) → (IA : SL X) → SL∼ X (SL-* (SL-η X) IA) IA
SL∼η* X (I , A) = (λ ij → (proj₁ ij) , refl) ,
  (λ {(i , tt) (i' , tt) eq → cong (λ z → (z , tt)) eq}) ,
  λ i → (i , tt) , refl

SL-η* : (X : Set) → (IA : SL X) → SL-iso X (SL-* (SL-η X) IA) IA
SL-η* X (I , A) = (λ {(i , j) → i , refl}) , (λ i → (i , tt) , refl) ,
  (λ i → refl) , (λ i → refl)


SL∼*η : {X Y : Set} → (f : X → SL Y) → (x : X) → SL∼ Y (SL-* f (SL-η X x)) (f x)
SL∼*η f x = (λ {(tt , i) → i , refl}) ,
  (λ {(tt , i) (tt , i') eq → cong (λ z → (tt , z)) eq}) ,
  λ i → (tt , i) , refl

SL-*η : {X Y : Set} → (f : X → SL Y) → (x : X) → SL-iso Y (SL-* f (SL-η X x)) (f x)
SL-*η f x = (λ p → (proj₂ p) , refl) , (λ i → (tt , i) , refl) ,
  (λ p → refl) , λ i → refl


SL∼** : {X Y Z : Set} → (f : X → SL Y) → (g : Y → SL Z) → (IA : SL X)
  → SL∼ Z (SL-* (λ x → SL-* g (f x)) IA) (SL-* g (SL-* f IA))
SL∼** f g (I , A) = (λ {(i , j , k) → ((i , j) , k) , refl}) ,
  (λ { (i , j , k) (.i , .j , .k) refl → refl}) ,
  λ {((i , j) , k) → (i , (j , k)) , refl}

SL-** : {X Y Z : Set} → (f : X → SL Y) → (g : Y → SL Z) → (IA : SL X)
  → SL-iso Z (SL-* (λ x → SL-* g (f x)) IA) (SL-* g (SL-* f IA))
SL-** f g (I , A) = (λ {(i , j , k) → ((i , j) , k) , refl}) ,
  (λ {((i , j) , k) → (i , j , k) , refl}) ,
  (λ ijk → refl) , λ ijk → refl


