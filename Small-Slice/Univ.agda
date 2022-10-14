module Small-Slice.Univ where

open import Data.Unit
open import Data.Empty
open import Data.Sum renaming (map to map⊎)
open import Data.Nat hiding (_⊔_)
open import Data.Product renaming (map to map×)
open import Relation.Binary.PropositionalEquality hiding ([_])


-- Simultaneous definition of universes as names and their corresponding sets
data 𝕌 : Set
𝕌S : 𝕌 → Set

data 𝕌 where
  𝕌⊥ : 𝕌
  𝕌⊤ : 𝕌
  𝕌ℕ : 𝕌
  𝕌→ : 𝕌 → 𝕌 → 𝕌
  𝕌⊎ : 𝕌 → 𝕌 → 𝕌
  𝕌× : 𝕌 → 𝕌 → 𝕌
  𝕌Σ : (Σ 𝕌 λ S → 𝕌S S → 𝕌) → 𝕌
  𝕌Π : (Σ 𝕌 λ S → 𝕌S S → 𝕌) → 𝕌

𝕌S 𝕌⊥ = ⊥
𝕌S 𝕌⊤ = ⊤
𝕌S 𝕌ℕ = ℕ
𝕌S (𝕌→ t t₁) = 𝕌S t → 𝕌S t₁
𝕌S (𝕌⊎ t t₁) = 𝕌S t ⊎ 𝕌S t₁
𝕌S (𝕌× t t₁) = 𝕌S t × 𝕌S t₁
𝕌S (𝕌Σ (I , A)) = Σ (𝕌S I) (λ i → 𝕌S (A i))
𝕌S (𝕌Π (I , A)) = (i : 𝕌S I) → 𝕌S (A i)



-- Main use: slices using 𝕌 don't go up a universe level
𝕌SL : Set → Set
𝕌SL X = Σ 𝕌 (λ S → 𝕌S S → X)


𝕌SL-Γ : {X Y : Set} → (R : X → Y → Set) → (𝕌SL X → 𝕌SL Y → Set)
𝕌SL-Γ R (I , f) (J , g) = Σ (𝕌S I → 𝕌S J) (λ H → (i : 𝕌S I) → R (f i) (g (H i)))

𝕌SL→ : (X : Set) → 𝕌SL X → 𝕌SL X → Set
𝕌SL→ X = 𝕌SL-Γ {X} {X} _≡_



𝕌SL-⊥ : (X : Set) → 𝕌SL X
𝕌SL-⊥ X = 𝕌⊥ , (λ {()})

𝕌SL-join : {X : Set} → 𝕌SL X → 𝕌SL X → 𝕌SL X
𝕌SL-join (I , f) (J , g) = (𝕌⊎ I J) , (λ {(inj₁ i) → f i ; (inj₂ j) → g j})

𝕌SL-ℕ : {X : Set} → (X → 𝕌SL X) → ℕ → X → 𝕌SL X
𝕌SL-ℕ f zero x = 𝕌⊤ , λ i → x
𝕌SL-ℕ f (suc n) x = (𝕌Σ (proj₁ (f x) , λ i → proj₁ (𝕌SL-ℕ f n (proj₂ (f x) i)))) ,
  λ {(i , j) → proj₂ (𝕌SL-ℕ f n (proj₂ (f x) i)) j}

𝕌SL-ω : {X : Set} → (X → 𝕌SL X) → (X → 𝕌SL X)
𝕌SL-ω f x = (𝕌Σ (𝕌ℕ , (λ n → proj₁ (𝕌SL-ℕ f n x)))) , λ {(n , i) → proj₂ (𝕌SL-ℕ f n x) i}


𝕌SL-η : {X : Set} → X → 𝕌SL X
𝕌SL-η x = 𝕌⊤ , (λ i → x)

𝕌SL-μ : {X : Set} → 𝕌SL (𝕌SL X) → 𝕌SL X
𝕌SL-μ (I , f) = (𝕌Σ (I , (λ i → proj₁ (f i)))) , λ {(i , j) → proj₂ (f i) j}

𝕌SL-κ : {X Y : Set} → (X → 𝕌SL Y) → (𝕌SL X → 𝕌SL Y)
𝕌SL-κ f (I , A) = 𝕌Σ (I , (λ i → proj₁ (f (A i)))) , λ {(i , j) → proj₂ (f (A i)) j}

𝕌SL-μ≡ : {X : Set} → (d d' : 𝕌SL (𝕌SL X)) → 𝕌SL-Γ (𝕌SL-Γ _≡_) d d'
  → 𝕌SL-Γ _≡_ (𝕌SL-μ d) (𝕌SL-μ d')
𝕌SL-μ≡ (I , f) (J , g) (H , rel) = (λ {(i , a) → (H i) , (proj₁ (rel i) a)}) ,
  λ {(i , a) → proj₂ (rel i) a}


--
𝕌Hom : Set → Set → Set
𝕌Hom X Y = X → 𝕌SL Y

𝕌Hom-⊂ : {X Y : Set} → 𝕌Hom X Y → 𝕌Hom X Y → Set
𝕌Hom-⊂ {X} {Y} f g = (x : X) → 𝕌SL→ Y (f x) (g x)

𝕌Hom-id : (X : Set) → 𝕌Hom X X
𝕌Hom-id X x = 𝕌SL-η x

𝕌Hom-∘ : {X Y Z : Set} → 𝕌Hom X Y → 𝕌Hom Y Z → 𝕌Hom X Z
𝕌Hom-∘ f g x = 𝕌SL-κ g (f x)


-- Set functor
𝕌Hom-fun : {X Y : Set} → (X → Y) → 𝕌Hom X Y
𝕌Hom-fun f x = 𝕌SL-η (f x)


-- Container Monad
𝕌-Sig : Set₁
𝕌-Sig = Σ Set λ A → A → 𝕌


data Free (S : 𝕌-Sig) (X : Set) : Set where
  leaf : X → Free S X
  node : (σ : proj₁ S) → (ts : 𝕌S (proj₂ S σ) → Free S X) → Free S X

Free-μ : (S : 𝕌-Sig) → (X : Set) → Free S (Free S X) → Free S X
Free-μ S X (leaf t) = t
Free-μ S X (node σ ts) = node σ (λ i → Free-μ S X (ts i))


𝕌Free-μ : (S : 𝕌-Sig) → (X : Set) → 𝕌Hom (Free S (Free S X)) (Free S X)
𝕌Free-μ S X d = 𝕌SL-η (Free-μ S X d)

𝕌Free-δ : (S : 𝕌-Sig) → (X : Set) → 𝕌Hom (Free S X) (Free S (Free S X))
𝕌Free-δ S X (leaf x) = 𝕌SL-η (leaf (leaf x))
proj₁ (𝕌Free-δ S X (node σ ts)) = 𝕌Π (proj₂ S σ , λ i → proj₁ (𝕌Free-δ S X (ts i)))
proj₂ (𝕌Free-δ S X (node σ ts)) f = node σ (λ i → proj₂ (𝕌Free-δ S X (ts i)) (f i))

open import Extensionality

𝕌Free-eq<-δμ : (S : 𝕌-Sig) → (X : Set)
  → 𝕌Hom-⊂ (𝕌Hom-∘ (𝕌Free-δ S X) (𝕌Free-μ S X)) (𝕌Hom-id (Free S X))
𝕌Free-eq<-δμ S X (leaf x) = (λ a → tt) , λ a → refl
proj₁ (𝕌Free-eq<-δμ S X (node σ ts)) = (λ x → tt)
proj₂ (𝕌Free-eq<-δμ S X (node σ ts)) (a , tt) =
  cong (node σ) (dep-ext (λ i → proj₂ (𝕌Free-eq<-δμ S X (ts i)) (a i , tt)))



𝕌SL-⊗ : {X Y  : Set} → 𝕌SL X → 𝕌SL Y → 𝕌SL (X × Y)
𝕌SL-⊗ (I , f) (J , g) = (𝕌× I J) , (λ {(x , y) → (f x) , (g y)})

𝕌SL-⊗→ : {X Y : Set} → {a a' : 𝕌SL X} → (𝕌SL→ X a a') → {b b' : 𝕌SL Y} → (𝕌SL→ Y b b')
  → 𝕌SL→ (X × Y) (𝕌SL-⊗ a b) (𝕌SL-⊗ a' b') 
𝕌SL-⊗→ (f , a-f->a') (g , b-g->b') = (λ {(i , j) → (f i) , (g j)}) ,
  λ {(i , j) → cong₂ (λ x y → (x , y)) (a-f->a' i) (b-g->b' j)} 



𝕌SL-⊎ : {X Y : Set} → (𝕌SL X ⊎ 𝕌SL Y) → 𝕌SL (X ⊎ Y)
𝕌SL-⊎ (inj₁ (I , f)) = I , λ i → inj₁ (f i)
𝕌SL-⊎ (inj₂ (J , g)) = J , λ j → inj₂ (g j)

𝕌SL-⊎→1 :  {X Y : Set} → {a a' : 𝕌SL X} → (𝕌SL→ X a a')
  → 𝕌SL→ (X ⊎ Y) (𝕌SL-⊎ (inj₁ a)) (𝕌SL-⊎ (inj₁ a')) 
𝕌SL-⊎→1 (f , a-f->a') = f , (λ i → cong inj₁ (a-f->a' i))

𝕌SL-⊎→2 :  {X Y : Set} → {b b' : 𝕌SL Y} → (𝕌SL→ Y b b')
  → 𝕌SL→ (X ⊎ Y) (𝕌SL-⊎ (inj₂ b)) (𝕌SL-⊎ (inj₂ b')) 
𝕌SL-⊎→2 (g , b-g->b') = g , (λ i → cong inj₂ (b-g->b' i))




𝕌SL-⊗-⊎ : {X Y : Set} → 𝕌SL (X × Y) → 𝕌SL (X ⊎ Y) 
𝕌SL-⊗-⊎ (I , f) = (𝕌⊎ I I) , (λ { (inj₁ i) → inj₁ (proj₁ (f i)) ;
                                  (inj₂ i) → inj₂ (proj₂ (f i))})

