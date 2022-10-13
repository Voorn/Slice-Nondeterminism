module Examples.Iterative where

open import Data.Unit
open import Data.Empty
open import Data.Sum renaming (map to map⊎)
open import Data.Nat hiding (_⊔_)
open import Data.Product renaming (map to map×)
open import Relation.Binary.PropositionalEquality hiding ([_])


open import Slice.Base
open import Slice.Lattice


data Tower (X : Set) : Set₁ where
  leaf : X → Tower X
  node : (Σ Set λ I → (I → Tower X)) → Tower X
  bott : Tower X

Path : {X : Set} → Tower X → Set
Path (leaf x) = ⊤
Path (node (I , ns)) = Σ I λ i → Path (ns i) 
Path bott = ⊥

Ext : {X : Set} → (t : Tower X) → (p : Path t) → X
Ext (leaf x) tt = x
Ext (node (I , nt)) (i , np) = Ext (nt i) np

Tower-Slice : {X : Set} → Tower X → SL X
Tower-Slice t = (Path t) , (Ext t)


-- Simple coalgebra automata
COA : (S X : Set) → Set₁
COA S X = S → SL (S ⊎ X)

COA-Tower : {S X : Set} → COA S X → S → ℕ → Tower X
COA-Tower' : {S X : Set} → COA S X → (S ⊎ X) → ℕ → Tower X
COA-Tower c s zero = bott
COA-Tower c s (suc n) with (c s)
... | I , nt = node (I , (λ i → COA-Tower' c (nt i) n))
COA-Tower' c (inj₁ s) n = COA-Tower c s n
COA-Tower' c (inj₂ x) n = leaf x

COA-Slice : {S X : Set} → COA S X → S → ℕ → SL X
COA-Slice c s n = Tower-Slice (COA-Tower c s n)

COA-Slice-suc : {S X : Set} → (c : COA S X) → (s : S) → (n : ℕ)
  → SL→ X (COA-Slice c s n) (COA-Slice c s (suc n))
COA-Slice-suc c s zero ()
proj₁ (proj₁ (COA-Slice-suc c s (suc n) (i , p))) = i
proj₂ (proj₁ (COA-Slice-suc c s (suc n) (i , p))) with (c s)
... | I , e with (e i)
... | inj₁ z = proj₁ (COA-Slice-suc c z n p)
... | inj₂ x = tt
proj₂ (COA-Slice-suc c s (suc n) (i , p)) with (c s)
... | I , e with (e i)
... | inj₁ z = proj₂ (COA-Slice-suc c z n p)
... | inj₂ x = refl

-- More direct construction
COA-iter : {S X : Set} → (a : COA S X) → S → ℕ → SL X
COA-iter a s zero = SL-⊥ _
COA-iter a s (suc n) = SL-* (λ {(inj₁ z) → COA-iter a z n ; (inj₂ x) → SL-η _ x}) (a s)

-- ℕmax calculus
ℕ+ : ℕ → ℕ → ℕ
ℕ+ zero m = m
ℕ+ (suc n) m = suc (ℕ+ n m)

ℕ+-suc : (n m : ℕ) → ℕ+ n (suc m) ≡ suc (ℕ+ n m)
ℕ+-suc zero m = refl
ℕ+-suc (suc n) m = cong suc (ℕ+-suc n m)

COA-Slice-+ : {S X : Set} → (c : COA S X) → (s : S) → (n m : ℕ)
  → SL→ X (COA-Slice c s n) (COA-Slice c s (ℕ+ m n))
COA-Slice-+ c s n zero i = i , refl
COA-Slice-+ c s n (suc m) = SL→∘ _ (COA-Slice-+ c s n m) (COA-Slice-suc c s (ℕ+ m n))


ℕmax : ℕ → ℕ → ℕ
ℕmax zero m = m
ℕmax (suc n) zero = suc n
ℕmax (suc n) (suc m) = suc (ℕmax n m)

ℕmax-zero : (n : ℕ) → ℕmax n 0 ≡ n
ℕmax-zero zero = refl
ℕmax-zero (suc n) = refl


ℕmax-l+ : (n m : ℕ) → (Σ ℕ λ k → (ℕ+ k n ≡ ℕmax n m))
ℕmax-l+ zero zero = zero , refl
ℕmax-l+ zero (suc m) = (suc (proj₁ (ℕmax-l+ zero m))) , cong suc (proj₂ (ℕmax-l+ zero m))
ℕmax-l+ (suc n) zero = zero , refl
ℕmax-l+ (suc n) (suc m) = proj₁ (ℕmax-l+ n m) ,
  trans (ℕ+-suc (proj₁ (ℕmax-l+ n m)) n) (cong suc (proj₂ (ℕmax-l+ n m)))

ℕmax-r+ : (n m : ℕ) → (Σ ℕ λ k → (ℕ+ k m ≡ ℕmax n m))
ℕmax-r+ zero m = zero , refl
ℕmax-r+ (suc n) zero = (suc (proj₁ (ℕmax-r+ n zero))) ,
  (cong suc (trans (proj₂ (ℕmax-r+ n zero)) (ℕmax-zero n)))
ℕmax-r+ (suc n) (suc m) = proj₁ (ℕmax-r+ n m) ,
  trans (ℕ+-suc (proj₁ (ℕmax-r+ n m)) m) (cong suc (proj₂ (ℕmax-r+ n m)))

COA-Slice-lmax : {S X : Set} → (c : COA S X) → (s : S) → (n m : ℕ)
  → SL→ X (COA-Slice c s n) (COA-Slice c s (ℕmax n m))
COA-Slice-lmax c s n m with ℕmax-l+ n m
... | (k , eq) rewrite (sym eq) = COA-Slice-+ c s n k

COA-Slice-rmax : {S X : Set} → (c : COA S X) → (s : S) → (n m : ℕ)
  → SL→ X (COA-Slice c s m) (COA-Slice c s (ℕmax n m))
COA-Slice-rmax c s n m with ℕmax-r+ n m
... | (k , eq) rewrite (sym eq) = COA-Slice-+ c s m k 




SL-Stream : {X : Set} → (ℕ → SL X) → SL X
SL-Stream stre = (Σ ℕ λ n → proj₁ (stre n)) , (λ {(n , i) → proj₂ (stre n) i})

-- Automata category
AUT : (X Y : Set) → Set₁
AUT X Y = Σ Set λ S → (X → S) × COA S Y

AUT-id : (X : Set) → AUT X X
AUT-id X = X , ((λ x → x) , λ x → SL-η (X ⊎ X) (inj₂ x))

AUT-∘ : {X Y Z : Set} → AUT X Y → AUT Y Z → AUT X Z
AUT-∘ (S , ini , ste) (S' , ini' , ste') = (S ⊎ S') , ((λ x → inj₁ (ini x)) ,
  (λ {(inj₁ s) → SL-fun (λ { (inj₁ x) → inj₁ (inj₁ x) ;
                             (inj₂ y) → inj₁ (inj₂ (ini' y))}) (ste s) ;
      (inj₂ s') → SL-fun (λ {(inj₁ y) → inj₁ (inj₂ y) ;
                             (inj₂ z) → inj₂ z}) (ste' s')}))



open import Slice-Functions.Base

AUT-PK : {X Y : Set} → AUT X Y → SF X Y
AUT-PK (S , init , step) x = SL-Stream (COA-Slice step (init x))

