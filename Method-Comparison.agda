module Method-Comparison where

open import Data.Unit
open import Data.Bool
open import Data.Sum 
open import Data.Nat 
open import Data.Product 
open import Relation.Binary.PropositionalEquality 



Erel-ℕ : Set₁
Erel-ℕ = ℕ → ℕ → Set

Span-ℕ : Set₁
Span-ℕ = Σ Set λ I → I → ℕ × ℕ

Slic-ℕ : Set₁
Slic-ℕ = ℕ → Σ Set λ I → (I → ℕ)


--
Erel-ℕ-test : Erel-ℕ → ℕ → ℕ → Set
Erel-ℕ-test R = R

Span-ℕ-test : Span-ℕ → ℕ → ℕ → Set
Span-ℕ-test (I , f) n m = Σ I λ i → f i ≡ (n , m)

Slic-ℕ-test : Slic-ℕ → ℕ → ℕ → Set
Slic-ℕ-test f n m = Σ (proj₁ (f n)) λ i → proj₂ (f n) i ≡ m




Erel-ℕ-id : Erel-ℕ
Erel-ℕ-id n m = n ≡ m

Span-ℕ-id : Span-ℕ
Span-ℕ-id = ℕ , λ n → n , n

Slic-ℕ-id : Slic-ℕ
Slic-ℕ-id n = ⊤ , (λ x → n)


-- Relation composition requires finding the intermediate state b
Erel-ℕ-comp : Erel-ℕ → Erel-ℕ → Erel-ℕ
Erel-ℕ-comp R S a c = Σ ℕ λ b → R a b × S b c

-- Span composition requires checking equality over intermediate state
Span-ℕ-comp : Span-ℕ → Span-ℕ → Span-ℕ  
Span-ℕ-comp (I , f) (J , g) = (Σ (I × J) λ {(i , j) → proj₂ (f i) ≡ proj₁ (g j)}) ,
  λ {((i , j) , eq) → proj₁ (f i) , proj₂ (g j)}

-- Slic composition only uses index information
Slic-ℕ-comp : Slic-ℕ → Slic-ℕ → Slic-ℕ
Slic-ℕ-comp f g a = (Σ (proj₁ (f a)) λ i → proj₁ (g (proj₂ (f a) i))) ,
  λ {(i , j) → proj₂ (g (proj₂ (f a) i)) j}



-- Representing the function that either keeps input, or increases it by one

Erel-ℕ-toss : Erel-ℕ
Erel-ℕ-toss n m = (n ≡ m) ⊎ (suc n ≡ m)

Span-ℕ-toss : Span-ℕ
Span-ℕ-toss = (ℕ × Bool) , λ {(n , false) → n , n ; (n , true) → n , (suc n)}

Slic-ℕ-toss : Slic-ℕ
Slic-ℕ-toss n = Bool , (λ { false → n ; true → suc n})



Erel-ℕ-multi-toss : (n : ℕ) → Erel-ℕ
Erel-ℕ-multi-toss zero    = Erel-ℕ-id
Erel-ℕ-multi-toss (suc n) = Erel-ℕ-comp Erel-ℕ-toss (Erel-ℕ-multi-toss n)


Span-ℕ-multi-toss : (n : ℕ) → Span-ℕ
Span-ℕ-multi-toss zero    = Span-ℕ-id
Span-ℕ-multi-toss (suc n) = Span-ℕ-comp Span-ℕ-toss (Span-ℕ-multi-toss n)


Slic-ℕ-multi-toss : (n : ℕ) → Slic-ℕ
Slic-ℕ-multi-toss zero    = Slic-ℕ-id
Slic-ℕ-multi-toss (suc n) = Slic-ℕ-comp Slic-ℕ-toss (Slic-ℕ-multi-toss n)



-- Example in all three models: tossing 5 coins can produce 3 heads
-- We will show this with a sequence of two tail followed by 3 heads, 0+0+0+1+1+1 = 3
Erel-ℕ-example : Erel-ℕ-test (Erel-ℕ-multi-toss 5) 0 3
Erel-ℕ-example = 0 , (inj₁ refl , 0 , (inj₁ refl) , 1 , (inj₂ refl) , 2 , (inj₂ refl) ,
  3 , (inj₂ refl) , refl)

Span-ℕ-example : Span-ℕ-test (Span-ℕ-multi-toss 5) 0 3
Span-ℕ-example = (((0 , false) , ((0 , false) , ((0 , true) , ((1 , true) ,
  ((2 , true) , 3) , refl) , refl) , refl) , refl) , refl) , refl

Slic-ℕ-example : Slic-ℕ-test (Slic-ℕ-multi-toss 5) 0 3
Slic-ℕ-example = (false , false , true , true , true , tt) , refl


-- In the last version, only the results of the coin tosses and one final check are considered.
-- No extra details need to be filled in, such as specifying intermediate results.


-- General example: tossing 2n coins can produce n head
-- we show this using a sequence of tail-heads.
doub : ℕ → ℕ
doub zero = zero
doub (suc n) = suc (suc (doub n))

rsuc : (n m : ℕ) → ((n + suc m) ≡ suc (n + m))
rsuc zero m = refl
rsuc (suc n) m = cong suc (rsuc n m)

Erel-ℕ-example2 : (n m : ℕ) → Erel-ℕ-test (Erel-ℕ-multi-toss (doub n)) m (n + m)
Erel-ℕ-example2 zero m = refl
Erel-ℕ-example2 (suc n) m = m , ((inj₁ refl) , ((suc m) , ((inj₂ refl) ,
  subst (λ z → Erel-ℕ-multi-toss (doub n) (suc m) z) (rsuc n m)
    (Erel-ℕ-example2 n (suc m)))))

Span-ℕ-example2 : (n m : ℕ) → Span-ℕ-test (Span-ℕ-multi-toss (doub n)) m (n + m)
Span-ℕ-example2 zero m = m , refl
Span-ℕ-example2 (suc n) m with Span-ℕ-example2 n (suc m)
... | (u , eq) = (((m , false) , (((m , true) , u) , sym (cong proj₁ eq))) , refl) ,
  cong (λ z → m , z) (trans (cong proj₂ eq) (rsuc n m))

Slic-ℕ-example2 : (n m : ℕ) → Slic-ℕ-test (Slic-ℕ-multi-toss (doub n)) m (n + m)
Slic-ℕ-example2 zero m = tt , refl
Slic-ℕ-example2 (suc n) m with Slic-ℕ-example2 n (suc m)
... | u , eq = (false , true , u) , trans eq (rsuc n m)
