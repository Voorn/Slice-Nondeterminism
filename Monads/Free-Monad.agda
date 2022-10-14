module Monads.Free-Monad where

open import Data.Unit
open import Data.Empty
open import Data.Sum renaming (map to map⊎)
open import Data.Nat hiding (_⊔_)
open import Data.Product renaming (map to map×)
open import Relation.Binary.PropositionalEquality hiding ([_])


open import Slice.Base
open import Slice.Lattice

open import Slice-Functions.Base
open import Slice-Functions.Subcategories
open import Slice-Functions.Dagger

open import Extensionality

-- Container Monad

Sig : Set₁
Sig = Σ Set λ A → A → Set


data Free (S : Sig) (X : Set) : Set where
  leaf : X → Free S X
  node : (σ : proj₁ S) → (ts : proj₂ S σ → Free S X) → Free S X


Free-η : (S : Sig) → (X : Set) → X → Free S X
Free-η S X = leaf

Free-μ : (S : Sig) → (X : Set) → Free S (Free S X) → Free S X
Free-μ S X (leaf t) = t
Free-μ S X (node σ ds) = node σ (λ b → Free-μ S X (ds b))

Free-σ : (S : Sig) → (X Y : Set) → (Free S X × Y) → Free S (X × Y)
Free-σ S X Y (leaf x , y) = leaf (x , y)
Free-σ S X Y (node σ ts , y) = node σ (λ i → Free-σ S X Y (ts i , y))


Pos : (S : Sig) → (X : Set) → (X → Set) → Free S X → Set
Pos S X f (leaf x) = f x
Pos S X f (node σ ts) = (i : proj₂ S σ) → Pos S X f (ts i)


Pos-In : (S : Sig) → (X : Set) → (f : X → Set) → (t : Free S X) →
  (g : (x : X) → f x) → Pos S X f t
Pos-In S X f (leaf x) g = g x
Pos-In S X f (node σ ts) g c = Pos-In S X f (ts c) g


Free-P : (S : Sig) → {X Y : Set} → Free S X → (X → SL Y) → SL (Free S Y)
proj₁ (Free-P S {X} {Y} t p) = Pos S X (λ x → proj₁ (p x)) t
proj₂ (Free-P S {X} {Y} (leaf x) p) i = leaf (proj₂ (p x) i)
proj₂ (Free-P S {X} {Y} (node σ ts) p) i =
  node σ (λ b → proj₂ (Free-P S {X} {Y} (ts b) p) (i b))

SF-F : (S : Sig) → {X Y : Set} → SF X Y → SF (Free S X) (Free S Y)
SF-F S f t = Free-P S t f

-- Completeness and soundness
data Free-dist (S : Sig) {X Y : Set} (f : X → SL Y) : Free S X → Free S Y → Set where
  FD-leaf : (x : X) → (i : proj₁ (f x)) → Free-dist S f (leaf x) (leaf (proj₂ (f x) i))
  FD-node : (σ : proj₁ S) → (ts : proj₂ S σ → Free S X) → (rs : proj₂ S σ → Free S Y)
    → ((i : proj₂ S σ) → Free-dist S f (ts i) (rs i)) → Free-dist S f (node σ ts) (node σ rs)

FD-complete : (S : Sig) → {X Y : Set} → (t : Free S X) → (f : X → SL Y)
  → (r : Free S Y) → Free-dist S f t r → SL-∈ (Free S Y) r (Free-P S t f)
proj₁ (FD-complete S (leaf x) f .(leaf (proj₂ (f x) i)) (FD-leaf .x i)) = i
proj₁ (FD-complete S (node σ ts) f .(node σ rs) (FD-node .σ .ts rs x)) c =
  proj₁ (FD-complete S (ts c) f (rs c) (x c)) 
proj₂ (FD-complete S (leaf x) f .(leaf (proj₂ (f x) i)) (FD-leaf .x i)) = refl
proj₂ (FD-complete S (node σ ts) f .(node σ rs) (FD-node .σ .ts rs x)) = cong (node σ) (fun-ext (λ c →
  proj₂ (FD-complete S (ts c) f (rs c) (x c)) ))

FD-sound : (S : Sig) → {X Y : Set} → (t : Free S X) → (f : X → SL Y)
  → (r : Free S Y) → SL-∈ (Free S Y) r (Free-P S t f) → Free-dist S f t r
FD-sound S (leaf x) f .(leaf (proj₂ (f x) i)) (i , refl) = FD-leaf x i
FD-sound S (node σ ts) f .(node σ (λ b → proj₂ (Free-P S (ts b) f) (i b))) (i , refl) =
  FD-node σ ts (λ b → proj₂ (Free-P S (ts b) f) (i b)) λ j →
    FD-sound S (ts j) f (proj₂ (Free-P S (ts j) f) (i j)) ((i j) , refl)


-- Functorial properties
SF-F-id : (S : Sig) → (X : Set) → SF≡ (SF-F S (SF-id X)) (SF-id (Free S X))
proj₁ (SF-F-id S X) (leaf x) i = tt , refl
proj₁ (SF-F-id S X) (node σ ts) i = tt ,
  cong (node σ) (fun-ext λ b → proj₂ (proj₁ (SF-F-id S X) (ts b) (i b)))
proj₂ (SF-F-id S X) (leaf x) tt = tt , refl
proj₂ (SF-F-id S X) (node σ ts) tt = (λ b → proj₁ (proj₂ (SF-F-id S X) (ts b) tt)) ,
  cong (node σ) (fun-ext (λ b → proj₂ (proj₂ (SF-F-id S X) (ts b) tt)))

SF-F-∘ : (S : Sig) → {X Y Z : Set} → (f : SF X Y) → (g : SF Y Z)
  → SF≡ (SF-F S (SF-∘ f g)) (SF-∘ (SF-F S f) (SF-F S g))
proj₁ (proj₁ (SF-F-∘ S f g) (leaf x) i) = i
proj₁ (proj₁ (SF-F-∘ S f g) (node σ ts) i) =
  (λ b → proj₁ (proj₁ (proj₁ (SF-F-∘ S f g) (ts b) (i b)))) ,
  λ b → proj₂ (proj₁ (proj₁ (SF-F-∘ S f g) (ts b) (i b)))
proj₂ (proj₁ (SF-F-∘ S f g) (leaf x) i) = refl
proj₂ (proj₁ (SF-F-∘ S f g) (node σ ts) i) = cong (node σ) (fun-ext (λ b →
  proj₂ (proj₁ (SF-F-∘ S f g) (ts b) (i b))))
proj₁ (proj₂ (SF-F-∘ S f g) (leaf x) i) = i
proj₁ (proj₂ (SF-F-∘ S f g) (node σ ts) (i , j)) =
  λ b → proj₁ (proj₂ (SF-F-∘ S f g) (ts b) (i b , j b))
proj₂ (proj₂ (SF-F-∘ S f g) (leaf x) i) = refl
proj₂ (proj₂ (SF-F-∘ S f g) (node σ ts) (i , j)) = cong (node σ) (fun-ext (λ b →
  proj₂ (proj₂ (SF-F-∘ S f g) (ts b) (i b , j b))))


SF-F-η : (S : Sig) → (X : Set) → SF X (Free S X)
SF-F-η S X = SF-Fun leaf




SF-F-η-nat : (S : Sig) → {X Y : Set} → (f : SF X Y) →
  SF≡ (SF-∘ f (SF-F-η S Y)) (SF-∘ (SF-F-η S X) (SF-F S f))
proj₁ (SF-F-η-nat S f) x (i , tt) = (tt , i) , refl
proj₂ (SF-F-η-nat S f) x (tt , i) = (i , tt) , refl


SF-F-μ : (S : Sig) → (X : Set) → SF (Free S (Free S X)) (Free S X)
SF-F-μ S X = SF-Fun (Free-μ S X)

SF-F-μ-nat : (S : Sig) → {X Y : Set} → (f : SF X Y) →
  SF≡ (SF-∘ (SF-F S (SF-F S f)) (SF-F-μ S Y)) (SF-∘ (SF-F-μ S X) (SF-F S f))
proj₁ (SF-F-μ-nat S f) (leaf t) (i , tt) = (tt , i) , refl
proj₁ (SF-F-μ-nat S f) (node σ ts) (i , tt) =
  (tt , (λ b → proj₂ (proj₁ (proj₁ (SF-F-μ-nat S f) (ts b) (i b , tt))))) ,
  cong (node σ) (fun-ext (λ b → proj₂ (proj₁ (SF-F-μ-nat S f) (ts b) (i b , tt))))
proj₂ (SF-F-μ-nat S f) (leaf t) (tt , i) = (i , tt) , refl
proj₂ (SF-F-μ-nat S f) (node σ ts) (tt , i) =
  ((λ b → proj₁ (proj₁ (proj₂ (SF-F-μ-nat S f) (ts b) (tt , i b)))) , tt) ,
  cong (node σ) (fun-ext (λ b → proj₂ (proj₂ (SF-F-μ-nat S f) (ts b) (tt , i b))))


-- A bit of unneccessary details, since indexing sets below are isomorphic to ⊤

SF-F-luni : (S : Sig) → (X : Set)
  → SF≡ (SF-∘ (SF-F-η S (Free S X)) (SF-F-μ S X)) (SF-id (Free S X))
proj₁ (SF-F-luni S X) t i = tt , refl
proj₂ (SF-F-luni S X) t i = (tt , tt) , refl


SF-F-runi : (S : Sig) → (X : Set)
  → SF≡ (SF-∘ (SF-F S (SF-F-η S X)) (SF-F-μ S X)) (SF-id (Free S X))
proj₁ (SF-F-runi S X) (leaf x) (i , tt) = tt , refl
proj₁ (SF-F-runi S X) (node σ ts) (i , tt) = tt ,
  (cong (node σ) (fun-ext (λ b → proj₂ (proj₁ (SF-F-runi S X) (ts b) (i b , tt)))))
proj₂ (SF-F-runi S X) (leaf x) tt = (tt , tt) , refl
proj₂ (SF-F-runi S X) (node σ ts) tt =
  ((λ b → proj₁ (proj₁ (proj₂ (SF-F-runi S X) (ts b) tt)) ) , tt) ,
  cong (node σ) (fun-ext (λ b → proj₂ (proj₂ (SF-F-runi S X) (ts b) tt)))


SF-F-asso : (S : Sig) → (X : Set)
  → SF≡ (SF-∘ (SF-F-μ S (Free S X)) (SF-F-μ S X))
         (SF-∘ (SF-F S (SF-F-μ S X)) (SF-F-μ S X))
proj₁ (proj₁ (SF-F-asso S X) (leaf d) (tt , tt)) = tt , tt
proj₁ (proj₁ (SF-F-asso S X) (node σ ts) (tt , tt)) =
  (λ b → proj₁ (proj₁ (proj₁ (SF-F-asso S X) (ts b) (tt , tt)))) , tt
proj₂ (proj₁ (SF-F-asso S X) (leaf q) (tt , tt)) = refl
proj₂ (proj₁ (SF-F-asso S X) (node σ ts) (tt , tt)) =
  cong (node σ) (fun-ext (λ b → proj₂ (proj₁ (SF-F-asso S X) (ts b) (tt , tt))))
proj₁ (proj₂ (SF-F-asso S X) q i) = tt , tt
proj₂ (proj₂ (SF-F-asso S X) (leaf q) i) = refl
proj₂ (proj₂ (SF-F-asso S X) (node σ ts) (i , tt)) = cong (node σ) (fun-ext (λ b →
  proj₂ (proj₂ (SF-F-asso S X) (ts b) (i b , tt))))


SF-F-dag : (S : Sig) → {X Y : Set} → (f : SF X Y)
  → SF≡ (SF-F S (SF-dag f)) (SF-dag (SF-F S f))
proj₁ (SF-F-dag S f) (leaf y) (x , i , eq) = ((leaf x) , (i , (cong leaf eq))) , refl
proj₁ (SF-F-dag S f) (node σ ts) i =
  ((node σ (λ b → proj₁ (proj₁ (proj₁ (SF-F-dag S f) (ts b) (i b))))) ,
  (λ b → proj₁ (proj₂ (proj₁ (proj₁ (SF-F-dag S f) (ts b) (i b))))) ,
  cong (node σ) (fun-ext (λ b → proj₂ (proj₂ (proj₁ (proj₁ (SF-F-dag S f) (ts b) (i b)))))))
  , cong (node σ) (fun-ext (λ b → proj₂ (proj₁ (SF-F-dag S f) (ts b) (i b))))
proj₂ (SF-F-dag S f) (leaf .(proj₂ (f x) i)) (leaf x , i , refl) = (x , (i , refl)) , refl
proj₂ (SF-F-dag S f) (node σ .(λ b → proj₂ (Free-P S (ts₁ b) f) (i b)))
  (node .σ ts₁ , i , refl) = (λ b → proj₁ (proj₂ (SF-F-dag S f) (proj₂ (Free-P S (ts₁ b) f)
    (i b)) (ts₁ b , i b , refl))) ,
  cong (node σ) (fun-ext (λ b → proj₂ (proj₂ (SF-F-dag S f) (proj₂ (Free-P S (ts₁ b) f)
    (i b)) (ts₁ b , i b , refl))))


-- Dualization: Comonad structure
SF-F-ε : (S : Sig) → (X : Set) → SF (Free S X) X
SF-F-ε S X = SF-dag (SF-F-η S X)

SF-F-ε-alt : (S : Sig) → (X : Set) → SF (Free S X) X
SF-F-ε-alt S X (leaf x) = SF-id _ x
SF-F-ε-alt S X (node σ ts) = SL-⊥ X

SF-F-ε-≡ : (S : Sig) → (X : Set) → SF≡ (SF-F-ε S X) (SF-F-ε-alt S X)
proj₁ (SF-F-ε-≡ S X) .(leaf x) (x , tt , refl) = tt , refl
proj₂ (SF-F-ε-≡ S X) (leaf x) tt = (x , tt , refl) , refl


SF-F-δ : (S : Sig) → (X : Set) → SF (Free S X) (Free S (Free S X))
SF-F-δ S X = SF-dag (SF-F-μ S X)


SF-F-δ-alt : (S : Sig) → (X : Set) → SF (Free S X) (Free S (Free S X))
SF-F-δ-alt S X (leaf x) = SF-id _ (leaf (leaf x))
SF-F-δ-alt S X (node σ ts) = join (SF-id _ (leaf (node σ ts)))
  (((i : proj₂ S σ) → proj₁ (SF-F-δ-alt S X (ts i))) ,
  (λ c → node σ (λ i → proj₂ (SF-F-δ-alt S X (ts i)) (c i))))


SF-F-δ-≡ : (S : Sig) → (X : Set) → SF≡ (SF-F-δ S X) (SF-F-δ-alt S X)
proj₁ (SF-F-δ-≡ S X) (leaf x) (leaf .(leaf x) , tt , refl) = tt , refl
proj₁ (SF-F-δ-≡ S X) (node σ ts) (leaf .(node σ ts) , tt , refl) = (inj₁ tt) , refl
proj₁ (SF-F-δ-≡ S X) .(node σ (λ i → Free-μ S X (ts i))) (node σ ts , tt , refl) =
  (inj₂ (λ i → proj₁ (proj₁ (SF-F-δ-≡ S X) (Free-μ S X (ts i)) (ts i , tt , refl)))) ,
  cong (node σ)
       (fun-ext (λ i → proj₂ (proj₁ (SF-F-δ-≡ S X) (Free-μ S X (ts i)) (ts i , tt , refl))))
proj₂ (SF-F-δ-≡ S X) (leaf x) tt = (leaf (leaf x) , tt , refl) , refl
proj₂ (SF-F-δ-≡ S X) (node σ ts) (inj₁ tt) = (leaf (node σ ts) , tt , refl) , refl
proj₂ (SF-F-δ-≡ S X) (node σ ts) (inj₂ c) =
  ((node σ (λ i → proj₁ (proj₁ (proj₂ (SF-F-δ-≡ S X) (ts i) (c i))))) , tt ,
  (cong (node σ)
        (fun-ext (λ i → proj₂ (proj₂ (proj₁ (proj₂ (SF-F-δ-≡ S X) (ts i) (c i)))))))) ,
  cong (node σ) (fun-ext (λ i → proj₂ (proj₂ (SF-F-δ-≡ S X) (ts i) (c i))))


SF-F-coas : (S : Sig) → (X : Set)
  → SF≡ (SF-∘ (SF-F-δ S X) (SF-F-δ S (Free S X)))
         (SF-∘ (SF-F-δ S X) (SF-F S (SF-F-δ S X)))
SF-F-coas S X = SF≡-Tran _ _ _ (SF≡-Symm _ _ (SF-dag-∘ (SF-F-μ S (Free S X)) (SF-F-μ S X)))
                (SF≡-Tran _ _ _ (SF≡-Symm _ _ (SF-dag-≡ _ _ (SF-F-asso S X)))
                (SF≡-Tran _ _ _ (SF-dag-∘ (SF-F S (SF-F-μ S X)) (SF-F-μ S X))
                ((SF-∘-r≡ (SF-F-δ S X) (SF-dag (SF-F S (SF-F-μ S X))) (SF-F S (SF-F-δ S X))
                          (SF≡-Symm _ _ (SF-F-dag S (SF-F-μ S X)))))))


SF-F-δμ : (S : Sig) → (X : Set) → SF≡ (SF-∘ (SF-F-δ S X) (SF-F-μ S X)) (SF-id (Free S X))
proj₁ (SF-F-δμ S X) .(Free-μ S X d) ((d , tt , refl) , tt) = tt , refl
proj₂ (SF-F-δμ S X) t tt = (((leaf t) , (tt , refl)) , tt) , refl


SF-F-ηδ≡ηη : (S : Sig) → (X : Set) → SF≡ (SF-∘ (SF-F-η S X) (SF-F-δ S X))
                                           (SF-∘ (SF-F-η S X) (SF-F-η S (Free S X)))
proj₁ (SF-F-ηδ≡ηη S X) x (tt , leaf (leaf .x) , tt , refl) = (tt , tt) , refl
proj₂ (SF-F-ηδ≡ηη S X) x (tt , tt) = (tt , ((leaf (leaf x)) , (tt , refl))) , refl

SF-F-με-εε : (S : Sig) → (X : Set) → SF≡ (SF-∘ (SF-F-μ S X) (SF-F-ε S X))
                                         (SF-∘ (SF-F-ε S (Free S X)) (SF-F-ε S X))
proj₁ (SF-F-με-εε S X) (leaf (leaf x)) (tt , .x , tt , refl) =
  (((leaf x) , (tt , refl)) , (x , (tt , refl))) , refl
proj₂ (SF-F-με-εε S X) .(leaf (leaf x)) ((.(leaf x) , tt , refl) , x , tt , refl) =
  (tt , (x , (tt , refl))) , refl

SF-F-ηε : (S : Sig) → (X : Set) → SF≡ (SF-∘ (SF-F-η S X) (SF-F-ε S X)) (SF-id X)
proj₁ (SF-F-ηε S X) x (tt , .x , tt , refl) = tt , refl
proj₂ (SF-F-ηε S X) x tt = (tt , (x , (tt , refl))) , refl


SF-F-χ-alt : (S : Sig) → (X : Set) → SF (Free S (Free S X)) (Free S (Free S X))
SF-F-χ-alt S X = SF-∘ (SF-F-μ S X) (SF-F-δ-alt S X)

-- SF-F-super : (S : Sig) → (X : Set) → SF≡
--   (SF-∘ (SF-F S (SF-F-δ-alt S X))
--   (SF-∘ (SF-F-δ-alt S (Free S (Free S X)))
--   (SF-∘ (SF-F S (SF-F-χ-alt S (Free S X)))
--   (SF-∘ (SF-F-μ S (Free S (Free S X)))
--   (SF-F S (SF-F-μ S X))))))
--   (SF-F-χ-alt S X)
-- proj₁ (SF-F-super S X) (leaf (leaf x)) (p , i , j , tt , k) = (tt , tt) , refl
-- proj₁ (SF-F-super S X) (leaf (node σ ts)) (inj₁ x , i , j , tt , k) = (tt , (inj₁ tt)) , refl
-- proj₁ (SF-F-super S X) (leaf (node σ ts)) (inj₂ y , i , (tt , inj₁ j) , tt , k) =
--   (tt , (inj₁ tt)) , cong leaf (cong (node σ) (fun-ext (λ a → {!proj₁ (SF-F-δμ S X) (ts a) !})))
-- proj₁ (SF-F-super S X) (leaf (node σ ts)) (inj₂ y , i , (tt , inj₂ j) , tt , k) =
--   (tt , (inj₂ y)) , {!!}
-- proj₁ (SF-F-super S X) (node σ ts) (p , inj₁ tt , j , tt , k) = {!!}
-- proj₁ (SF-F-super S X) (node σ ts) (p , inj₂ i , j , tt , k) = (tt ,
--   (inj₂ (λ a → proj₂ (proj₁ (proj₁ (SF-F-super S X) (ts a) (p a , i a , j a , tt , k a))))))
--   , cong (node σ) (fun-ext (λ a
--     → proj₂ (proj₁ (SF-F-super S X) (ts a) (p a , i a , j a , tt , k a))))
-- proj₂ (SF-F-super S X) v i = {!!}


-- -- SF-F-super : (S : Sig) → (X : Set) → SF≡
-- --   (SF-∘ (SF-F S (SF-F-δ S X))
-- --   (SF-∘ (SF-F-δ S (Free S (Free S X)))
-- --   (SF-∘ (SF-F S (SF-F-χ S (Free S X)))
-- --   (SF-∘ (SF-F-μ S (Free S (Free S X)))
-- --   (SF-F S (SF-F-μ S X))))))
-- --   (SF-F-χ S X)
-- -- proj₁ (SF-F-super S X) (leaf (leaf x)) ((leaf .(leaf x) , tt , refl) ,
-- --   (leaf .(leaf (leaf (leaf x))) , tt , refl) ,
-- --    (tt , leaf .(leaf (leaf x)) , tt , refl) , tt , tt) =
-- --    (tt , ((leaf (leaf x)) , (tt , refl))) , refl
-- -- proj₁ (SF-F-super S X) (leaf (node σ ts)) ((leaf d , tt , snd) , (leaf .(leaf (leaf d)) , tt , refl) , k , tt , l) = {!!}
-- -- proj₁ (SF-F-super S X) (node σ ts) (i , (q , tt , eq) , k , tt , l) = {!!}
-- -- proj₂ (SF-F-super S X) d i = {!!}




-- --Properties of the signature
-- Sig-Thin : Sig → Set
-- Sig-Thin (S , ar) = (op : S) → (i j : ar op) → i ≡ j 

-- Sig-Full : Sig → Set
-- Sig-Full (S , ar) = (op : S) → (ar op)

-- Sig-Line : Sig → Set
-- Sig-Line S = Sig-Thin S × Sig-Full S


-- -- Decidably empty
-- Sig-DE : Sig → Set
-- Sig-DE (S , ar) = (σ : S) → (ar σ → ⊥) ⊎ ar σ 

-- TSig : (A E : Set) → Sig
-- TSig A E = (A ⊎ E) , (λ { (inj₁ a) → ⊤ ; (inj₂ e) → ⊥})

-- TSig-Thin : (A E : Set) → Sig-Thin (TSig A E)
-- TSig-Thin A E (inj₁ a) tt tt = refl
-- TSig-Thin A E (inj₂ e) ()


-- Sig-DE-Act : (S : Sig) → (Sig-DE S) → Set
-- Sig-DE-Act (S , ar) S-DE = (Σ S λ σ → [_,_]′ (λ x → ⊥) (λ x → ⊤) (S-DE σ))
-- Sig-DE-Err : (S : Sig) → (Sig-DE S) → Set
-- Sig-DE-Err (S , ar) S-DE = (Σ S λ σ → [_,_]′ (λ x → ⊤) (λ x → ⊥) (S-DE σ))

-- Sig-DE-Sig : (S : Sig) → (Sig-DE S) → Sig
-- Sig-DE-Sig S S-DE = (Sig-DE-Act S S-DE ⊎ Sig-DE-Err S S-DE) ,
--   (λ {(inj₁ x) → ⊤ ; (inj₂ y) → ⊥})

-- Sig-Bij : Sig → Sig → Set
-- Sig-Bij (S , ar) (Z , br) = Σ (S → Z) λ f → Σ (Z → S) λ g →
--   (((x : S) → g (f x) ≡ x) × ((y : Z) → f (g y) ≡ y))
--   × ((x : S) → Σ (ar x → br (f x)) λ v → Σ (br (f x) → ar x) λ w →
--     ((i : ar x) → w (v i) ≡ i) × ((i : br (f x)) → v (w i) ≡ i))





-- open import Slice-Functions.Monoidal

-- -- Strength of Free Monads
-- SF-F-σ : (S : Sig) → (X Y : Set) → SF ((Free S X) × Y) (Free S (X × Y))
-- SF-F-σ S X Y = SF-Fun (Free-σ S X Y)



-- -- Naturality is dependent on subcategory and signature
-- SF-F-σ-nat< : (S : Sig) → {X X' Y Y' : Set}
--   → (f : SF X X') → (g : SF Y Y')
--   → SF≤ (SF-∘ (SF-F S f ⊗ g) (SF-F-σ S X' Y')) (SF-∘ (SF-F-σ S X Y) (SF-F S (f ⊗ g)))
-- SF-F-σ-nat< S f g (leaf x , y) ((i , j) , tt) = (tt , (i , j)) , refl
-- SF-F-σ-nat< S f g (node σ ts , y) ((ip , j) , tt) =
--   (tt , (λ i → proj₂ (proj₁ (SF-F-σ-nat< S f g (ts i , y) ((ip i , j) , tt))))) ,
--   (cong (node σ)
--   (fun-ext (λ i → (proj₂ (SF-F-σ-nat< S f g (ts i , y) ((ip i , j) , tt))))))



-- SF-F-Line-σ-nat> : (S : Sig) → (Sig-Line S) → {X X' Y Y' : Set}
--   → (f : SF X X') → (g : SF Y Y')
--   → SF≤ (SF-∘ (SF-F-σ S X Y) (SF-F S (f ⊗ g))) (SF-∘ (SF-F S f ⊗ g) (SF-F-σ S X' Y'))
-- SF-F-Line-σ-nat> S SLine f g (leaf x , y) (tt , p) = (p , tt) , refl
-- SF-F-Line-σ-nat> S (S-Thin , S-Full) f g (node σ ts , y) (tt , p)
--  = (((λ i → proj₁ (proj₁ (proj₁ (SF-F-Line-σ-nat> S (S-Thin , S-Full) f g (ts i , y)
--            (tt , p i))))) ,
--    proj₂ (proj₁ (proj₁ (SF-F-Line-σ-nat> S (S-Thin , S-Full) f g (ts (S-Full σ) , y)
--            (tt , p (S-Full σ)))))) ,
--    tt) ,
--    cong (node σ) (fun-ext (λ i →
--    trans
--      (cong (λ w → proj₂ (Free-P S (Free-σ S _ _ (ts w , y)) (f ⊗ g)) (p w))
--                         (S-Thin σ i (S-Full σ)))
--    (trans
--      (proj₂ (SF-F-Line-σ-nat> S (S-Thin , S-Full) f g (ts (S-Full σ) , y)
--                         (tt , p (S-Full σ))))
--      (cong₂ (λ r z → Free-σ S _ _ (r , z))
--             (cong (λ j → proj₂ (Free-P S (ts j) f)
--       (proj₁ (proj₁ (proj₁ (SF-F-Line-σ-nat> S (S-Thin , S-Full) f g (ts j , y)
--           (tt , p j)))))) (sym (S-Thin σ i (S-Full σ)))) refl))))
-- -- Above proof is a bit cumbersome, due to concrete unfoldings necessary to appease Agda's
-- -- termination checker. It just uses that we have a choice of arity of σ in the form of
-- -- S-Full σ, which due to S-Thin is equal to any other index


-- -- For the next result, we need to be able to decidably determine whether the arity is
-- -- empty or not, and do an inductive case distinction. So instead, we use the Thin Signature
-- -- representation in terms of sets A and E
-- SF-F-Thin-σ-T-nat> : (A E : Set) → {X X' Y Y' : Set}
--   → (f : SF X X') → (g : SF Y Y') → (SF-Total g)
--   → SF≤ (SF-∘ (SF-F-σ (TSig A E) X Y) (SF-F (TSig A E) (f ⊗ g)))
--           (SF-∘ (SF-F (TSig A E) f ⊗ g) (SF-F-σ (TSig A E) X' Y'))
-- SF-F-Thin-σ-T-nat> A E f g g-tot (leaf x , y) (tt , p) = (p , tt) , refl
-- SF-F-Thin-σ-T-nat> A E f g g-tot (node (inj₁ a) ts , y) (tt , p) =
--   (((λ i →  proj₁ (proj₁ (proj₁ (SF-F-Thin-σ-T-nat> A E f g g-tot (ts i , y)
--            (tt , p i))))) ,
--   proj₂ (proj₁ (proj₁ (SF-F-Thin-σ-T-nat> A E f g g-tot (ts tt , y)
--            (tt , p tt))))) ,
--   tt) , cong (node (inj₁ a)) (fun-ext
--     (λ i → proj₂ (SF-F-Thin-σ-T-nat> A E f g g-tot (ts i , y) (tt , p i))))
-- SF-F-Thin-σ-T-nat> A E f g g-tot (node (inj₂ e) ts , y) (tt , p) =
--   (((λ {()}) , g-tot y) , tt) , cong (node (inj₂ e)) (fun-ext (λ {()}))




-- SF-F-Full-σ-O-nat> : (S : Sig) → (Sig-Full S) → {X X' Y Y' : Set}
--   → (f : SF X X') → (g : SF Y Y') → (SF-Onele g)
--   → SF≤ (SF-∘ (SF-F-σ S X Y) (SF-F S (f ⊗ g))) (SF-∘ (SF-F S f ⊗ g) (SF-F-σ S X' Y'))
-- SF-F-Full-σ-O-nat> S S-Full f g g-one (leaf x , y) (tt , p) = (p , tt) , refl
-- SF-F-Full-σ-O-nat> S S-Full f g g-one (node σ ts , y) (tt , p) =
--   (((λ i → proj₁ (proj₁ (proj₁ (SF-F-Full-σ-O-nat> S S-Full f g g-one (ts i , y)
--            (tt , p i))))) ,
--   ( proj₂ (proj₁ (proj₁ (SF-F-Full-σ-O-nat> S S-Full f g g-one (ts (S-Full σ) , y)
--            (tt , p (S-Full σ))))))) , tt) ,
--   (cong (node σ) (fun-ext (λ i → trans
--         (proj₂ (SF-F-Full-σ-O-nat> S S-Full f g g-one (ts i , y) (tt , p i)))
--                (cong₂ (λ a b → Free-σ S _ _ (a , b))
--                refl (g-one y _ _)))))


-- SF-F-σ-Fun-nat> : (S : Sig) → {X X' Y Y' : Set}
--   → (f : SF X X') → (g : Y → Y') 
--   → SF≤ (SF-∘ (SF-F-σ S X Y) (SF-F S (f ⊗ (SF-Fun g))))
--           (SF-∘ (SF-F S f ⊗ (SF-Fun g)) (SF-F-σ S X' Y'))
-- SF-F-σ-Fun-nat> S f g (leaf x , y) (tt , p) = (p , tt) , refl
-- SF-F-σ-Fun-nat> S f g (node σ ts , y) (tt , p) =
--   (((λ i → proj₁ (proj₁ (proj₁ (SF-F-σ-Fun-nat> S f g (ts i , y) (tt , p i))))) , tt) ,
--   tt) , (cong (node σ) (fun-ext
--   (λ i → proj₂ (SF-F-σ-Fun-nat> S f g (ts i , y) (tt , p i)))))
