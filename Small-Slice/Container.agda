module Small-Slice.Container where

open import Data.Unit
open import Data.Empty
open import Data.Sum renaming (map to map⊎)
open import Data.Nat hiding (_⊔_)
open import Data.Product renaming (map to map×)
open import Relation.Binary.Core

open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Binary.Structures
open import Relation.Binary.Definitions

open import Small-Slice.Univ
open import Small-Slice.ND-functions

open import Extensionality


-- Container Monad
𝕌-Sig : Set₁
𝕌-Sig = Σ Set λ A → A → 𝕌


data Free (S : 𝕌-Sig) (X : Set) : Set where
  leaf : X → Free S X
  node : (σ : proj₁ S) → (ts : 𝕌S (proj₂ S σ) → Free S X) → Free S X



Pos : (S : 𝕌-Sig) → (X : Set) → (X → 𝕌) → Free S X → 𝕌
Pos S X f (leaf x) = f x
Pos S X f (node σ ts) = 𝕌Π (proj₂ S σ , λ i → Pos S X f (ts i))


Pos-In : (S : 𝕌-Sig) → (X : Set) → (f : X → 𝕌) → (t : Free S X) →
  (g : (x : X) → 𝕌S (f x)) → 𝕌S (Pos S X f t)
Pos-In S X f (leaf x) g = g x
Pos-In S X f (node σ ts) g c = Pos-In S X f (ts c) g


Free-P : (S : 𝕌-Sig) → {X Y : Set} → Free S X → (𝕌Hom X Y) → 𝕌SL (Free S Y)
proj₁ (Free-P S {X} {Y} t p) = Pos S X (λ x → proj₁ (p x)) t
proj₂ (Free-P S {X} {Y} (leaf x) p) i = leaf (proj₂ (p x) i)
proj₂ (Free-P S {X} {Y} (node σ ts) p) i =
  node σ (λ b → proj₂ (Free-P S {X} {Y} (ts b) p) (i b))

SF-F : (S : 𝕌-Sig) → {X Y : Set} → 𝕌Hom X Y → 𝕌Hom (Free S X) (Free S Y)
SF-F S f t = Free-P S t f

-- Completeness and soundness
data Free-dist (S : 𝕌-Sig) {X Y : Set} (f : X → 𝕌SL Y) : Free S X → Free S Y → Set where
  FD-leaf : (x : X) → (i : 𝕌S (proj₁ (f x))) → Free-dist S f (leaf x) (leaf (proj₂ (f x) i))
  FD-node : (σ : proj₁ S) → (ts : 𝕌S (proj₂ S σ) → Free S X)
    → (rs : 𝕌S (proj₂ S σ) → Free S Y)
    → ((i : 𝕌S (proj₂ S σ)) → Free-dist S f (ts i) (rs i))
    → Free-dist S f (node σ ts) (node σ rs)

FD-complete : (S : 𝕌-Sig) → {X Y : Set} → (t : Free S X) → (f : X → 𝕌SL Y)
  → (r : Free S Y) → Free-dist S f t r → 𝕌SL-∈ {Free S Y} r (Free-P S t f)
proj₁ (FD-complete S (leaf x) f .(leaf (proj₂ (f x) i)) (FD-leaf .x i)) = i
proj₁ (FD-complete S (node σ ts) f .(node σ rs) (FD-node .σ .ts rs x)) c =
  proj₁ (FD-complete S (ts c) f (rs c) (x c)) 
proj₂ (FD-complete S (leaf x) f .(leaf (proj₂ (f x) i)) (FD-leaf .x i)) = refl
proj₂ (FD-complete S (node σ ts) f .(node σ rs) (FD-node .σ .ts rs x)) = cong (node σ) (fun-ext (λ c →
  proj₂ (FD-complete S (ts c) f (rs c) (x c)) ))

FD-sound : (S : 𝕌-Sig) → {X Y : Set} → (t : Free S X) → (f : X → 𝕌SL Y)
  → (r : Free S Y) → 𝕌SL-∈ {Free S Y} r (Free-P S t f) → Free-dist S f t r
FD-sound S (leaf x) f .(leaf (proj₂ (f x) i)) (i , refl) = FD-leaf x i
FD-sound S (node σ ts) f .(node σ (λ b → proj₂ (Free-P S (ts b) f) (i b))) (i , refl) =
  FD-node σ ts (λ b → proj₂ (Free-P S (ts b) f) (i b)) λ j →
    FD-sound S (ts j) f (proj₂ (Free-P S (ts j) f) (i j)) ((i j) , refl)


-- Functorial properties
SF-F-id : (S : 𝕌-Sig) → (X : Set) → 𝕌Hom-≡ (SF-F S (𝕌Hom-id X)) (𝕌Hom-id (Free S X))
proj₁ (SF-F-id S X) (leaf x) i = tt , refl
proj₁ (SF-F-id S X) (node σ ts) i = tt ,
  cong (node σ) (fun-ext λ b → proj₂ (proj₁ (SF-F-id S X) (ts b) (i b)))
proj₂ (SF-F-id S X) (leaf x) tt = tt , refl
proj₂ (SF-F-id S X) (node σ ts) tt = (λ b → proj₁ (proj₂ (SF-F-id S X) (ts b) tt)) ,
  cong (node σ) (fun-ext (λ b → proj₂ (proj₂ (SF-F-id S X) (ts b) tt)))

SF-F-∘ : (S : 𝕌-Sig) → {X Y Z : Set} → (f : 𝕌Hom X Y) → (g : 𝕌Hom Y Z)
  → 𝕌Hom-≡ (SF-F S (𝕌Hom-∘ g f)) (𝕌Hom-∘ (SF-F S g) (SF-F S f))
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



Free-μ : (S : 𝕌-Sig) → (X : Set) → Free S (Free S X) → Free S X
Free-μ S X (leaf t) = t
Free-μ S X (node σ ts) = node σ (λ i → Free-μ S X (ts i))


𝕌Free-η : (S : 𝕌-Sig) → (X : Set) → 𝕌Hom X (Free S X)
𝕌Free-η S X x = 𝕌SL-η (leaf x)

𝕌Free-μ : (S : 𝕌-Sig) → (X : Set) → 𝕌Hom (Free S (Free S X)) (Free S X)
𝕌Free-μ S X d = 𝕌SL-η (Free-μ S X d)

𝕌Free-ε : (S : 𝕌-Sig) → (X : Set) → 𝕌Hom (Free S X) X
𝕌Free-ε S X (leaf x) = 𝕌SL-η x
𝕌Free-ε S X (node σ ts) = 𝕌SL-⊥

𝕌Free-δ : (S : 𝕌-Sig) → (X : Set) → 𝕌Hom (Free S X) (Free S (Free S X))
𝕌Free-δ S X (leaf x) = 𝕌SL-η (leaf (leaf x))
proj₁ (𝕌Free-δ S X (node σ ts)) = 𝕌⊎ 𝕌⊤ (𝕌Π (proj₂ S σ , λ i → proj₁ (𝕌Free-δ S X (ts i))))
proj₂ (𝕌Free-δ S X (node σ ts)) (inj₁ tt) = leaf (node σ ts)
proj₂ (𝕌Free-δ S X (node σ ts)) (inj₂ C) = node σ (λ i → proj₂ (𝕌Free-δ S X (ts i)) (C i))


𝕌Free-χ : (S : 𝕌-Sig) → (X : Set) → 𝕌Hom (Free S (Free S X)) (Free S (Free S X))
𝕌Free-χ S X = 𝕌Hom-∘ (𝕌Free-δ S X) (𝕌Free-μ S X)



open import Small-Slice.Substructure


𝕌Free-η-ε-† : (S : 𝕌-Sig) → (X : Set) → 𝕌-is-† (𝕌Free-η S X) (𝕌Free-ε S X)
proj₁ (𝕌Free-η-ε-† S X) x tt = tt , refl
proj₂ (𝕌Free-η-ε-† S X) (leaf x) tt = tt , refl


𝕌Free-μ-δ-† : (S : 𝕌-Sig) → (X : Set) → 𝕌-is-† (𝕌Free-μ S X) (𝕌Free-δ S X)
proj₁ (𝕌Free-μ-δ-† S X) (leaf (leaf x)) i = tt , refl
proj₁ (𝕌Free-μ-δ-† S X) (leaf (node σ ts)) i = (inj₁ tt) , refl
proj₁ (𝕌Free-μ-δ-† S X) (node σ ts) tt = inj₂ (λ i → proj₁ (proj₁ (𝕌Free-μ-δ-† S X) (ts i) tt)) ,
      cong (node σ) (fun-ext (λ i → proj₂ (proj₁ (𝕌Free-μ-δ-† S X) (ts i) tt)))
proj₂ (𝕌Free-μ-δ-† S X) (leaf x) tt = tt , refl
proj₂ (𝕌Free-μ-δ-† S X) (node σ ts) (inj₁ tt) = tt , refl
proj₂ (𝕌Free-μ-δ-† S X) (node σ ts) (inj₂ C) = tt ,
      cong (node σ) (fun-ext (λ i → proj₂ (proj₂ (𝕌Free-μ-δ-† S X) (ts i) (C i))))

𝕌Free-eq-με : (S : 𝕌-Sig) → (X : Set)
  → 𝕌Hom-≡ (𝕌Hom-∘ (𝕌Free-ε S X) (𝕌Free-μ S X)) (𝕌Hom-∘ (𝕌Free-ε S X) (𝕌Free-ε S (Free S X)))
proj₁ (𝕌Free-eq-με S X) (leaf (leaf x)) (tt , tt) = (tt , tt) , refl
proj₂ (𝕌Free-eq-με S X) (leaf (leaf x)) (tt , tt) = (tt , tt) , refl

𝕌Free-eq-ηε : (S : 𝕌-Sig) → (X : Set)
  → 𝕌Hom-≡ (𝕌Hom-∘ (𝕌Free-ε S X) (𝕌Free-η S X)) (𝕌Hom-id X )
𝕌Free-eq-ηε S X = (λ x i → tt , refl) , (λ x i → (tt , tt) , refl)


𝕌Free-eq-δμ : (S : 𝕌-Sig) → (X : Set)
  → 𝕌Hom-≡ (𝕌Hom-∘ (𝕌Free-μ S X) (𝕌Free-δ S X)) (𝕌Hom-id (Free S X))
proj₁ (𝕌Free-eq-δμ S X) (leaf x) _ = tt , refl
proj₁ (𝕌Free-eq-δμ S X) (node σ ts) (inj₁ tt , tt) = tt , refl
proj₁ (𝕌Free-eq-δμ S X) (node σ ts) (inj₂ H , tt) = tt ,
  cong (node σ) (dep-ext (λ i → proj₂ (proj₁ (𝕌Free-eq-δμ S X) (ts i) ((H i) , tt))))
proj₂ (𝕌Free-eq-δμ S X) (leaf x) tt = (tt , tt) , refl
proj₂ (𝕌Free-eq-δμ S X) (node σ ts) tt = ((inj₁ tt) , tt) , refl

𝕌Free-η<δ : (S : 𝕌-Sig) → (X : Set) → 𝕌Hom-⊂ (𝕌Free-η S (Free S X)) (𝕌Free-δ S X)
𝕌Free-η<δ S X (leaf x) tt = tt , refl
𝕌Free-η<δ S X (node σ ts) tt = (inj₁ tt) , refl

𝕌Free-eq-<>< : (S : 𝕌-Sig) → (X : Set)
  → 𝕌Hom-≡ (𝕌Hom-∘ (𝕌Hom-∘ (𝕌Free-μ S (Free S X)) (SF-F S (𝕌Free-χ S X))) (𝕌Free-δ S (Free S X))) (𝕌Free-χ S X)
proj₁ (𝕌Free-eq-<>< S X) (leaf t) (tt , (tt , j) , tt) = (tt , j) , refl
proj₁ (𝕌Free-eq-<>< S X) (node σ ds) (inj₁ tt , (tt , j) , tt) = (tt , j) , refl
proj₁ (𝕌Free-eq-<>< S X) (node σ ds) (inj₂ i , j , tt) = (tt , (inj₂ (λ k →
  proj₂ (proj₁ (proj₁ (𝕌Free-eq-<>< S X) (ds k) ((i k) , ((j k) , tt))))))) ,
  cong (node σ) (dep-ext (λ k → proj₂ (proj₁ (𝕌Free-eq-<>< S X) (ds k) ((i k) , ((j k) , tt)))))
proj₂ (𝕌Free-eq-<>< S X) (leaf t) (tt , i) = (tt , ((tt , i) , tt)) , refl
proj₂ (𝕌Free-eq-<>< S X) (node σ ds) (tt , i) = ((inj₁ tt) , ((tt , i) , tt)) , refl

--𝕌Free-eq-><> : (S : 𝕌-Sig) → (X : Set)
--  → 𝕌Hom-≡ (𝕌Hom-∘ (𝕌Hom-∘ (SF-F S (𝕌Free-μ S X)) (𝕌Free-χ S (Free S X))) (SF-F S (𝕌Free-δ S X))) (𝕌Free-χ S X)
--proj₁ (𝕌Free-eq-><> S X) (leaf (leaf x)) (tt , (tt , tt) , tt) = (tt , tt) , refl
--proj₁ (𝕌Free-eq-><> S X) (leaf (node σ ts)) (inj₁ tt , (tt , tt) , tt) = (tt , (inj₁ tt)) , refl
--proj₁ (𝕌Free-eq-><> S X) (leaf (node σ ts)) (inj₂ i , (tt , inj₁ tt) , tt) = (tt , (inj₁ tt)) ,
--  cong (λ z → leaf (node σ z)) (dep-ext (λ u → proj₂ (proj₁ (𝕌Free-eq-δμ S X) (ts u) ((i u) , tt)) ))
--proj₁ (𝕌Free-eq-><> S X) (leaf (node σ ts)) (inj₂ i , (tt , inj₂ j) , k) = (tt , (inj₂ (λ u →
--  proj₂ (proj₁ (proj₁ (𝕌Free-eq-><> S X) (leaf (ts u)) ((i u) , ((tt , j u) , k u))))))) ,
--  cong (node σ) (dep-ext (λ u → proj₂ (proj₁ (𝕌Free-eq-><> S X) (leaf (ts u)) ((i u) , ((tt , j u) , k u)))))
--proj₁ (𝕌Free-eq-><> S X) (node σ ds) (i , (tt , inj₁ tt) , tt) = (tt , (inj₁ tt)) , (cong (λ z → leaf (node σ z))
--  (dep-ext (λ u → {!proj₂ (proj₁ (𝕌Free-eq-><> S X) (ds u) (i u , (tt , ?) , ?))!})))
--proj₁ (𝕌Free-eq-><> S X) (node σ ds) (i , (tt , inj₂ y) , k) = {!!}
--proj₂ (𝕌Free-eq-><> S X) = {!!}
