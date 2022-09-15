module Runner.Trace-Runner where

open import Data.Unit
open import Data.Empty
open import Data.Sum renaming (map to map⊎)
open import Data.Nat hiding (_⊔_)
open import Data.Product renaming (map to map×)
open import Relation.Binary.PropositionalEquality hiding ([_])


open import Slice.Base

open import Slice-Functions.Base
open import Slice-Functions.Subcategories
open import Slice-Functions.Monoidal

open import Monads.Trace




cur : {X Y : Set} → {Z : Set₁} → (X → Y → Z) → (X × Y → Z)
cur f (x , y) = f x y


Trace-⊥-dec : (A E X : Set) → (Trace A E ⊥) → (Trace A E X)
Trace-⊥-dec A E X (act a t) = act a (Trace-⊥-dec A E X t)
Trace-⊥-dec A E X (err e) = err e

Trace-⊥ : (A E X : Set) → SF (Trace A E ⊥) (Trace A E X)
Trace-⊥ A E X = SF-Fun (Trace-⊥-dec A E X)


Trace-⊥-nat : (A E : Set) → {X Y : Set} → (f : SF X Y)
  → SF≡ (Trace-⊥ A E Y) (SF-∘ (Trace-⊥ A E X) (SF-T A E f))
proj₁ (Trace-⊥-nat A E f) (act a t) tt with proj₁ (Trace-⊥-nat A E f) t tt
... | (tt , u) , v = (tt , u) , (cong (act a) v)
proj₁ (Trace-⊥-nat A E f) (err e) tt = (tt , tt) , refl
proj₂ (Trace-⊥-nat A E f) (act a t) (tt , j) with proj₂ (Trace-⊥-nat A E f) t (tt , j)
... | tt , v = tt , (cong (act a) v)
proj₂ (Trace-⊥-nat A E f) (err e) (tt , tt) = tt , refl


-- Trace runner and its properties
Runner-map : (A E B F K : Set) → Set₁
Runner-map A E B F K = (X : Set) → K → SF (Trace A E X) (Trace B F (K × X))

Runner-map-Total : {A E A' E' : Set} → (K : Set) → (Runner-map A E A' E' K) → Set₁
Runner-map-Total K ϕ = (X : Set) → (k : K) → SF-Total (ϕ X k)

Runner-map-T-nat : {A E A' E' : Set} → (K : Set) → (Runner-map A E A' E' K) → Set₁
Runner-map-T-nat K ϕ = {X Y : Set} → (f : SF X Y) → SF-Total f → (k : K)
  → SF≡ (SF-∘ (SF-T _ _ f) (ϕ Y k))
          (SF-∘ (ϕ X k) (SF-T _ _ (SF-id K ⊗ f)))

Runner-map-S-nat : {A E A' E' : Set} → (K : Set) → (Runner-map A E A' E' K) → Set₁
Runner-map-S-nat K ϕ = {X Y : Set} → (f : X → Y) → (k : K)
  → SF≡ (λ t → (ϕ Y k (Trace-map _ _ f t)))
         (λ t → SL-fun (Trace-map _ _ (λ p → proj₁ p , f (proj₂ p))) (ϕ X k t))

Runner-map-η : {A E A' E' : Set} → (K : Set) → (Runner-map A E A' E' K) → Set₁
Runner-map-η K ϕ = (X : Set) → (k : K)
  → SF≡ (SF-∘ (SF-T-η _ _ X) (ϕ X k))
         (SF-∘ (SF-Fun (λ x → (k , x))) (SF-T-η _ _ (K × X)))

Runner-map-μ : {A E A' E' : Set} → (K : Set) → (Runner-map A E A' E' K) → Set₁
Runner-map-μ K ϕ = (X : Set) → (k : K)
  → SF≡ (SF-∘ (SF-T-μ _ _ X) (ϕ X k))
         (SF-∘ (ϕ (Trace _ _ X) k)
               (SF-∘ (SF-T _ _ (cur (ϕ X))) (SF-T-μ _ _ (K × X))))

Runner-map-κ : {A E A' E' : Set} → (K : Set) → (Runner-map A E A' E' K) → Set₁
Runner-map-κ K ϕ = (X Y : Set) → (t : Trace _ _ X) → (f : X → Trace _ _ Y)
  → (k : K)
  → SL→ (Trace _ _ (K × Y)) (ϕ Y k (Trace-κ _ _ X Y f t))
           (SL-* {Trace _ _ (K × X)} {Trace _ _ (K × Y)}
                  (SF-T-κ (K × X) (K × Y) (λ p → cur (ϕ Y) (proj₁ p , f (proj₂ p))))
                                          (ϕ X k t))



Runner-map-trans : {A E : Set} → (K : Set) → (Runner-map A E ⊥ ⊤ K) → Set₁
Runner-map-trans K ϕ = {X Y : Set} → (f : X → Y) → (k : K) → (t : Trace _ _ X)
  → Σ (proj₁ (ϕ X k t) → proj₁ (ϕ Y k (Trace-map _ _ f t)))
    λ π → (i : proj₁ (ϕ X k t)) → (u : K) → (x : X) → proj₂ (ϕ X k t) i ≡ ret (u , x)
    → proj₂ (ϕ Y k (Trace-map _ _ f t)) (π i) ≡ ret (u , f x)

Runner-map-trans2 : {A E : Set} → (K : Set) → (Runner-map A E ⊥ ⊤ K) → Set₁
Runner-map-trans2 K ϕ = {X Y : Set} → (f : X → Y) → (k : K) → (t : Trace _ _ X)
  → Σ (proj₁ (ϕ Y k (Trace-map _ _ f t)) → proj₁ (ϕ X k t))
    λ π → (i : proj₁ (ϕ Y k (Trace-map _ _ f t)))
    → (u : K) → (y : Y) → proj₂ (ϕ Y k (Trace-map _ _ f t)) i ≡ ret (u , y)
    → Σ X λ x → f x ≡ y × proj₂ (ϕ X k t) (π i) ≡ ret (u , x)




-- Local definition of a runner
Trace-Runner : (A E B F K : Set) → Set₁
Trace-Runner A E B F K = (A → SF K (Trace B F K)) × (E → SF K (Trace B F ⊥))

TR-Total : {A E B F K : Set} → Trace-Runner A E B F K → Set
TR-Total (θ₁ , θ₂) = ((a : _) → SF-Total (θ₁ a)) × ((e : _) → SF-Total (θ₂ e))


TR-map : {A E B F : Set} → (K : Set) → (θ : Trace-Runner A E B F K)
  → (X : Set) → K → SF (Trace A E X) (Trace B F (K × X))
TR-map-act : {A E B F : Set} → (K : Set) → (θ : Trace-Runner A E B F K)
  → (X : Set) → Trace B F K → SF (Trace A E X) (Trace B F (K × X))
TR-map K θ X k (ret x) = SF-id _ (ret (k , x))
TR-map K θ X k (act a t) = SL-* 
  (λ r → TR-map-act K θ X r t) (proj₁ θ a k) 
TR-map K θ X k (err e) = SL-* (Trace-⊥ _ _ (K × X)) (proj₂ θ e k)
TR-map-act K θ X (ret k) = TR-map K θ X k
TR-map-act K θ X (act a r) t = SL-act a (K × X) (TR-map-act K θ X r t)
TR-map-act K θ X (err e) t = SF-id _ (err e)


TR-map-Total : {A E B F : Set} → (K : Set) → (θ : Trace-Runner A E B F K)
  → TR-Total θ → Runner-map-Total K (TR-map K θ)
TR-map-act-Total : {A E B F : Set} → (K : Set) → (θ : Trace-Runner A E B F K)
  → TR-Total θ → (X : Set) → (r : Trace B F K) → SF-Total (TR-map-act K θ X r)
TR-map-Total K θ θ-tot X k (ret x) = tt
TR-map-Total K θ θ-tot X k (act a t) = (proj₁ θ-tot a k) ,
  TR-map-act-Total K θ θ-tot X  (proj₂ (proj₁ θ a k) (proj₁ θ-tot a k)) t
TR-map-Total K θ θ-tot X k (err e) = (proj₂ θ-tot e k) , tt
TR-map-act-Total K θ θ-tot X (ret k) t = TR-map-Total K θ θ-tot X k t
TR-map-act-Total K θ θ-tot X (act a r) t = TR-map-act-Total K θ θ-tot X r t
TR-map-act-Total K θ θ-tot X (err e) t = tt


TR-map-nat< : {A E A' E' : Set} → (K : Set) → (θ : Trace-Runner A E A' E' K)
  → {X Y : Set} → (f : SF X Y) → (k : K)
  → SF≤ (SF-∘ (SF-T A E f) (TR-map K θ Y k))
          (SF-∘ (TR-map K θ X k) (SF-T A' E' (SF-id K ⊗ f)))
TR-map-nat<-act : {A E A' E' : Set} → (K : Set) → (θ : Trace-Runner A E A' E' K)
  → {X Y : Set} → (f : SF X Y) → (r : Trace A' E' K)
  → SF≤ (SF-∘ (SF-T A E f) (TR-map-act K θ Y r))
          (SF-∘ (TR-map-act K θ X r) (SF-T A' E' (SF-id K ⊗ f)))
TR-map-nat< K θ f k (ret x) (i , tt) = (tt , (tt , i)) , refl
TR-map-nat< K θ f k (act a t) (i , j , p) with proj₁ θ a k
...| u , v = ((j ,
  (proj₁ (proj₁ (TR-map-nat<-act K θ f (v j) t (i , p))))) ,
  (proj₂ (proj₁ (TR-map-nat<-act K θ f (v j) t (i , p))))) ,
  (proj₂ (TR-map-nat<-act K θ f (v j) t (i , p)))
TR-map-nat< K θ f k (err e) (tt , j , tt) with proj₂ θ e k
... | u , v = ((j , tt) ,
  (proj₂ (proj₁ (proj₁ (Trace-⊥-nat _ _ (SF-id K ⊗ f)) (v j) tt)))) ,
  (proj₂ (proj₁ (Trace-⊥-nat _ _ (SF-id K ⊗ f)) (v j) tt))
TR-map-nat<-act K θ f (ret k) t (i , j) = TR-map-nat< K θ f k t (i , j)
TR-map-nat<-act K θ f (act a r) t (i , j) with TR-map-nat<-act K θ f r t (i , j)
... | (u , v) , w = (u , v) , (cong (act a) w)
TR-map-nat<-act K θ f (err e) t (i , tt) = (tt , tt) , refl


TR-map-T-nat> : {A E A' E' : Set} → (K : Set) → (θ : Trace-Runner A E A' E' K)
  → {X Y : Set} → (f : SF X Y) → (SF-Total f) → (k : K)
  → SF≤ (SF-∘ (TR-map K θ X k) (SF-T A' E' (SF-id K ⊗ f)))
          (SF-∘ (SF-T A E f) (TR-map K θ Y k))
TR-map-T-nat>-act : {A E A' E' : Set} → (K : Set) → (θ : Trace-Runner A E A' E' K)
  → {X Y : Set} → (f : SF X Y) → (SF-Total f) → (r : Trace A' E' K)
  → SF≤ (SF-∘ (TR-map-act K θ X r) (SF-T A' E' (SF-id K ⊗ f)))
          (SF-∘ (SF-T A E f) (TR-map-act K θ Y r))
TR-map-T-nat> K θ f f-tot k (ret x) (tt , tt , i) = (i , tt) , refl
TR-map-T-nat> K θ f f-tot k (act a t) ((i , j) , p) with proj₁ θ a k
... | u , v = (proj₁ (proj₁ (TR-map-T-nat>-act K θ f f-tot (v i) t (j , p))) ,
  i , proj₂ (proj₁ (TR-map-T-nat>-act K θ f f-tot (v i) t (j , p)))) ,
  proj₂ (TR-map-T-nat>-act K θ f f-tot (v i) t (j , p))
TR-map-T-nat> K θ f f-tot k (err e) ((i , tt) , j) with proj₂ θ e k
... | u , v = (tt , (i , tt)) ,
  (proj₂ (proj₂ (Trace-⊥-nat _ _ (SF-id K ⊗ f)) (v i) (tt , j)))
TR-map-T-nat>-act K θ f f-tot (ret k) t (i , j) = TR-map-T-nat> K θ f f-tot k t (i , j)
TR-map-T-nat>-act K θ f f-tot (act a r) t (i , j)
  with TR-map-T-nat>-act K θ f f-tot r t (i , j)
... | u , v = u , cong (act a) v
TR-map-T-nat>-act K θ f f-tot (err e) t (tt , tt) = (SF-T-Total _ _ f f-tot t , tt) , refl


TR-map-T-nat : {A E B F : Set} → (K : Set) → (θ : Trace-Runner A E B F K)
  → TR-Total θ → Runner-map-T-nat K (TR-map K θ)
TR-map-T-nat K θ θ-tot f f-tot k = TR-map-nat< K θ f k , TR-map-T-nat> K θ f f-tot k



TR-map-η : {A E A' E' : Set} → (K : Set) → (θ : Trace-Runner A E A' E' K)
  → Runner-map-η K (TR-map K θ)
proj₁ (TR-map-η S θ X s) x i = (tt , tt) , refl
proj₂ (TR-map-η S θ X s) x i = (tt , tt) , refl




Trace-⊥-μ : (A E X : Set) → (t : Trace A E ⊥)
  → Trace-⊥-dec A E X t ≡
      Trace-μ A E X (Trace-⊥-dec A E (Trace A E X) t)
Trace-⊥-μ A E X (act a t) = cong (act a) (Trace-⊥-μ A E X t)
Trace-⊥-μ A E X (err e) = refl


TR-map-μ : {A E A' E' : Set} → (K : Set) → (θ : Trace-Runner A E A' E' K)
  → Runner-map-μ K (TR-map K θ)
TR-map-act-μ : {A E A' E' : Set} → (K : Set) → (θ : Trace-Runner A E A' E' K)
  → (X : Set) → (r : Trace A' E' K)
  → SF≡ (SF-∘ (SF-T-μ A E X) (TR-map-act K θ X r))
         (SF-∘ (TR-map-act K θ (Trace A E X) r)
               (SF-∘ (SF-T A' E' (cur (TR-map K θ X))) (SF-T-μ A' E' (K × X))))
proj₁ (TR-map-μ K θ X k) (ret t) (tt , i) = (tt , (i , tt)) , refl
proj₁ (TR-map-μ K θ X k) (act a d) (tt , i , j) with proj₁ θ a k
... | u , v = ((i , (proj₁ (proj₁ (proj₁ (TR-map-act-μ K θ X (v i)) d (tt , j))))) ,
  (proj₂ (proj₁ (proj₁ (TR-map-act-μ K θ X (v i)) d (tt , j))))) ,
  proj₂ (proj₁ (TR-map-act-μ K θ X (v i)) d (tt , j))
proj₁ (TR-map-μ K θ X k) (err e) (tt , i , tt) with proj₂ θ e k
... | u , v = ((i , tt) ,
  (proj₂ (proj₁ (proj₁ (Trace-⊥-nat _ _ (cur (TR-map K θ X))) (v i) tt)) , tt)) ,
  trans (Trace-⊥-μ _ _ (K × X) (v i))
  (cong (Trace-μ _ _ (Σ K (λ x → X)))
  (proj₂ (proj₁ (Trace-⊥-nat _ _ (cur (TR-map K θ X))) (v i) tt)))

proj₂ (TR-map-μ K θ X k) (ret t) (tt , i , tt) = (tt , i) , refl
proj₂ (TR-map-μ K θ X k) (act a d) ((i , j) , p , tt) with proj₁ θ a k
... | u , v = (tt , (i ,
  ((proj₂ (proj₁ (proj₂ (TR-map-act-μ K θ X (v i)) d (j , (p , tt)))))))) ,
  proj₂ (proj₂ (TR-map-act-μ K θ X (v i)) d (j , (p , tt)))
proj₂ (TR-map-μ K θ X k) (err e) ((i , tt) , j , tt) with proj₂ θ e k
... | u , v = (tt , (i , tt)) ,
  (trans (cong (Trace-μ _ _ (K × X))
               (proj₂ (proj₂ (Trace-⊥-nat _ _ (cur (TR-map K θ X))) (v i) (tt , j))))
  (sym (Trace-⊥-μ _ _ (K × X) (v i))))

proj₁ (TR-map-act-μ K θ X (ret k)) d i = proj₁ (TR-map-μ K θ X k) d i
proj₁ (TR-map-act-μ K θ X (act a r)) d i with proj₁ (TR-map-act-μ K θ X r) d i
... | u , w = u , cong (act a) w
proj₁ (TR-map-act-μ K θ X (err e)) d i = (tt , (tt , tt)) , refl

proj₂ (TR-map-act-μ K θ X (ret k)) d i = proj₂ (TR-map-μ K θ X k) d i
proj₂ (TR-map-act-μ K θ X (act a r)) d i with proj₂ (TR-map-act-μ K θ X r) d i
... | u , w = u , cong (act a) w
proj₂ (TR-map-act-μ K θ X (err e)) d i = (tt , tt) , refl




-- Local definition

TR-map-extract : {A E A' E' : Set} → (K : Set)
  → ((X : Set) → K → SF (Trace A E X) (Trace A' E' (K × X))) → Trace-Runner A E A' E' K
proj₁ (TR-map-extract K ϕ) a k = SF-∘ (ϕ ⊤ k) (SF-T _ _ (⊗-proj₁ _ _)) (act a (ret tt))
proj₂ (TR-map-extract K ϕ) e k = SF-∘ (ϕ ⊥ k) (SF-T _ _ (λ x → (SF-id _ (proj₂ x)))) (err e)


TR-≡ : {A E A' E' : Set} → (K : Set) → Trace-Runner A E A' E' K
  → Trace-Runner A E A' E' K → Set
TR-≡ K θ θ' = ((a : _) → SF≡ (proj₁ θ a) (proj₁ θ' a)) ×
              ((e : _) → SF≡ (proj₂ θ e) (proj₂ θ' e))



help : {A E A' E' : Set} → (K : Set) → (θ : Trace-Runner A E A' E' K)
     → (w : Trace A' E' K)
     → (j  : proj₁ (TR-map-act K θ ⊤ w (ret tt)))
     → (p  : proj₁ (SF-T A' E' (λ x → ⊤ , (λ _ → proj₁ x))
           (proj₂ (TR-map-act K θ ⊤ w (ret tt)) j)))
      →  proj₂ (SF-T A' E' (λ x → ⊤ , (λ _ → proj₁ x))
         (proj₂ (TR-map-act K θ ⊤ w (ret tt)) j)) p ≡ w
help K θ (ret k) j p = refl
help K θ (act a w) j p = cong (act a) (help K θ w j p)
help K θ (err e) j p = refl

help' : {A E A' E' : Set} → (K : Set) → (θ : Trace-Runner A E A' E' K)
     → (w : Trace A' E' K)
     → (proj₁ (TR-map-act K θ ⊤ w (ret tt)))
help' K θ (ret k) = tt
help' K θ (act a w) = help' K θ w
help' K θ (err e) = tt

help'' : {A E A' E' : Set} → (K : Set) → (θ : Trace-Runner A E A' E' K)
     → (w : Trace A' E' K)
     → proj₁ (SF-T A' E' (λ x → ⊤ , (λ _ → proj₁ x))
       (proj₂ (TR-map-act K θ ⊤ w (ret tt)) (help' K θ w)))
help'' K θ (ret k) = tt
help'' K θ (act a w) = help'' K θ w
help'' K θ (err e) = tt

belp :  {A E A' E' X : Set} → (K : Set) → (θ : Trace-Runner A E A' E' K)
     → (w : Trace A' E' ⊥) 
     → SL→ (Trace A' E' ⊥)
              (SF-T A' E' (λ x → SF-id _ (proj₂ x)) (Trace-⊥-dec A' E' (X × ⊥) w))
                (SF-id (Trace A' E' ⊥) w)
proj₁ (belp K θ w i) = tt
proj₂ (belp K θ (act a w) i) = cong (act a) (proj₂ (belp K θ w i))
proj₂ (belp K θ (err e) i) = refl

belp' :  {A E A' E' : Set} → (K : Set) → (θ : Trace-Runner A E A' E' K)
     → (w : Trace A' E' ⊥) 
     → proj₁ (SF-T A' E' {K × ⊥} {⊥} (λ x → ⊤ , (λ _ → proj₂ x))
       (Trace-⊥-dec A' E' (K × ⊥) w))
belp' {A} {E} {A'} {E'} K θ (act a w) = belp' {A} {E} {A'} {E'} K θ w
belp' K θ (err e) = tt

TR-map-bij-1 : {A E A' E' : Set} → (K : Set) → (θ : Trace-Runner A E A' E' K)
  → TR-≡ K (TR-map-extract K (TR-map K θ)) θ
proj₁ (proj₁ (TR-map-bij-1 K θ) a) k ((i , j) , p) = i ,
  help K θ (proj₂ (proj₁ θ a k) i) j p
proj₂ (proj₁ (TR-map-bij-1 K θ) a) k i = ((i , help' K θ (proj₂ (proj₁ θ a k) i)) ,
  help'' K θ (proj₂ (proj₁ θ a k) i)) ,
  sym (help K θ (proj₂ (proj₁ θ a k) i)
  (help' K θ (proj₂ (proj₁ θ a k) i)) (help'' K θ (proj₂ (proj₁ θ a k) i)))
proj₁ (proj₂ (TR-map-bij-1 K θ) e) k ((i , tt) , j) = i ,
  proj₂ (belp K θ (proj₂ (proj₂ θ e k) i) j)
proj₂ (proj₂ (TR-map-bij-1 K θ) e) k i = ((i , tt) , belp' K θ (proj₂ (proj₂ θ e k) i)) ,
  sym (proj₂ (belp K θ (proj₂ (proj₂ θ e k) i) (belp' K θ (proj₂ (proj₂ θ e k) i))))


-- Composition of trace runners
TR-∘ : {A₀ E₀ A₁ E₁ A₂ E₂ : Set} → (K K' : Set)
  → Trace-Runner A₀ E₀ A₁ E₁ K → Trace-Runner A₁ E₁ A₂ E₂ K'
  → Trace-Runner A₀ E₀ A₂ E₂ (K' × K) 
proj₁ (TR-∘ K K' (θ₁ , θ₂) ϕ) a = SF-∘ (SF-id K' ⊗ θ₁ a) (cur (TR-map K' ϕ K)) 
proj₂ (TR-∘ K K' (θ₁ , θ₂) ϕ) e =
  SF-∘ (SF-id K' ⊗ θ₂ e) (SF-∘ (cur (TR-map K' ϕ ⊥)) (SF-T _ _ λ {()}))




-- Parallel runner
TR-Par : (A E Y : Set) → Trace-Runner A E A E (Trace A E Y)
proj₁ (TR-Par A E Y) a r = SL-act a (Trace A E Y) (SF-T-δ A E Y r)
proj₂ (TR-Par A E Y) e r = SF-id (Trace A E ⊥) (err e)
