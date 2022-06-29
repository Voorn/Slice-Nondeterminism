module Runner.Stateful-Relator where


open import Data.Unit
open import Data.Empty
open import Data.Sum renaming (map to map⊎)
open import Data.Nat hiding (_⊔_)
open import Data.Product renaming (map to map×)
open import Relation.Binary.PropositionalEquality hiding ([_])


open import Index-Nondeterminism
open import Monoidal

open import Monads.Trace
open import Runner.Trace-Runner
open import Runner.Trace-Relator


-- State relation preserved under runs
Rela-run-pres : {U V A E K : Set}
  → (Runner-map U V A E K) → (Rel K K) → (Trace-Relator A E) → Set₁
Rela-run-pres θ CR Γ = {X : Set} → (a b : _) → (CR a b)
  → (t : Trace _ _ X) → Pow-Relator Γ (Rel× CR _≡_) (θ _ a t) (θ _ b t)

-- Relator dependent on starting state
Local-Relator : {A E B F : Set} 
  → (Γ : Trace-Relator B F) → (K : Set)
  → (Runner-map A E B F K) → (CR : Rel K K) → K → Trace-Relator A E 
Local-Relator Γ K ϕ CR k R a b = Pow-Relator Γ (Rel× CR R) (ϕ _ k a) (ϕ _ k b)


-- The local relator is a relator
LR-id : {A E B F K : Set} → (Γ : Trace-Relator B F) → (TRel-prop Γ)
  → (θ : Runner-map A E B F K) 
  → (CR : Rel K K) → (Rela-preo CR)
  → (k : K) → TRel-id (Local-Relator Γ K θ CR k)
LR-id Γ Γ-p θ CR CR-p k X a .a refl i = i ,
  (TRel-prop.Γ-sub Γ-p (_≡_) (Rel× CR _≡_) (λ {x .x refl → proj₁ (CR-p) (proj₁ x) , refl})
    (proj₂ (θ X k a) i) (proj₂ (θ X k a) i)
    (TRel-prop.Γ-id Γ-p (_ × X) (proj₂ (θ X k a) i) (proj₂ (θ X k a) i) refl))


LR-comp : {A E B F K : Set} → (Γ : Trace-Relator B F) → (TRel-prop Γ)
  → (θ : Runner-map A E B F K)
  → (CR : Rel K K) → (Rela-preo CR)
  → (k : K) → TRel-comp (Local-Relator Γ K θ CR k)
LR-comp Γ prop θ CR CR-p k S R l r (m , lΓSm , mΓRr) i with lΓSm i
... | j , rel₁ with mΓRr j
... | p , rel₂ = p , (TRel-prop.Γ-sub prop (Rela-comp (Rel× CR S) (Rel× CR R))
  (Rel× CR (Rela-comp S R)) (λ {(u , x) (v , z) ((w , y) , (u<w , xSy) , (w<v , yRz)) →
    (proj₂ CR-p u<w w<v) , y , xSy , yRz})
  (proj₂ (θ _ k l) i) (proj₂ (θ _ k r) p)
    (TRel-prop.Γ-comp prop (Rel× CR S) (Rel× CR R) (proj₂ (θ _ k l) i) (proj₂ (θ _ k r) p)
      ((proj₂ (θ _ k m) j) , (rel₁ , rel₂))))


LR-sub : {A E B F K : Set} → (Γ : Trace-Relator B F) → (TRel-prop Γ)
  → (θ : Runner-map A E B F K)
  → (CR : Rel K K) → (Rela-preo CR)
  → (k : K) → TRel-sub (Local-Relator Γ K θ CR k)
LR-sub Γ prop θ CR CR-p k S R S⊂R t r tΓSr i with tΓSr i
... | j , rel = j , (TRel-prop.Γ-sub prop (Rel× CR S) (Rel× CR R)
                    (λ {(u , x) (v , y) (u<v , xSy) → u<v , (S⊂R x y xSy)})
                    (proj₂ (θ _ k t) i) (proj₂ (θ _ k r) j) rel)


LR-nat< : {A E B F K : Set} → (Γ : Trace-Relator B F) → (TRel-prop Γ)
  → (θ : Runner-map A E B F K)
  → (Runner-map-S-nat K θ)
  → (CR : Rel K K) → (Rela-preo CR)
  → (k : K) → TRel-nat< (Local-Relator Γ K θ CR k)
LR-nat< Γ prop θ θ-fun CR CR-p k R f g t r t-r i
  with proj₂ (θ-fun f k) t i
... | j , eq with t-r j
... | p , rel with proj₁ (θ-fun g k) r p
... | c , eq₁ = c ,
    (TRel-prop.Γ-nat< prop (Rel× CR R) (λ (u , x) → (u , f x)) (λ (v , y) → (v , g y))
      (proj₂ (θ _ k t) i) (proj₂ (θ _ k r) c)
        (subst₂ (Γ (Rel× CR R)) (sym eq) eq₁ rel))

LR-nat> : {A E B F K : Set} → (Γ : Trace-Relator B F) → (TRel-prop Γ)
  → (θ : Runner-map A E B F K)
  → (Runner-map-S-nat K θ)
  → (CR : Rel K K) → (Rela-preo CR)
  → (k : K) → TRel-nat> (Local-Relator Γ K θ CR k)
LR-nat> Γ prop θ θ-fun CR CR-p k R f g t r t-r i with proj₁ (θ-fun f k) t i
... | j , eq with t-r j
... | p , rel with proj₂ (θ-fun g k) r p
... | c , eq₁ = c , subst₂ (Γ (Rel× CR R)) (sym eq) eq₁
  (TRel-prop.Γ-nat> prop (Rel× CR R) (λ {(u , x) → (u , f x)}) (λ {(v , y) → (v , g y)})
    (proj₂ (θ _ k t) j) (proj₂ (θ _ k r) p) rel)


LR-prop : {A E B F K : Set} → (Γ : Trace-Relator B F) → (TRel-prop Γ)
  → (θ : Runner-map A E B F K)
  → (Runner-map-S-nat K θ)
  → (CR : Rel K K) → (Rela-preo CR)
  → (k : K) → TRel-prop (Local-Relator Γ K θ CR k)
LR-prop Γ prop θ θ-fun CR CR-prop k = record
  {Γ-id = LR-id Γ prop θ CR CR-prop k ;
  Γ-comp = LR-comp Γ prop θ CR CR-prop k ;
  Γ-sub = LR-sub Γ prop θ CR CR-prop k ;
  Γ-nat< = LR-nat< Γ prop θ θ-fun CR CR-prop k ;
  Γ-nat> = LR-nat> Γ prop θ θ-fun CR CR-prop k }


LR-η : {A E B F K : Set} → (Γ : Trace-Relator B F) → (TRel-prop Γ) → (TRel-η Γ)
  → (θ : Runner-map A E B F K) → (Runner-map-η K θ)
  → (CR : Rel K K) → (Rela-preo CR)
  → (k : K) → TRel-η (Local-Relator Γ K θ CR k)
LR-η Γ prop Γ-η θ θ-η CR CR-prop k R x y xRy i  with proj₁ (θ-η _ k) x (tt , i)
... | (tt , tt) , eq with proj₂ (θ-η _ k) y (tt , tt)
... | (tt , j) , eq' = j , subst₂ (Γ (Rel× CR R)) (sym eq) eq'
                              (Γ-η (Rel× CR R) (k , x) (k , y) ((proj₁ CR-prop k) , xRy))


-- World relator: Dependent on subset of initial states
World-Relator : {A E B F : Set} → (Γ : Trace-Relator B F) → (K : Set)
  → (Runner-map A E B F K) → (CR : Rel K K) → (K → Set) → Trace-Relator A E 
World-Relator Γ K ϕ CR W R a b = (k : K) → W k → Local-Relator Γ K ϕ CR k R a b


World-sub : {A E B F : Set} → (Γ : Trace-Relator B F) → (K : Set)
  → (θ : Runner-map A E B F K) → (CR : Rel K K) → (W : K → Set) → (k : K) → (W k)
  → Trace-Relator-sub (World-Relator Γ K θ CR W) (Local-Relator Γ K θ CR k) 
World-sub Γ K θ CR W k Wk R l r rel = rel k Wk



-- World relator is a relator
WR-prop : {A E B F K : Set} → (Γ : Trace-Relator B F) → (TRel-prop Γ)
  → (θ : Runner-map A E B F K) → (Runner-map-S-nat K θ)
  → (CR : Rel K K) → (Rela-preo CR)
  → (W : K → Set) → TRel-prop (World-Relator Γ K θ CR W)
WR-prop Γ prop θ θ-fun CR CR-prop W = record
  {Γ-id = λ X x y x≡y k Wk → LR-id Γ prop θ CR CR-prop k X x y x≡y ;
  Γ-comp = λ S R x z (y , x-y , y-z) k Wk →
    LR-comp Γ prop θ CR CR-prop k S R x z (y , x-y k Wk , y-z k Wk) ;
  Γ-sub = λ S R S⊂R x y x-y k Wk → LR-sub Γ prop θ CR CR-prop k S R S⊂R x y (x-y k Wk) ;
  Γ-nat< = λ R f g x y x-y k Wk → LR-nat< Γ prop θ θ-fun CR CR-prop k R f g x y (x-y k Wk) ;
  Γ-nat> = λ R f g x y x-y k Wk → LR-nat> Γ prop θ θ-fun CR CR-prop k R f g x y (x-y k Wk) }


WR-η : {A E B F K : Set} → (Γ : Trace-Relator B F) → (TRel-prop Γ) → (TRel-η Γ)
  → (θ : Runner-map A E B F K) → (Runner-map-η K θ)
  → (CR : Rel K K) → (Rela-preo CR)
  → (W : K → Set) → TRel-η (World-Relator Γ K θ CR W)
WR-η Γ prop Γ-η θ θ-η CR CR-prop W R x y xRy k Wk =
  LR-η Γ prop Γ-η θ θ-η CR CR-prop k R x y xRy



-- Global relator (World relator on the full subset of states) is monadic if:
-- the relator Γ distributes over the non-empty powerset relator, and the θ runner is total

GR-μ : {A E B F K : Set} → (Γ : Trace-Relator B F) → (TRel-prop Γ) → (TRel-Pow Γ)
  → (θ : Runner-map A E B F K) → (Runner-map-S-nat K θ) → (Runner-map-μ K θ)
       → (Runner-map-Total _ θ)
  → (CR : Rel K K) → (Rela-preo CR) → (Rela-run-pres θ CR Γ)
  → TRel-μ (World-Relator Γ K θ CR (λ _ → ⊤))
GR-μ Γ prop Γ-P θ θ-sn θ-μ θ-tot CR CR-preo CR-rp R d e d-e k tt i
  with (WR-prop Γ prop θ θ-sn CR CR-preo (λ _ → ⊤))
... | GR-prop with proj₁ (θ-μ _ k) d (tt , i)
... | (j , j' , tt) , eq with d-e k tt j
... | p , t-r with proj₂ (θ _ k d) j
... | t with TRel-prop.Γ-sub prop (Rel× CR (World-Relator Γ _ θ CR (λ _ → ⊤) R))
-- The following is maybe nicer as a lemma
  (λ tu rv → Pow-Relator Γ (Rel× CR R) (cur (θ _) tu) (cur (θ _) rv))
    (λ {(u , a) (v , b) (u-v , a-b) i₁ →
      (proj₁ (a-b v tt (proj₁ (CR-rp u v u-v a i₁)))) ,
        (TRel-prop.Γ-sub prop (Rela-comp (Rel× CR _≡_) (Rel× CR R)) (Rel× CR R)
          (λ x y x₁ → (proj₂ CR-preo (proj₁ (proj₁ (proj₂ x₁))) (proj₁ (proj₂ (proj₂ x₁)))) ,
            subst (λ z → R z (proj₂ y)) (sym (proj₂ (proj₁ (proj₂ x₁))))
              (proj₂ (proj₂ (proj₂ x₁))))
          (proj₂ (θ _ u a) i₁) (proj₂ (θ _ v b)
                               (proj₁ (a-b v tt (proj₁ (CR-rp u v u-v a i₁)))))
      (TRel-prop.Γ-comp prop (Rel× CR _≡_) (Rel× CR R)
         (proj₂ (θ _ u a) i₁)
         (proj₂ (θ _ v b) (proj₁ (a-b v tt (proj₁ (CR-rp u v u-v a i₁)))))
         ((proj₂ (θ _ v a) (proj₁ (CR-rp u v u-v a i₁))) ,
           ((proj₂ (CR-rp u v u-v a i₁)) ,
           (proj₂ (a-b v tt (proj₁ (CR-rp u v u-v a i₁))))))))})
    t (proj₂ (θ _ k e) p) t-r
... | frb with Γ-P (Rel× CR R) (cur (θ _)) (cur (θ _)) (λ x → θ-tot _ (proj₁ x) (proj₂ x))
          t (proj₂ (θ _ k e) p) frb (j' , tt)
... | (u , tt) , w with proj₂ (θ-μ _ k) e (p , (u , tt))
... | (tt , h) , eq'   rewrite eq | eq' = h , w

