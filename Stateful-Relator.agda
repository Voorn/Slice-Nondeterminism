module Stateful-Relator where


open import Data.Unit
open import Data.Empty
open import Data.Sum renaming (map to map⊎)
open import Data.Nat hiding (_⊔_)
open import Data.Product renaming (map to map×)
open import Relation.Binary.PropositionalEquality hiding ([_])


open import Index-Nondeterminism
open import Monoidal
open import Free-Monad
open import Trace
open import Trace-Runner


Rela : Set → Set → Set₁
Rela X Y = X → Y → Set

Rela₁ :  Set₁ → Set₁ → Set₁
Rela₁ X Y = X → Y → Set


Rel× : {A B C D : Set} → Rela A B → Rela C D → Rela (A × C) (B × D)
Rel× S R (a , c) (b , d) = S a b × R c d


Rela-id : (X : Set) → Rela X X
Rela-id X = _≡_

Rela-comp : {X Y Z : Set} → Rela X Y → Rela Y Z → Rela X Z
Rela-comp S R x z = Σ _ λ y → S x y × R y z

Rela-sub : {X Y : Set} → Rela₁ (Rela X Y) (Rela X Y)
Rela-sub S R = (x : _) → (y : _) → S x y → R x y

Rela-eq : {X Y : Set} → Rela₁ (Rela X Y) (Rela X Y)
Rela-eq S R = Rela-sub S R × Rela-sub R S

Rela-tp : {X Y X' Y' : Set} → (f : X → X') → (g : Y → Y') → Rela X' Y' → Rela X Y
Rela-tp f g R x y = R (f x) (g y) 



Rela-refl : {X : Set} → Rela X X → Set
Rela-refl R = (x : _) → R x x

Rela-trans : {X : Set} → Rela X X → Set
Rela-trans R = {x y z : _} → R x y → R y z → R x z

Rela-preo : {X : Set} → Rela X X → Set
Rela-preo R = Rela-refl R × Rela-trans R



TError : (E X : Set) → Set
TError E X = Trace ⊥ E X

Error-Runner : (A E F K : Set) → Set₁
Error-Runner A E F K = Runner-map A E ⊥ F K


data E-relat {E : Set} (U : E → Set) {X Y : Set} (R : Rela X Y) :
     Rela (TError E X) (TError E Y) where
  rel-ret : (x : X) → (y : Y) → R x y → E-relat U R (ret x) (ret y)
  rel-err : (e : E) → E-relat U R (err e) (err e)
  rel-inv : (e : E) → (U e) → (t : Trace ⊥ E Y) → E-relat U R (err e) t



Trace-Relator : (A E : Set) → Set₁
Trace-Relator A E = {X Y : Set} → Rela X Y → Rela (Trace A E X) (Trace A E Y)

Trace-Relator-sub : {A E : Set} → (Trace-Relator A E) → (Trace-Relator A E) → Set₁
Trace-Relator-sub Γ Γ' = {X Y : Set} → (R : Rela X Y) → Rela-sub (Γ R) (Γ' R)




TRel-id : {A E : Set} → Trace-Relator A E → Set₁
TRel-id Γ = (X : Set) → Rela-sub (Rela-id (Trace _ _ X)) (Γ (Rela-id X))

TRel-comp : {A E : Set} → Trace-Relator A E → Set₁
TRel-comp Γ = {X Y Z : Set} → (S : Rela X Y) → (R : Rela Y Z)
  → Rela-sub (Rela-comp (Γ S) (Γ R)) (Γ (Rela-comp S R))

TRel-sub : {A E : Set} → Trace-Relator A E → Set₁
TRel-sub Γ = {X Y : Set} → (S R : Rela X Y) → Rela-sub S R → Rela-sub (Γ S) (Γ R)

TRel-nat< : {A E : Set} → Trace-Relator A E → Set₁
TRel-nat< Γ = {X Y X' Y' : Set} → (R : Rela X' Y') → (f : X → X') → (g : Y → Y')
  → Rela-sub (Rela-tp (Trace-map _ _ f) (Trace-map _ _ g) (Γ R)) (Γ (Rela-tp f g R))

TRel-nat> : {A E : Set} → Trace-Relator A E → Set₁
TRel-nat> Γ = {X Y X' Y' : Set} → (R : Rela X' Y') → (f : X → X') → (g : Y → Y')
  → Rela-sub (Γ (Rela-tp f g R)) (Rela-tp (Trace-map _ _ f) (Trace-map _ _ g) (Γ R))


record TRel-prop {A E : Set} (Γ : Trace-Relator A E) : Set₁ where
  field
    Γ-id : TRel-id Γ
    Γ-comp : TRel-comp Γ
    Γ-sub : TRel-sub Γ
    Γ-nat< : TRel-nat< Γ
    Γ-nat> : TRel-nat> Γ



TRel-η : {A E : Set} → Trace-Relator A E → Set₁
TRel-η Γ = {X Y : Set} → (R : Rela X Y) → Rela-sub R (λ x y → Γ R (ret x) (ret y))

TRel-μ : {A E : Set} → Trace-Relator A E → Set₁
TRel-μ Γ = {X Y : Set} → (R : Rela X Y)
  → Rela-sub (Γ (Γ R)) (λ d d' → Γ R (Trace-μ _ _ X d) (Trace-μ _ _ Y d')) 




E-relat-id : {E : Set} → (U : E → Set) → TRel-id (E-relat U)
E-relat-id U X (ret x) .(ret x) refl = rel-ret x x refl
E-relat-id U X (err e) .(err e) refl = rel-err e


E-relat-comp : {E : Set} → (U : E → Set) → TRel-comp (E-relat U)
E-relat-comp U S R (ret x) .(ret z) (.(ret y) , rel-ret .x y xSy , rel-ret .y z yRz) =
  rel-ret x z (y , xSy , yRz)
E-relat-comp U S R (err e) .(err e) (.(err e) , rel-err .e , rel-err .e) = rel-err e
E-relat-comp U S R (err e) r (.(err e) , rel-err .e , rel-inv .e x .r) = rel-inv e x r
E-relat-comp U S R (err e) r (m , rel-inv .e x .m , mΓRr) = rel-inv e x r


E-relat-sub : {E : Set} → (U : E → Set) → TRel-sub (E-relat U)
E-relat-sub U S R S⊂R (ret x) .(ret y) (rel-ret .x y xSy) = rel-ret x y (S⊂R x y xSy)
E-relat-sub U S R S⊂R (err e) .(err e) (rel-err .e) = rel-err e
E-relat-sub U S R S⊂R (err e) r (rel-inv .e ue .r) = rel-inv e ue r


E-relat-nat< : {E : Set} → (U : E → Set) → TRel-nat< (E-relat U)
E-relat-nat< U R f g (ret x) (ret y) (rel-ret .(f x) .(g y) fxRgy) = rel-ret x y fxRgy
E-relat-nat< U R f g (err e) (ret y) (rel-inv .e ue .(ret (g y))) = rel-inv e ue (ret y)
E-relat-nat< U R f g (err e) (err .e) (rel-err .e) = rel-err e
E-relat-nat< U R f g (err e) (err e') (rel-inv .e ue .(err e')) = rel-inv e ue (err e')


E-relat-nat> : {E : Set} → (U : E → Set) → TRel-nat> (E-relat U)
E-relat-nat> U R f g (ret x) (ret y) (rel-ret .x .y fxRgy) = rel-ret (f x) (g y) fxRgy
E-relat-nat> U R f g (err e) (ret y) (rel-inv .e ue .(ret y)) = rel-inv e ue (ret (g y))
E-relat-nat> U R f g (err e) (err .e) (rel-err .e) = rel-err e
E-relat-nat> U R f g (err e) (err e') (rel-inv .e ue .(err e')) = rel-inv e ue (err e')


E-relat-prop : {E : Set} → (U : E → Set) → TRel-prop (E-relat U)
E-relat-prop U = record
  { Γ-id = E-relat-id U ; Γ-comp = E-relat-comp U ; Γ-sub = E-relat-sub U ;
    Γ-nat< = E-relat-nat< U ; Γ-nat> = E-relat-nat> U }


E-relat-η : {E : Set} → (U : E → Set) → TRel-η (E-relat U)
E-relat-η U R x y xRy = rel-ret x y xRy

E-relat-μ : {E : Set} → (U : E → Set) → TRel-μ (E-relat U)
E-relat-μ U R (ret (ret x)) .(ret (ret y)) (rel-ret .(ret x) .(ret y) (rel-ret .x y xRy))
  = rel-ret x y xRy
E-relat-μ U R (ret (err e)) .(ret (err e)) (rel-ret .(err e) .(err e) (rel-err .e))
  = rel-err e
E-relat-μ U R (ret (err e)) .(ret r) (rel-ret .(err e) r (rel-inv .e ue .r))
  = rel-inv e ue r
E-relat-μ U R (err e) .(err e) (rel-err .e) = rel-err e
E-relat-μ U R (err e) d' (rel-inv .e ue .d') = rel-inv e ue (Trace-μ _ _ _ d')



-- Nondeterminism
Pow-Relator : {A E : Set} → (Γ : Trace-Relator A E) → {X Y : Set}
  → Rela X Y → Rela₁ (Pow (Trace A E X)) (Pow (Trace A E Y))
Pow-Relator Γ R (I , V) (J , W) = (i : I) → Σ J λ j → Γ R (V i) (W j) 


Local-Relator : {A E B F : Set} 
  → (Γ : Trace-Relator B F) → (K : Set)
  → (Runner-map A E B F K) → (CR : Rela K K) → K → Trace-Relator A E 
Local-Relator Γ K ϕ CR k R a b = Pow-Relator Γ (Rel× CR R) (ϕ _ k a) (ϕ _ k b)


-- Proofs could be generalised to more relators
LR-id : {A E B F K : Set} → (Γ : Trace-Relator B F) → (TRel-prop Γ)
  → (θ : Runner-map A E B F K) 
  → (CR : Rela K K) → (Rela-preo CR)
  → (k : K) → TRel-id (Local-Relator Γ K θ CR k)
LR-id Γ Γ-p θ CR CR-p k X a .a refl i = i ,
  (TRel-prop.Γ-sub Γ-p (_≡_) (Rel× CR _≡_) (λ {x .x refl → proj₁ (CR-p) (proj₁ x) , refl})
    (proj₂ (θ X k a) i) (proj₂ (θ X k a) i)
    (TRel-prop.Γ-id Γ-p (_ × X) (proj₂ (θ X k a) i) (proj₂ (θ X k a) i) refl))


LR-comp : {A E B F K : Set} → (Γ : Trace-Relator B F) → (TRel-prop Γ)
  → (θ : Runner-map A E B F K)
  → (CR : Rela K K) → (Rela-preo CR)
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
  → (CR : Rela K K) → (Rela-preo CR)
  → (k : K) → TRel-sub (Local-Relator Γ K θ CR k)
LR-sub Γ prop θ CR CR-p k S R S⊂R t r tΓSr i with tΓSr i
... | j , rel = j , (TRel-prop.Γ-sub prop (Rel× CR S) (Rel× CR R)
                    (λ {(u , x) (v , y) (u<v , xSy) → u<v , (S⊂R x y xSy)})
                    (proj₂ (θ _ k t) i) (proj₂ (θ _ k r) j) rel)


LR-nat< : {A E B F K : Set} → (Γ : Trace-Relator B F) → (TRel-prop Γ)
  → (θ : Runner-map A E B F K)
  → (Runner-map-S-nat K θ)
  → (CR : Rela K K) → (Rela-preo CR)
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
  → (CR : Rela K K) → (Rela-preo CR)
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
  → (CR : Rela K K) → (Rela-preo CR)
  → (k : K) → TRel-prop (Local-Relator Γ K θ CR k)
LR-prop Γ prop θ θ-fun CR CR-prop k = record
  {Γ-id = LR-id Γ prop θ CR CR-prop k ;
  Γ-comp = LR-comp Γ prop θ CR CR-prop k ;
  Γ-sub = LR-sub Γ prop θ CR CR-prop k ;
  Γ-nat< = LR-nat< Γ prop θ θ-fun CR CR-prop k ;
  Γ-nat> = LR-nat> Γ prop θ θ-fun CR CR-prop k }


LR-η : {A E B F K : Set} → (Γ : Trace-Relator B F) → (TRel-prop Γ) → (TRel-η Γ)
  → (θ : Runner-map A E B F K) → (Runner-map-η K θ)
  → (CR : Rela K K) → (Rela-preo CR)
  → (k : K) → TRel-η (Local-Relator Γ K θ CR k)
LR-η Γ prop Γ-η θ θ-η CR CR-prop k R x y xRy i  with proj₁ (θ-η _ k) x (tt , i)
... | (tt , tt) , eq with proj₂ (θ-η _ k) y (tt , tt)
... | (tt , j) , eq' = j , subst₂ (Γ (Rel× CR R)) (sym eq) eq'
                              (Γ-η (Rel× CR R) (k , x) (k , y) ((proj₁ CR-prop k) , xRy))


-- World relator
World-Relator : {A E B F : Set} → (Γ : Trace-Relator B F) → (K : Set)
  → (Runner-map A E B F K) → (CR : Rela K K) → (K → Set) → Trace-Relator A E 
World-Relator Γ K ϕ CR W R a b = (k : K) → W k → Local-Relator Γ K ϕ CR k R a b


World-sub : {A E B F : Set} → (Γ : Trace-Relator B F) → (K : Set)
  → (θ : Runner-map A E B F K) → (CR : Rela K K) → (W : K → Set) → (k : K) → (W k)
  → Trace-Relator-sub (World-Relator Γ K θ CR W) (Local-Relator Γ K θ CR k) 
World-sub Γ K θ CR W k Wk R l r rel = rel k Wk




WR-prop : {A E B F K : Set} → (Γ : Trace-Relator B F) → (TRel-prop Γ)
  → (θ : Runner-map A E B F K) → (Runner-map-S-nat K θ)
  → (CR : Rela K K) → (Rela-preo CR)
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
  → (CR : Rela K K) → (Rela-preo CR)
  → (W : K → Set) → TRel-η (World-Relator Γ K θ CR W)
WR-η Γ prop Γ-η θ θ-η CR CR-prop W R x y xRy k Wk =
  LR-η Γ prop Γ-η θ θ-η CR CR-prop k R x y xRy



--GR-μ : {A E B F K : Set} → (Γ : Trace-Relator B F) → (TRel-prop Γ) → (TRel-μ Γ)
--  → (θ : Runner-map A E B F K) → (Runner-map-μ K θ)
--  → (CR : Rela K K) → (Rela-preo CR)
--  → TRel-μ (World-Relator Γ K θ CR (λ _ → ⊤))
--GR-μ Γ prop Γ-μ θ θ-μ CR CR-preo R d d' d-d' k tt i with proj₁ (θ-μ _ k) d (tt , i)
--... | (j , v , tt) , eq with d-d' k tt j
--... | p , rel = {!p!}


-- proj₂ (PK-T _ _ (cur (θ _)) (proj₂ (θ (Trace _ _ _) k d) j)) v
