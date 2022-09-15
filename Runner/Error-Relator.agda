module Runner.Error-Relator where


open import Data.Unit
open import Data.Empty
open import Data.Sum renaming (map to map⊎)
open import Data.Nat hiding (_⊔_)
open import Data.Product renaming (map to map×)
open import Relation.Binary.PropositionalEquality hiding ([_])


open import Monads.Trace
open import Runner.Trace-Runner
open import Runner.Trace-Relator


TError : (E X : Set) → Set
TError E X = Trace ⊥ E X

Error-Runner : (A E F K : Set) → Set₁
Error-Runner A E F K = Runner-map A E ⊥ F K

-- The error relator, using a predicate U on E denoting which errors are undetectable

data E-relat {E : Set} (U : E → Set) {X Y : Set} (R : Rel X Y) :
     Rel (TError E X) (TError E Y) where
  rel-ret : (x : X) → (y : Y) → R x y → E-relat U R (ret x) (ret y)
  rel-err : (e : E) → E-relat U R (err e) (err e)
  rel-inv : (e : E) → (U e) → (t : Trace ⊥ E Y) → E-relat U R (err e) t



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

E-relat-κ : {E : Set} → (U : E → Set) → TRel-κ (E-relat U)
E-relat-κ U S R f g (ret x) .(ret y) f-g (rel-ret .x y xSy) = f-g x y xSy
E-relat-κ U S R f g (err e) .(err e) f-g (rel-err .e) = rel-err e
E-relat-κ U S R f g (err e) r f-g (rel-inv .e Ue .r) = rel-inv e Ue (Trace-κ ⊥ _ _ _ g r)


E-relat-Pow : {E : Set} → (U : E → Set) → TRel-SL (E-relat U)
E-relat-Pow U R f g g-tot (ret x) .(ret y) (rel-ret .x y x-y) (i , tt) =
  (proj₁ (x-y i) , tt) , proj₂ (x-y i)
E-relat-Pow U R f g g-tot (err x) .(err x) (rel-err .x) i = (tt , tt) , (rel-err x)
E-relat-Pow U R f g g-tot (err x) r (rel-inv .x xU .r) i =
  (SF-T-Total ⊥ _ g g-tot r , tt) , rel-inv x xU _

