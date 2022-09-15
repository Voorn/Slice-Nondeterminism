module Examples.Process-Algebra where

open import Data.Unit
open import Data.Empty
open import Data.Sum renaming (map to map⊎)
open import Data.Nat hiding (_⊔_)
open import Data.Product renaming (map to map×)
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Data.Bool

open import Slice.Base
open import Slice.Lattice

open import Slice-Functions.Base

open import Examples.Transition


data PA (A : Set) : Set where
  at : A → PA A
  _⊕_ : PA A → PA A → PA A
  _·_ : PA A → PA A → PA A
  _𝕀_ : PA A → PA A → PA A
  _𝕃_ : PA A → PA A → PA A


SL-2* : {X Y Z : Set} → (X → Y → SL Z) → (SL X → SL Y → SL Z)
SL-2* f a b = SL-* (λ p → SL-* (f p) b) a


Lis-𝕀 : {A : Set} → Lis A → Lis A → SL (Lis A)
Lis-𝕃 : {A : Set} → Lis A → Lis A → SL (Lis A)
Lis-𝕀 p q = join (Lis-𝕃 p q) (Lis-𝕃 q p)
Lis-𝕃 uni q = SL-η _ q
Lis-𝕃 (act a p) q = SL-fun (act a) (Lis-𝕀 p q)



PA-eval : {A : Set} → SF (PA A) (Lis A)
PA-eval (at a) = SL-η (Lis _) (act a uni)
PA-eval (P ⊕ Q) = join (PA-eval P) (PA-eval Q)
PA-eval (P · Q) = SL-* (λ a → SL-fun (append a) (PA-eval Q)) (PA-eval P)
PA-eval (P 𝕀 Q) = SL-2* Lis-𝕀 (PA-eval P) (PA-eval Q)
PA-eval (P 𝕃 Q) = SL-2* Lis-𝕃 (PA-eval P) (PA-eval Q)


