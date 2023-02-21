module Slice-Functions.Category where

-- standard library
open import Data.Unit
open import Data.Empty
open import Data.Sum 
open import Data.Product

open import Relation.Binary.PropositionalEquality

-- categories library
open import Categories.Category

-- local
open import Slice-Functions.Base


SF-Cat : Category _ _ _
SF-Cat = record
    { Obj = Set
    ; _⇒_ = SF
    ; _≈_ = SF≡
    ; id = SF-id _
    ; _∘_ = λ g f → SF-∘ f g
    ; assoc = λ {_ _ _ _ f g h} → SF≡-Symm _ _ (SF-asso f g h)  
    ; sym-assoc = λ {_ _ _ _ f g h} → SF-asso f g h
    ; identityˡ = λ {A B f} → SF-runi {A} {B} f
    ; identityʳ =  λ {A B f} → SF-luni {A} {B} f
    ; identity² = (λ x i → tt , refl) , (λ x i → (tt , tt) , refl)
    ; equiv = record
      { refl = SF≡-Refl _
      ; sym = λ eq → SF≡-Symm _ _ eq
      ; trans = λ eq eq' → SF≡-Tran _ _ _ eq eq'
      }
    ; ∘-resp-≈ = SF-∘≡
    }
