module Parallel.Runner where

open import Data.Unit
open import Data.Empty
open import Data.Sum renaming (map to map⊎)
open import Data.Nat hiding (_⊔_)
open import Data.Product renaming (map to map×)
open import Relation.Binary.PropositionalEquality hiding ([_])


open import Slice-Functions.Base
open import Slice-Functions.Subcategories
open import Slice-Functions.Monoidal

open import Monads.Trace

open import Parallel.Base
open import Parallel.Monoidal


-- Parallel runner

ρ-runner : (A E K : Set) → (X : Set) → SF (Trace A E X × Trace A E K)
                                              (Trace A E (X × Trace A E K))
ρ-runner A E Y X = SF-∘ (SF-id _ ⊗ SF-T-δ A E Y) (𝕃 A E X (Trace A E Y))



ρ-runner-Total : (A E K X : Set) → SF-Total (ρ-runner A E K X)
ρ-runner-Total A E K X (ret x , ret y) = (tt , tt) , tt
ρ-runner-Total A E K X (ret x , act a r) = (tt , (inj₁ tt)) , tt
ρ-runner-Total A E K X (ret x , err e) = (tt , (inj₁ tt)) , tt
ρ-runner-Total A E K X (act a l , r) = (tt , (SF-T-δ-Total A E K r)) ,
  (ℙ-Total A E X (Trace A E K) (l , (proj₂ (SF-T-δ A E K r) (SF-T-δ-Total A E K r))))
ρ-runner-Total A E K X (err e , r) = (tt , (SF-T-δ-Total A E K r)) , tt



ρ-runner-nat : (A E K : Set) → {X Y : Set} → (f : SF X Y) → SF-Total f
  → SF≡ (SF-∘ (SF-T A E f ⊗ SF-id _) (ρ-runner A E K Y))
         (SF-∘ (ρ-runner A E K X) (SF-T A E (f ⊗ SF-id _)))
ρ-runner-nat A E K f f-tot =
  SF≡-Tran _ _ _
    (SF≡-Symm _ _ (SF-asso (SF-T A E f ⊗ SF-id (Trace A E K))
              (SF-id _ ⊗ SF-T-δ A E _) (𝕃 A E _ (Trace A E _))))
  (SF≡-Tran _ _ _
    (SF-∘-l≡ (SF-∘ (SF-T A E f ⊗ SF-id (Trace A E K))
           (SF-id (Trace A E _) ⊗ SF-T-δ A E K))
           (SF-∘ (SF-id (Trace A E _) ⊗ SF-T-δ A E K)
           (SF-T A E f ⊗ SF-id (Trace A E (Trace A E K))))
           (𝕃 A E _ (Trace A E _))
        (⊗-trade (SF-T A E f) (SF-T-δ A E K)))
  (SF≡-Tran _ _ _
    (SF-asso (SF-id _ ⊗ SF-T-δ A E _) (SF-T A E f ⊗ SF-id _) (𝕃 A E _ (Trace A E _)))
  (SF≡-Tran _ _ _
    (SF-∘-r≡ (SF-id _ ⊗ SF-T-δ A E _)
       (SF-∘ (SF-T A E f ⊗ SF-id _) (𝕃 A E _ (Trace A E _)))
       (SF-∘ (𝕃 A E _ (Trace A E _)) (SF-T A E (f ⊗ SF-id _)))
       (𝕃-T-nat-left A E _ f f-tot ))
  (SF≡-Symm _ _ (SF-asso (SF-id _ ⊗ SF-T-δ A E K) (𝕃 A E _ _) (SF-T A E (f ⊗ SF-id _)))))))


ρ-runner-mult : (A E K : Set) → (X : Set)
  → SF≡ (SF-∘ (SF-T-μ A E X ⊗ SF-id _) (ρ-runner A E K X))
         (SF-∘ (ρ-runner A E K (Trace A E X)) (SF-∘ (SF-T A E (ρ-runner A E K X))
               (SF-T-μ A E (X × Trace A E K))))
ρ-runner-mult A E K X =
  SF≡-Tran _ _ _
    (SF≡-Symm _ _ (SF-asso (SF-T-μ A E _ ⊗ SF-id (Trace A E K))
              (SF-id _ ⊗ SF-T-δ A E _) (𝕃 A E _ (Trace A E _))))
  (SF≡-Tran _ _ _
    (SF-∘-l≡ (SF-∘ (SF-T-μ A E _ ⊗ SF-id (Trace A E K))
           (SF-id (Trace A E _) ⊗ SF-T-δ A E K))
           (SF-∘ (SF-id (Trace A E _) ⊗ SF-T-δ A E K)
           (SF-T-μ A E _ ⊗ SF-id (Trace A E (Trace A E K))))
           (𝕃 A E _ (Trace A E _))
-- Interchange order of (μ ⊗ I) and (I ⊗ δ)
        (⊗-trade (SF-T-μ A E _) (SF-T-δ A E K)))
  (SF≡-Tran _ _ _
    (SF-asso (SF-id _ ⊗ SF-T-δ A E _) (SF-T-μ A E _ ⊗ SF-id _)
             (𝕃 A E _ (Trace A E _)))
  (SF≡-Tran _ _ _
    (SF-∘-r≡ (SF-id _ ⊗ SF-T-δ A E _)
             (SF-∘ (SF-T-μ A E _ ⊗ SF-id _) (𝕃 A E _ (Trace A E _)))
             (SF-∘ (SF-id (Trace A E (Trace A E X)) ⊗ SF-T-δ A E (Trace A E K))
               (SF-∘ (𝕃 A E (Trace A E X) (Trace A E (Trace A E K)))
               (SF-∘ (SF-T A E (𝕃 A E X (Trace A E K)))
               (SF-T-μ A E (X × Trace A E K)))))
-- Multiplication law for 𝕃
             (IL-mult-𝕃 A E _ _))
  (SF≡-Tran _ _ _
    (SF≡-Symm _ _ (SF-asso (SF-id _ ⊗ SF-T-δ A E _) (SF-id _ ⊗ SF-T-δ A E (Trace A E K))
               (SF-∘ (𝕃 A E (Trace A E X) (Trace A E (Trace A E K)))
               (SF-∘ (SF-T A E (𝕃 A E X (Trace A E K)))
               (SF-T-μ A E (X × Trace A E K))))))
  (SF≡-Tran _ _ _
    ((SF-∘-l≡ (SF-∘ (SF-id _ ⊗ SF-T-δ A E _) (SF-id _ ⊗ SF-T-δ A E _))
      _ (SF-∘ (𝕃 A E (Trace A E X) (Trace A E (Trace A E K)))
               (SF-∘ (SF-T A E (𝕃 A E X (Trace A E K)))
               (SF-T-μ A E (X × Trace A E K))))
        (SF≡-Tran _ _ _
           (SF≡-Symm _ _ (⊗-∘ (SF-id _) (SF-id _) (SF-T-δ A E _) (SF-T-δ A E _)))
        (SF≡-Tran _ _ _ (⊗-≡-right (SF-∘ (SF-id _) (SF-id _))
-- Coassociativity of δ
            (SF-T-δ-asso A E _))
            (⊗-∘ (SF-id _) (SF-id _) (SF-T-δ A E _) (SF-T A E (SF-T-δ A E _))) ))))
  (SF≡-Tran _ _ _
    (SF-asso (SF-id _ ⊗ SF-T-δ A E _) (SF-id _ ⊗ SF-T A E (SF-T-δ A E K))
             (SF-∘ (𝕃 A E (Trace A E X) (Trace A E (Trace A E K)))
                   (SF-∘ (SF-T A E (𝕃 A E X (Trace A E K)))
                         (SF-T-μ A E (X × Trace A E K)))))
  (SF≡-Tran _ _ _
    (SF-∘-r≡ (SF-id _ ⊗ SF-T-δ A E _)
             (SF-∘ (SF-id _ ⊗ SF-T A E (SF-T-δ A E K))
             (SF-∘ (𝕃 A E (Trace A E X) (Trace A E (Trace A E K)))
                   (SF-∘ (SF-T A E (𝕃 A E X (Trace A E K)))
                         (SF-T-μ A E (X × Trace A E K)))))
             _
             (SF≡-Tran _ _ _
               (SF≡-Symm _ _ (SF-asso (SF-id _ ⊗ SF-T A E (SF-T-δ A E K))
                       (𝕃 A E (Trace A E X) (Trace A E (Trace A E K)))
                       (SF-∘ (SF-T A E (𝕃 A E X (Trace A E K)))
                         (SF-T-μ A E (X × Trace A E K)))))
               (SF≡-Tran _ _ _ (SF-∘-l≡
                  (SF-∘ (SF-id _ ⊗ SF-T A E (SF-T-δ A E K))
                   (𝕃 A E (Trace A E X) (Trace A E (Trace A E K))))
                  _
                  (SF-∘ (SF-T A E (𝕃 A E X (Trace A E K)))
                   (SF-T-μ A E (X × Trace A E K)))
-- Naturality to get Tδ past 𝕃
                 (𝕃-T-nat-right A E _ (SF-T-δ A E K) (SF-T-δ-Total A E K)))
               (SF≡-Tran _ _ _ (SF-asso (𝕃 A E (Trace A E X) (Trace A E K))
                        (SF-T A E (SF-id _ ⊗ (SF-T-δ A E K)))
                        (SF-∘ (SF-T A E (𝕃 A E X (Trace A E K)))
                           (SF-T-μ A E (X × Trace A E K))))
               (SF-∘-r≡ (𝕃 A E (Trace A E X) (Trace A E K))
                        (SF-∘ (SF-T A E (SF-id _ ⊗ (SF-T-δ A E K)))
                             (SF-∘ (SF-T A E (𝕃 A E X (Trace A E K)))
                               (SF-T-μ A E (X × Trace A E K))))
                        _
                  (SF≡-Tran _ _ _
                    (SF≡-Symm _ _ (SF-asso (SF-T A E (SF-id _ ⊗ (SF-T-δ A E K)))
                              (SF-T A E (𝕃 A E X (Trace A E K)))
                              (SF-T-μ A E (X × Trace A E K))))
                    (SF-∘-l≡ (SF-∘ (SF-T A E (SF-id _ ⊗ (SF-T-δ A E K)))
                                   (SF-T A E (𝕃 A E X (Trace A E K))))
                             (SF-T A E (ρ-runner A E K _))
                             (SF-T-μ A E (X × Trace A E K))
-- Compositionality on functor
                      (SF≡-Symm _ _ (SF-T-∘ A E (SF-id _ ⊗ (SF-T-δ A E K))
                                (𝕃 A E X (Trace A E K))))
                             )))))))
  (SF≡-Symm _ _ (SF-asso (SF-id _ ⊗ SF-T-δ A E _) (𝕃 A E (Trace A E X) (Trace A E K))
           (SF-∘ (SF-T A E (ρ-runner A E K _))
                  (SF-T-μ A E (X × Trace A E K))))))))))))


-- SF-∘ (SF-id _ ⊗ SF-T-δ A E _)
--      (SF-∘ (𝕃 A E (Trace A E X) (Trace A E K))
--            (SF-∘ (SF-T A E (ρ-runner A E K _))
--                  (SF-T-μ A E (X × Trace A E K))))

-- SF-∘ (SF-id _ ⊗ SF-T-δ A E _)
--      (SF-∘ (SF-∘ (𝕃 A E (Trace A E X) (Trace A E K))
--                  (SF-T A E (SF-id _ ⊗ (SF-T-δ A E K))))
--            (SF-∘ (SF-T A E (𝕃 A E X (Trace A E K)))
--                  (SF-T-μ A E (X × Trace A E K))))


-- SF-∘ (SF-∘ (SF-id _ ⊗ SF-T-δ A E _) (SF-id _ ⊗ SF-T A E (SF-T-δ A E K)))
--      (SF-∘ (𝕃 A E (Trace A E X) (Trace A E (Trace A E K)))
--            (SF-∘ (SF-T A E (𝕃 A E X (Trace A E K)))
--                  (SF-T-μ A E (X × Trace A E K))))

-- (SF≡-Symm _ _ (⊗-∘ (SF-id _) (SF-id _) (SF-T-δ A E _) (SF-T-δ A E _)))

--proj₁ (ρ-runner-nat A E K f f-tot) (act x l , r) ((i , tt) , (tt , j) , k) = {!!}
--proj₁ (ρ-runner-nat A E K f f-tot) (err x , r) ((i , tt) , (tt , j) , k) = {!!}
--proj₂ (ρ-runner-nat A E K f f-tot) (l , r) i = {!!}

-- (𝕃-T-nat A E f (SF-id _) f-tot ?)
