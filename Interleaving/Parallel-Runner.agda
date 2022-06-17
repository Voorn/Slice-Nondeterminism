module Interleaving.Parallel-Runner where

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

open import Interleaving.Parallel
open import Interleaving.Parallel-Monoidal




ρ-runner : (A E K : Set) → (X : Set) → PK-Hom (Trace A E X × Trace A E K)
                                              (Trace A E (X × Trace A E K))
ρ-runner A E Y X = PK-∘ (PK-Id _ ⊗ PK-T-δ A E Y) (𝕃 A E X (Trace A E Y))



ρ-runner-Total : (A E K X : Set) → PK-Total (ρ-runner A E K X)
ρ-runner-Total A E K X (ret x , ret y) = (tt , tt) , tt
ρ-runner-Total A E K X (ret x , act a r) = (tt , (inj₁ tt)) , tt
ρ-runner-Total A E K X (ret x , err e) = (tt , (inj₁ tt)) , tt
ρ-runner-Total A E K X (act a l , r) = (tt , (PK-T-δ-Total A E K r)) ,
  (ℙ-Total A E X (Trace A E K) (l , (proj₂ (PK-T-δ A E K r) (PK-T-δ-Total A E K r))))
ρ-runner-Total A E K X (err e , r) = (tt , (PK-T-δ-Total A E K r)) , tt



ρ-runner-nat : (A E K : Set) → {X Y : Set} → (f : PK-Hom X Y) → PK-Total f
  → PK-≡ (PK-∘ (PK-T A E f ⊗ PK-Id _) (ρ-runner A E K Y))
         (PK-∘ (ρ-runner A E K X) (PK-T A E (f ⊗ PK-Id _)))
ρ-runner-nat A E K f f-tot =
  PK-≡-trans
    (PK-≡-sym (PK-asso (PK-T A E f ⊗ PK-Id (Trace A E K))
              (PK-Id _ ⊗ PK-T-δ A E _) (𝕃 A E _ (Trace A E _))))
  (PK-≡-trans
    (PK-∘-l≡ (PK-∘ (PK-T A E f ⊗ PK-Id (Trace A E K))
           (PK-Id (Trace A E _) ⊗ PK-T-δ A E K))
           (PK-∘ (PK-Id (Trace A E _) ⊗ PK-T-δ A E K)
           (PK-T A E f ⊗ PK-Id (Trace A E (Trace A E K))))
           (𝕃 A E _ (Trace A E _))
        (⊗-trade (PK-T A E f) (PK-T-δ A E K)))
  (PK-≡-trans
    (PK-asso (PK-Id _ ⊗ PK-T-δ A E _) (PK-T A E f ⊗ PK-Id _) (𝕃 A E _ (Trace A E _)))
  (PK-≡-trans
    (PK-∘-r≡ (PK-Id _ ⊗ PK-T-δ A E _)
       (PK-∘ (PK-T A E f ⊗ PK-Id _) (𝕃 A E _ (Trace A E _)))
       (PK-∘ (𝕃 A E _ (Trace A E _)) (PK-T A E (f ⊗ PK-Id _)))
       (𝕃-T-nat-left A E _ f f-tot ))
  (PK-≡-sym (PK-asso (PK-Id _ ⊗ PK-T-δ A E K) (𝕃 A E _ _) (PK-T A E (f ⊗ PK-Id _)))))))


ρ-runner-mult : (A E K : Set) → (X : Set)
  → PK-≡ (PK-∘ (PK-T-μ A E X ⊗ PK-Id _) (ρ-runner A E K X))
         (PK-∘ (ρ-runner A E K (Trace A E X)) (PK-∘ (PK-T A E (ρ-runner A E K X))
               (PK-T-μ A E (X × Trace A E K))))
ρ-runner-mult A E K X =
  PK-≡-trans
    (PK-≡-sym (PK-asso (PK-T-μ A E _ ⊗ PK-Id (Trace A E K))
              (PK-Id _ ⊗ PK-T-δ A E _) (𝕃 A E _ (Trace A E _))))
  (PK-≡-trans
    (PK-∘-l≡ (PK-∘ (PK-T-μ A E _ ⊗ PK-Id (Trace A E K))
           (PK-Id (Trace A E _) ⊗ PK-T-δ A E K))
           (PK-∘ (PK-Id (Trace A E _) ⊗ PK-T-δ A E K)
           (PK-T-μ A E _ ⊗ PK-Id (Trace A E (Trace A E K))))
           (𝕃 A E _ (Trace A E _))
-- Interchange order of (μ ⊗ I) and (I ⊗ δ)
        (⊗-trade (PK-T-μ A E _) (PK-T-δ A E K)))
  (PK-≡-trans
    (PK-asso (PK-Id _ ⊗ PK-T-δ A E _) (PK-T-μ A E _ ⊗ PK-Id _)
             (𝕃 A E _ (Trace A E _)))
  (PK-≡-trans
    (PK-∘-r≡ (PK-Id _ ⊗ PK-T-δ A E _)
             (PK-∘ (PK-T-μ A E _ ⊗ PK-Id _) (𝕃 A E _ (Trace A E _)))
             (PK-∘ (PK-Id (Trace A E (Trace A E X)) ⊗ PK-T-δ A E (Trace A E K))
               (PK-∘ (𝕃 A E (Trace A E X) (Trace A E (Trace A E K)))
               (PK-∘ (PK-T A E (𝕃 A E X (Trace A E K)))
               (PK-T-μ A E (X × Trace A E K)))))
-- Multiplication law for 𝕃
             (IL-mult-𝕃 A E _ _))
  (PK-≡-trans
    (PK-≡-sym (PK-asso (PK-Id _ ⊗ PK-T-δ A E _) (PK-Id _ ⊗ PK-T-δ A E (Trace A E K))
               (PK-∘ (𝕃 A E (Trace A E X) (Trace A E (Trace A E K)))
               (PK-∘ (PK-T A E (𝕃 A E X (Trace A E K)))
               (PK-T-μ A E (X × Trace A E K))))))
  (PK-≡-trans
    ((PK-∘-l≡ (PK-∘ (PK-Id _ ⊗ PK-T-δ A E _) (PK-Id _ ⊗ PK-T-δ A E _))
      _ (PK-∘ (𝕃 A E (Trace A E X) (Trace A E (Trace A E K)))
               (PK-∘ (PK-T A E (𝕃 A E X (Trace A E K)))
               (PK-T-μ A E (X × Trace A E K))))
        (PK-≡-trans
           (PK-≡-sym (⊗-∘ (PK-Id _) (PK-Id _) (PK-T-δ A E _) (PK-T-δ A E _)))
        (PK-≡-trans (⊗-≡-right (PK-∘ (PK-Id _) (PK-Id _))
-- Coassociativity of δ
            (PK-T-δ-asso A E _))
            (⊗-∘ (PK-Id _) (PK-Id _) (PK-T-δ A E _) (PK-T A E (PK-T-δ A E _))) ))))
  (PK-≡-trans
    (PK-asso (PK-Id _ ⊗ PK-T-δ A E _) (PK-Id _ ⊗ PK-T A E (PK-T-δ A E K))
             (PK-∘ (𝕃 A E (Trace A E X) (Trace A E (Trace A E K)))
                   (PK-∘ (PK-T A E (𝕃 A E X (Trace A E K)))
                         (PK-T-μ A E (X × Trace A E K)))))
  (PK-≡-trans
    (PK-∘-r≡ (PK-Id _ ⊗ PK-T-δ A E _)
             (PK-∘ (PK-Id _ ⊗ PK-T A E (PK-T-δ A E K))
             (PK-∘ (𝕃 A E (Trace A E X) (Trace A E (Trace A E K)))
                   (PK-∘ (PK-T A E (𝕃 A E X (Trace A E K)))
                         (PK-T-μ A E (X × Trace A E K)))))
             _
             (PK-≡-trans
               (PK-≡-sym (PK-asso (PK-Id _ ⊗ PK-T A E (PK-T-δ A E K))
                       (𝕃 A E (Trace A E X) (Trace A E (Trace A E K)))
                       (PK-∘ (PK-T A E (𝕃 A E X (Trace A E K)))
                         (PK-T-μ A E (X × Trace A E K)))))
               (PK-≡-trans (PK-∘-l≡
                  (PK-∘ (PK-Id _ ⊗ PK-T A E (PK-T-δ A E K))
                   (𝕃 A E (Trace A E X) (Trace A E (Trace A E K))))
                  _
                  (PK-∘ (PK-T A E (𝕃 A E X (Trace A E K)))
                   (PK-T-μ A E (X × Trace A E K)))
-- Naturality to get Tδ past 𝕃
                 (𝕃-T-nat-right A E _ (PK-T-δ A E K) (PK-T-δ-Total A E K)))
               (PK-≡-trans (PK-asso (𝕃 A E (Trace A E X) (Trace A E K))
                        (PK-T A E (PK-Id _ ⊗ (PK-T-δ A E K)))
                        (PK-∘ (PK-T A E (𝕃 A E X (Trace A E K)))
                           (PK-T-μ A E (X × Trace A E K))))
               (PK-∘-r≡ (𝕃 A E (Trace A E X) (Trace A E K))
                        (PK-∘ (PK-T A E (PK-Id _ ⊗ (PK-T-δ A E K)))
                             (PK-∘ (PK-T A E (𝕃 A E X (Trace A E K)))
                               (PK-T-μ A E (X × Trace A E K))))
                        _
                  (PK-≡-trans
                    (PK-≡-sym (PK-asso (PK-T A E (PK-Id _ ⊗ (PK-T-δ A E K)))
                              (PK-T A E (𝕃 A E X (Trace A E K)))
                              (PK-T-μ A E (X × Trace A E K))))
                    (PK-∘-l≡ (PK-∘ (PK-T A E (PK-Id _ ⊗ (PK-T-δ A E K)))
                                   (PK-T A E (𝕃 A E X (Trace A E K))))
                             (PK-T A E (ρ-runner A E K _))
                             (PK-T-μ A E (X × Trace A E K))
-- Compositionality on functor
                      (PK-≡-sym (PK-T-∘ A E (PK-Id _ ⊗ (PK-T-δ A E K))
                                (𝕃 A E X (Trace A E K))))
                             )))))))
  (PK-≡-sym (PK-asso (PK-Id _ ⊗ PK-T-δ A E _) (𝕃 A E (Trace A E X) (Trace A E K))
           (PK-∘ (PK-T A E (ρ-runner A E K _))
                  (PK-T-μ A E (X × Trace A E K))))))))))))


-- PK-∘ (PK-Id _ ⊗ PK-T-δ A E _)
--      (PK-∘ (𝕃 A E (Trace A E X) (Trace A E K))
--            (PK-∘ (PK-T A E (ρ-runner A E K _))
--                  (PK-T-μ A E (X × Trace A E K))))

-- PK-∘ (PK-Id _ ⊗ PK-T-δ A E _)
--      (PK-∘ (PK-∘ (𝕃 A E (Trace A E X) (Trace A E K))
--                  (PK-T A E (PK-Id _ ⊗ (PK-T-δ A E K))))
--            (PK-∘ (PK-T A E (𝕃 A E X (Trace A E K)))
--                  (PK-T-μ A E (X × Trace A E K))))


-- PK-∘ (PK-∘ (PK-Id _ ⊗ PK-T-δ A E _) (PK-Id _ ⊗ PK-T A E (PK-T-δ A E K)))
--      (PK-∘ (𝕃 A E (Trace A E X) (Trace A E (Trace A E K)))
--            (PK-∘ (PK-T A E (𝕃 A E X (Trace A E K)))
--                  (PK-T-μ A E (X × Trace A E K))))

-- (PK-≡-sym (⊗-∘ (PK-Id _) (PK-Id _) (PK-T-δ A E _) (PK-T-δ A E _)))

--proj₁ (ρ-runner-nat A E K f f-tot) (act x l , r) ((i , tt) , (tt , j) , k) = {!!}
--proj₁ (ρ-runner-nat A E K f f-tot) (err x , r) ((i , tt) , (tt , j) , k) = {!!}
--proj₂ (ρ-runner-nat A E K f f-tot) (l , r) i = {!!}

-- (𝕃-T-nat A E f (PK-Id _) f-tot ?)
