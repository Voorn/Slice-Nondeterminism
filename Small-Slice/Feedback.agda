module Small-Slice.Feedback where

open import Data.Unit
open import Data.Empty
open import Data.Sum renaming (map to map⊎)
open import Data.Nat hiding (_⊔_)
open import Data.Product renaming (map to map×)
open import Relation.Binary.Core
open import Function.Base
open import Relation.Binary.PropositionalEquality hiding ([_])


open import Small-Slice.Univ
open import Small-Slice.ND-functions
open import Small-Slice.Countable-Join
open import Small-Slice.Monoidal
open import Small-Slice.Cartesian


𝕌Hom-⊎-merge : {X : Set} → 𝕌Hom (X ⊎ X) X
𝕌Hom-⊎-merge (inj₁ x) = 𝕌SL-η x
𝕌Hom-⊎-merge (inj₂ x) = 𝕌SL-η x

𝕌Hom-⊎-merge-nat : {X Y : Set} → (f : 𝕌Hom X Y)
  → 𝕌Hom-≡ (𝕌Hom-∘ 𝕌Hom-⊎-merge (𝕌Hom-⊎ (f , f))) (𝕌Hom-∘ f 𝕌Hom-⊎-merge)
proj₁ (𝕌Hom-⊎-merge-nat f) (inj₁ x) (i , tt) = (tt , i) , refl
proj₁ (𝕌Hom-⊎-merge-nat f) (inj₂ x) (i , tt) = (tt , i) , refl
proj₂ (𝕌Hom-⊎-merge-nat f) (inj₁ x) (tt , i) = (i , tt) , refl
proj₂ (𝕌Hom-⊎-merge-nat f) (inj₂ x) (tt , i) = (i , tt) , refl



𝕌Iter : {X Y : Set} → 𝕌Hom X (Y ⊎ X) → ℕ → 𝕌Hom X Y
𝕌Iter H zero x = 𝕌SL-⊥
𝕌Iter H (suc n) = 𝕌Hom-∘ (𝕌-copr-glue (𝕌Hom-id _) (𝕌Iter H n)) H

𝕌Iter-≡ : {X Y : Set} → (H K : 𝕌Hom X (Y ⊎ X)) → 𝕌Hom-≡ H K → (n : ℕ)
  → 𝕌Hom-≡ (𝕌Iter H n) (𝕌Iter K n)
𝕌Iter-≡ H K H≡K zero = 𝕌Hom-≡-Refl {_} {_} {λ x → 𝕌SL-⊥}
𝕌Iter-≡ H K H≡K (suc n) = 𝕌Hom-∘≡ {_} {_} {_} {H} {K}
  {(𝕌-copr-glue (𝕌Hom-id _) (𝕌Iter H n))} {(𝕌-copr-glue (𝕌Hom-id _) (𝕌Iter K n))}
  H≡K (𝕌-copr-glue-≡ (𝕌Hom-≡-Refl {_} {_} {𝕌Hom-id _}) (𝕌Iter-≡ H K H≡K n))

Help2 : {X X' Y : Set} → (f : 𝕌Hom X X') → (H : 𝕌Hom X' (Y ⊎ X)) → (K : 𝕌Hom X' Y)
  → 𝕌Hom-≡ (𝕌Hom-∘ (𝕌-copr-glue (𝕌Hom-id _) (𝕌Hom-∘ K f)) H)
    (𝕌Hom-∘ (𝕌-copr-glue (𝕌Hom-id _) K) (𝕌Hom-∘ (𝕌Hom-⊎ (𝕌Hom-id _ , f)) H))
proj₁ (proj₁ (proj₁ (proj₁ (Help2 f H K) x (i , j)))) = i
proj₂ (proj₁ (proj₁ (proj₁ (Help2 f H K) x (i , j)))) with proj₂ (H x) i
... | inj₁ x' = tt
... | inj₂ y = proj₁ j
proj₂ (proj₁ (proj₁ (Help2 f H K) x (i , j))) with proj₂ (H x) i
... | inj₁ x' = tt
... | inj₂ y = proj₂ j
proj₂ (proj₁ (Help2 f H K) x (i , j)) with proj₂ (H x) i
... | inj₁ x' = refl
... | inj₂ y = refl
proj₁ (proj₁ (proj₂ (Help2 f H K) x ((i , j) , k))) = i
proj₂ (proj₁ (proj₂ (Help2 f H K) x ((i , j) , k))) with proj₂ (H x) i
... | inj₁ x' = tt
... | inj₂ y = j , k
proj₂ (proj₂ (Help2 f H K) x ((i , j) , k)) with proj₂ (H x) i
... | inj₁ x' = refl
... | inj₂ y = refl

𝕌Iter-nat₁ : {X X' Y : Set} → (f : 𝕌Hom X X') → (H : 𝕌Hom X' (Y ⊎ X)) → (n : ℕ)
  → 𝕌Hom-≡ (𝕌Iter (𝕌Hom-∘ H f) n) (𝕌Hom-∘ (𝕌Iter (𝕌Hom-∘ (𝕌Hom-⊎ (𝕌Hom-id _ , f)) H) n) f)
𝕌Iter-nat₁ f H zero = (λ {x ()}) , λ {x ()}
𝕌Iter-nat₁ f H (suc n) =
  𝕌Hom-≡-Trans
  {_} {_}
  {𝕌Hom-∘ (𝕌-copr-glue (𝕌Hom-id _) (𝕌Iter (𝕌Hom-∘ H f) n)) (𝕌Hom-∘ H f)}
  {𝕌Hom-∘ (𝕌Hom-∘ (𝕌-copr-glue (𝕌Hom-id _) (𝕌Iter (𝕌Hom-∘ H f) n)) H) f}
  {(𝕌Hom-∘ (𝕌Hom-∘ (𝕌-copr-glue (𝕌Hom-id _) (𝕌Iter (𝕌Hom-∘ (𝕌Hom-⊎ (𝕌Hom-id _ , f)) H) n))
                   (𝕌Hom-∘ (𝕌Hom-⊎ (𝕌Hom-id _ , f)) H))  f)}
    (𝕌Hom-≡-Symm {_} {_}
    {𝕌Hom-∘ (𝕌Hom-∘ (𝕌-copr-glue (𝕌Hom-id _) (𝕌Iter (𝕌Hom-∘ H f) n)) H) f}
    {𝕌Hom-∘ (𝕌-copr-glue (𝕌Hom-id _) (𝕌Iter (𝕌Hom-∘ H f) n)) (𝕌Hom-∘ H f)}
      (𝕌Hom-asso f H (𝕌-copr-glue (𝕌Hom-id _) (𝕌Iter (𝕌Hom-∘ H f) n))))
  (𝕌Hom-∘l≡ {_} {_} {_} f
  {(𝕌Hom-∘ (𝕌-copr-glue (𝕌Hom-id _) (𝕌Iter (𝕌Hom-∘ H f) n)) H)}
  {(𝕌Hom-∘ (𝕌-copr-glue (𝕌Hom-id _) (𝕌Iter (𝕌Hom-∘ (𝕌Hom-⊎ (𝕌Hom-id _ , f)) H) n))
                   (𝕌Hom-∘ (𝕌Hom-⊎ (𝕌Hom-id _ , f)) H))}
    (𝕌Hom-≡-Trans {_} {_}
    {𝕌Hom-∘ (𝕌-copr-glue (𝕌Hom-id _) (𝕌Iter (𝕌Hom-∘ H f) n)) H}
    {𝕌Hom-∘ (𝕌-copr-glue (𝕌Hom-id _)
         (𝕌Hom-∘ (𝕌Iter (𝕌Hom-∘ (𝕌Hom-⊎ (𝕌Hom-id _ , f)) H) n) f)) H}
    {𝕌Hom-∘ (𝕌-copr-glue (𝕌Hom-id _) (𝕌Iter (𝕌Hom-∘ (𝕌Hom-⊎ (𝕌Hom-id _ , f)) H) n))
        (𝕌Hom-∘ (𝕌Hom-⊎ (𝕌Hom-id _ , f)) H)}
      (𝕌Hom-∘l≡ {_} {_} {_} H
      {(𝕌-copr-glue (𝕌Hom-id _) (𝕌Iter (𝕌Hom-∘ H f) n))}
      {(𝕌-copr-glue (𝕌Hom-id _) (𝕌Hom-∘ (𝕌Iter (𝕌Hom-∘ (𝕌Hom-⊎ (𝕌Hom-id _ , f)) H) n) f))}
      (𝕌-copr-glue-≡
        (𝕌Hom-≡-Refl {_} {_} {𝕌Hom-id _})
        (𝕌Iter-nat₁ f H n)))
      (Help2 f H (𝕌Iter (𝕌Hom-∘ (𝕌Hom-⊎ (𝕌Hom-id _ , f)) H) n))))


Help3 : {X Y Y' : Set} → (H : 𝕌Hom X (Y ⊎ X)) → (f : 𝕌Hom Y Y') → (L : 𝕌Hom X Y)
  → 𝕌Hom-≡ (𝕌Hom-∘ (𝕌-copr-glue (𝕌Hom-id _) (𝕌Hom-∘ f L))
                   (𝕌Hom-∘ (𝕌Hom-⊎ (f , 𝕌Hom-id _)) H))
           (𝕌Hom-∘ f (𝕌Hom-∘ (𝕌-copr-glue (𝕌Hom-id _) L) H))
proj₁ (proj₁ (proj₁ (proj₁ (Help3 H f L) x ((i , j) , k)))) =  i
proj₂ (proj₁ (proj₁ (proj₁ (Help3 H f L) x ((i , j) , k)))) with proj₂ (H x) i
... | inj₁ y = tt
... | inj₂ x' = proj₁ k
proj₂ (proj₁ (proj₁ (Help3 H f L) x ((i , j) , k))) with proj₂ (H x) i
... | inj₁ y = j
... | inj₂ x' = proj₂ k
proj₂ (proj₁ (Help3 H f L) x ((i , j) , k)) with proj₂ (H x) i
... | inj₁ y = refl
... | inj₂ x' = refl
proj₁ (proj₁ (proj₁ (proj₂ (Help3 H f L) x ((i , j) , k)))) = i
proj₂ (proj₁ (proj₁ (proj₂ (Help3 H f L) x ((i , j) , k)))) with proj₂ (H x) i
... | inj₁ y = k
... | inj₂ x' = tt
proj₂ (proj₁ (proj₂ (Help3 H f L) x ((i , j) , k))) with proj₂ (H x) i
... | inj₁ y = tt
... | inj₂ x' = j , k
proj₂ (proj₂ (Help3 H f L) x ((i , j) , k)) with proj₂ (H x) i
... | inj₁ y = refl
... | inj₂ x' = refl


𝕌Iter-nat₂ : {X Y Y' : Set} → (f : 𝕌Hom Y Y') → (H : 𝕌Hom X (Y ⊎ X)) → (n : ℕ)
  → 𝕌Hom-≡ (𝕌Iter (𝕌Hom-∘ (𝕌Hom-⊎ (f , 𝕌Hom-id _)) H) n) (𝕌Hom-∘ f (𝕌Iter H n))
𝕌Iter-nat₂ f H zero = (λ {x ()}) , λ {x ()}
𝕌Iter-nat₂ f H (suc n) = 𝕌Hom-≡-Trans {_} {_}
  {𝕌Hom-∘ (𝕌-copr-glue (𝕌Hom-id _) (𝕌Iter (𝕌Hom-∘ (𝕌Hom-⊎ (f , 𝕌Hom-id _)) H) n))
                                   (𝕌Hom-∘ (𝕌Hom-⊎ (f , 𝕌Hom-id _)) H)}
  {𝕌Hom-∘ (𝕌-copr-glue (𝕌Hom-id _) (𝕌Hom-∘ f (𝕌Iter H n)))
                                   (𝕌Hom-∘ (𝕌Hom-⊎ (f , 𝕌Hom-id _)) H)}
  {𝕌Hom-∘ f (𝕌Hom-∘ (𝕌-copr-glue (𝕌Hom-id _) (𝕌Iter H n)) H)}
    (𝕌Hom-∘l≡ (𝕌Hom-∘ (𝕌Hom-⊎ (f , 𝕌Hom-id _)) H)
      {(𝕌-copr-glue (𝕌Hom-id _) (𝕌Iter (𝕌Hom-∘ (𝕌Hom-⊎ (f , 𝕌Hom-id _)) H) n))}
      {𝕌-copr-glue (𝕌Hom-id _) (𝕌Hom-∘ f (𝕌Iter H n))}
    (𝕌-copr-glue-≡ {_} {_} {_} {𝕌Hom-id _} {𝕌Hom-id _}
                               {𝕌Iter (𝕌Hom-∘ (𝕌Hom-⊎ (f , 𝕌Hom-id _)) H) n}
                               {𝕌Hom-∘ f (𝕌Iter H n)}
      (𝕌Hom-≡-Refl {_} {_} {𝕌Hom-id _})
      (𝕌Iter-nat₂ f H n)) )
  (Help3 H f (𝕌Iter H n))


-- Iter chain
𝕌Iter-chain : {X Y : Set} → (H : 𝕌Hom X (Y ⊎ X)) → 𝕌Hom-chain (𝕌Iter H)
proj₁ (proj₁ (𝕌Iter-chain H (suc n) x (i , j))) = i
proj₂ (proj₁ (𝕌Iter-chain H (suc n) x (i , j))) with proj₂ (H x) i
... | inj₁ y = tt
... | inj₂ x' = (proj₁ (proj₁ (𝕌Iter-chain H n x' j))) ,
  (proj₂ (proj₁ (𝕌Iter-chain H n x' j)))
proj₂ (𝕌Iter-chain H (suc n) x (i , j)) with proj₂ (H x) i
... | inj₁ y = refl
... | inj₂ x' = proj₂ (𝕌Iter-chain H n x' j)

⊎≡ : {X : Set} → (a : X) → Σ X λ b → (a ≡ b)
⊎≡ a = a , refl


𝕌Iterω : {X Y : Set} → 𝕌Hom X (Y ⊎ X) → 𝕌Hom X Y
𝕌Iterω H = 𝕌Hom-⋁ (𝕌Iter H)

𝕌Iterω-≡ : {X Y : Set} → (H K : 𝕌Hom X (Y ⊎ X)) → 𝕌Hom-≡ H K 
  → 𝕌Hom-≡ (𝕌Iterω H) (𝕌Iterω K)
𝕌Iterω-≡ H K H≡K = 𝕌Hom-⋁-≡ (𝕌Iter H) (𝕌Iter K) (𝕌Iter-≡ H K H≡K)

𝕌Iterω-unfold : {X Y : Set} → (H : 𝕌Hom X (Y ⊎ X))
  → 𝕌Hom-≡ (𝕌Hom-∘ (𝕌-copr-glue (𝕌Hom-id _) (𝕌Iterω H)) H) (𝕌Iterω H)
𝕌Iterω-unfold H = 𝕌Hom-≡-Trans {_} {_}
    {𝕌Hom-∘ (𝕌-copr-glue (𝕌Hom-id _) (𝕌Hom-⋁ (𝕌Iter H))) H}
    {𝕌Hom-⋁ (λ n → 𝕌Hom-∘ (𝕌-copr-glue (𝕌Hom-id _) (𝕌Iter H n)) H)}
    {𝕌Hom-⋁ (𝕌Iter H)}
      (𝕌Hom-≡-Trans {_} {_}
      {𝕌Hom-∘ (𝕌-copr-glue (𝕌Hom-id _) (𝕌Hom-⋁ (𝕌Iter H))) H}
      {𝕌Hom-∘ (𝕌Hom-⋁ (λ n → 𝕌-copr-glue (𝕌Hom-id _) (𝕌Iter H n))) H}
      {𝕌Hom-⋁ (λ n → 𝕌Hom-∘ (𝕌-copr-glue (𝕌Hom-id _) (𝕌Iter H n)) H)}
      (𝕌Hom-∘l≡ H {𝕌-copr-glue (𝕌Hom-id _) (𝕌Hom-⋁ (𝕌Iter H))}
         {𝕌Hom-⋁ (λ n → 𝕌-copr-glue (𝕌Hom-id _) (𝕌Iter H n))}
         (𝕌Hom-⋁-copr-glue-r (𝕌Hom-id _) (𝕌Iter H)))
      (𝕌Hom-⋁-l∘ H (λ n → 𝕌-copr-glue (𝕌Hom-id _) (𝕌Iter H n))))
    ((λ { x (n , i , j) → ((suc n) , (i , j)) , refl}) ,
    λ { x (suc n , i , j) → (n , (i , j)) , refl})

𝕌Iterω-nat₁ : {X X' Y : Set} → (f : 𝕌Hom X X') → (H : 𝕌Hom X' (Y ⊎ X))
  → 𝕌Hom-≡ (𝕌Iterω (𝕌Hom-∘ H f)) (𝕌Hom-∘ (𝕌Iterω (𝕌Hom-∘ (𝕌Hom-⊎ (𝕌Hom-id _ , f)) H)) f)
𝕌Iterω-nat₁ f H = 𝕌Hom-≡-Trans {_} {_}
  {𝕌Hom-⋁ (𝕌Iter (𝕌Hom-∘ H f))}
  {𝕌Hom-⋁ (λ n → 𝕌Hom-∘ (𝕌Iter (𝕌Hom-∘ (𝕌Hom-⊎ (𝕌Hom-id _ , f)) H) n) f)}
  {𝕌Hom-∘ (𝕌Iterω (𝕌Hom-∘ (𝕌Hom-⊎ (𝕌Hom-id _ , f)) H)) f}
    (𝕌Hom-⋁-≡ (𝕌Iter (𝕌Hom-∘ H f))
              (λ n → 𝕌Hom-∘ (𝕌Iter (𝕌Hom-∘ (𝕌Hom-⊎ (𝕌Hom-id _ , f)) H) n) f)
              (𝕌Iter-nat₁ f H))
    (𝕌Hom-≡-Symm {_} {_}
      {𝕌Hom-∘ (𝕌Iterω (𝕌Hom-∘ (𝕌Hom-⊎ (𝕌Hom-id _ , f)) H)) f}
      {𝕌Hom-⋁ (λ n → 𝕌Hom-∘ (𝕌Iter (𝕌Hom-∘ (𝕌Hom-⊎ (𝕌Hom-id _ , f)) H) n) f)}
        (𝕌Hom-⋁-l∘ f (𝕌Iter (𝕌Hom-∘ (𝕌Hom-⊎ (𝕌Hom-id _ , f)) H))) )


𝕌Iterω-nat₂ : {X Y Y' : Set} → (f : 𝕌Hom Y Y') → (H : 𝕌Hom X (Y ⊎ X))
  → 𝕌Hom-≡ (𝕌Iterω (𝕌Hom-∘ (𝕌Hom-⊎ (f , 𝕌Hom-id _)) H)) (𝕌Hom-∘ f (𝕌Iterω H))
𝕌Iterω-nat₂ f H = 𝕌Hom-≡-Trans {_} {_}
  {𝕌Iterω (𝕌Hom-∘ (𝕌Hom-⊎ (f , 𝕌Hom-id _)) H)}
  {𝕌Hom-⋁ (λ n → 𝕌Hom-∘ f (𝕌Iter H n))}
  {𝕌Hom-∘ f (𝕌Iterω H)}
      (𝕌Hom-⋁-≡ (𝕌Iter (𝕌Hom-∘ (𝕌Hom-⊎ (f , 𝕌Hom-id _)) H)) (λ n → 𝕌Hom-∘ f (𝕌Iter H n))
      λ n → 𝕌Iter-nat₂ f H n  )
  (𝕌Hom-≡-Symm {_} {_} {𝕌Hom-∘ f (𝕌Iterω H)} {𝕌Hom-⋁ (λ n → 𝕌Hom-∘ f (𝕌Iter H n))}
      (𝕌Hom-⋁-r∘ (𝕌Iter H) f))





-- Traced construction
𝕌Trace-part : {X Y C : Set} → (𝕌Hom X (Y ⊎ C)) → (𝕌Hom C (Y ⊎ C)) → (𝕌Hom X Y)
𝕌Trace-part H₀ H₁ = 𝕌Hom-∘ 𝕌Hom-⊎-merge (𝕌Hom-∘ (𝕌Hom-⊎ (𝕌Hom-id _ , 𝕌Iterω H₁)) H₀)

𝕌Trace : {X Y C : Set} → (𝕌Hom (X ⊎ C) (Y ⊎ C)) → 𝕌Hom X Y
𝕌Trace H = 𝕌Trace-part (𝕌Hom-∘ H 𝕌-copr-inj₁) (𝕌Hom-∘ H 𝕌-copr-inj₂)




