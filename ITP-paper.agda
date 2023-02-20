module ITP-paper where

-- This file imports terms associated to definitions and proofs from the ITP 2023 paper
-- submission "Slice Nondeterminism". Comments refer to name of definition or resul in
-- in the paper, and a selection of in-line definition and results are included too.


import Small-Slice.ND-functions
import Small-Slice.Substructure
import Small-Slice.Cartesian


-------------------------------------
-- Section 2:  Powerset via Slices --
-------------------------------------

import Small-Slice.Univ


-- Section 2.1:  A Universe for Indexing Sets

-- Definition 1
𝕌-names = Small-Slice.Univ.𝕌
𝕌-denotations : 𝕌-names → Set
𝕌-denotations = Small-Slice.Univ.𝕌S

-- Definition 2
SL = Small-Slice.Univ.𝕌SL

SL-maps                 =  Small-Slice.Univ.𝕌SL-fun
SL-functor-identity     =  Small-Slice.Univ.𝕌SL-fun-id
SL-functor-composition  =  Small-Slice.Univ.𝕌SL-fun-∘


-- Section 2.2:  Relations on Slices

-- Definition 3
Γ𝕌 = Small-Slice.Univ.𝕌Γ

-- preservation properties
Γ-preserves-reflexivity    =  Small-Slice.Univ.𝕌Γ-refl
Γ-preserves-transitivity   =  Small-Slice.Univ.𝕌Γ-tran
Γ-preserves-relation-order =  Small-Slice.Univ.𝕌Γ-⊂
Γ-preserves-maps           =  Small-Slice.Univ.𝕌SL-fun-cong


-- Section 2.3:  A Monad on Setoids

-- Proposition 4
⟨⟩                  =  Small-Slice.Univ.𝕌SL-η
⟨⟩-set-natural      =  Small-Slice.Univ.𝕌SL-η-nat
⟨⟩-setoid-natural   =  Small-Slice.Univ.𝕌SL-η-setoid

⊔                  =  Small-Slice.Univ.𝕌SL-μ
⊔-set-natural      =  Small-Slice.Univ.𝕌SL-μ-nat
⊔-setoid-natural   =  Small-Slice.Univ.𝕌SL-μ-setoid

SL-setoid-left-unitality   =  Small-Slice.Univ.𝕌SL-setoid-luni
SL-setoid-right-unitality  =  Small-Slice.Univ.𝕌SL-setoid-runi
SL-setoid-associativity    =  Small-Slice.Univ.𝕌SL-setoid-asso


-- Section 2.4:  A Kleisli Triple on Sets

Kleisli-lifting      =  Small-Slice.Univ.𝕌SL-κ

Kleisli-preserves-≡  =  Small-Slice.Univ.𝕌SL-κ-≡
Kleisli-property-1   =  Small-Slice.Univ.𝕌SL-Kleisli-1
Kleisli-property-2   =  Small-Slice.Univ.𝕌SL-Kleisli-2
Kleisli-property-3   =  Small-Slice.Univ.𝕌SL-Kleisli-3


-- Section 2.5:  Semi Lattice Structure

⊑ = Small-Slice.Univ.𝕌SL→

-- Lemma 5

import Small-Slice.Semi-Lattice
import Small-Slice.Countable-Join

𝕌SL-⋁        =  Small-Slice.Countable-Join.𝕌SL-⋁
𝕌SL-upper    =  Small-Slice.Countable-Join.𝕌SL-⋁-upper
𝕌SL-supremum =  Small-Slice.Countable-Join.𝕌SL-⋁-supremum

⊘            =  Small-Slice.Univ.𝕌SL-⊥
binary-∨      =  Small-Slice.Semi-Lattice.𝕌SL-∨  


--------------------------------------------
-- Section 3:  Nondeterministic Functions --
--------------------------------------------

-- Subsection 3.1:  E-categories

-- Definition 7
SNF-map              =  Small-Slice.ND-functions.𝕌Hom
SNF-map-equivalence  =  Small-Slice.ND-functions.𝕌Hom-≡

SNF-map-id           =  Small-Slice.ND-functions.𝕌Hom-id
SNF-map-composition  =  Small-Slice.ND-functions.𝕌Hom-∘


-- Subsection 3.2:  Functions and Variations

SNF→Rel-functor  =  Small-Slice.Substructure.𝕌→Rel-Hom

Total          =  Small-Slice.Substructure.𝕌-Total
Deterministic  =  Small-Slice.Substructure.𝕌-Deter
Surjective     =  Small-Slice.Substructure.𝕌-Surje
Injective      =  Small-Slice.Substructure.𝕌-Injec

epimorphism-conditions   =  Small-Slice.Substructure.𝕌-epi-con
monomorphism-conditions  =  Small-Slice.Substructure.𝕌-mono-con
total-deterministic-is-set-1  =  Small-Slice.Substructure.𝕊→𝕌→𝕊
total-deterministic-is-set-2  =  Small-Slice.Substructure.𝕌→𝕊→𝕌

-- Subsection 3.3:  Morphisms with Daggers

-- Definition 9
Eachothers-dagger   =  Small-Slice.Substructure.𝕌-is-†

Morphism-is-daggerable  =  Small-Slice.Substructure.𝕌-Dagger



----------------------------------------
-- Section 4:  Categorical Structures --
----------------------------------------


Set→SNF-functor  =  Small-Slice.ND-functions.𝕌Hom-fun


-- Subsection 4.1:  Products and Coproducts

-- Lemma 10
terminal-map            =  Small-Slice.Cartesian.𝕌-termin
terminal-map-is-unique  =  Small-Slice.Cartesian.𝕌-termin-unique
initial-map             =  Small-Slice.Cartesian.𝕌-initia
initial-map-is-unique   =  Small-Slice.Cartesian.𝕌-initia-unique


coproduct-injection-0  =  Small-Slice.Cartesian.𝕌-copr-inj₁  
coproduct-injection-1  =  Small-Slice.Cartesian.𝕌-copr-inj₂

-- Lemma 11
coproduct-universal-property  =  Small-Slice.Cartesian.𝕌-copr-glue-unique


product-projection-0  =  Small-Slice.Cartesian.𝕌-prod-proj₁  
product-projection-1  =  Small-Slice.Cartesian.𝕌-prod-proj₂

-- Lemma 12
product-universal-property  =  Small-Slice.Cartesian.𝕌-prod-glue-unique


-- Subsection 4.2:  Semi Lattice Enriched

join-on-morphisms  =  Small-Slice.Countable-Join.𝕌Hom-⋁

-- Definition 14
ω-chain  =  Small-Slice.Countable-Join.𝕌Hom-chain

composition-preserves-chains  =  Small-Slice.Countable-Join.𝕌Hom-chain-∘
⊎-product-preserves-chains    =  Small-Slice.Countable-Join.𝕌Hom-chain-⊎
⊗-product-preserves-chains   =  Small-Slice.Countable-Join.𝕌Hom-chain-⊗

composition-merges-chains     =  Small-Slice.Countable-Join.𝕌Hom-⋁-∘
⊎-product-merges-chains       =  Small-Slice.Countable-Join.𝕌Hom-⋁-⊎
⊗-product--merges-chains     =  Small-Slice.Countable-Join.𝕌Hom-⋁-⊗


-- Subsection 4.3:  Monoidal

import Small-Slice.Monoidal

⊗-Monoidal-bifunctor  =  Small-Slice.Monoidal.𝕌Hom-⊗

⊗-comonoid-u  =  Small-Slice.Monoidal.𝕌Hom-delete  
⊗-comonoid-c  =  Small-Slice.Monoidal.𝕌Hom-copy

-------------------------------------------------------
-- Section 5:  Inductive Nondeterministic Structures --
-------------------------------------------------------

import Small-Slice.Container

𝕌-container = Small-Slice.Container.𝕌-Sig

-- Definition 15
F-object  =  Small-Slice.Container.Free
F-map     =  Small-Slice.Container.SF-F
F-η       =  Small-Slice.Container.Free-η
F-μ       =  Small-Slice.Container.Free-μ

-- Definition 16
Pos    =  Small-Slice.Container.Pos

-- Definition 17
T-map  =  Small-Slice.Container.SF-F

choice-relation  =  Small-Slice.Container.Free-dist

-- Theorem 18
T-completeness  =  Small-Slice.Container.FD-complete
T-soundness     =  Small-Slice.Container.FD-sound

-- Subsection 5.2:  Monad and Comonad Structure

T-η             =  Small-Slice.Container.𝕌Free-η
T-η-is-natural  =  Small-Slice.Container.𝕌Free-η-nat

T-μ             =  Small-Slice.Container.𝕌Free-μ
T-μ-is-natural  =  Small-Slice.Container.𝕌Free-μ-nat

-- Lemma 19
T-is-left-unital   =  Small-Slice.Container.𝕌Free-luni
T-is-right-unital  =  Small-Slice.Container.𝕌Free-runi
T-is-associative   =  Small-Slice.Container.𝕌Free-asso

T-ε                    =  Small-Slice.Container.𝕌Free-ε
T-η-and-ε-are-daggers  =  Small-Slice.Container.𝕌Free-η-ε-†

T-δ                    =  Small-Slice.Container.𝕌Free-δ
T-μ-and-δ-are-daggers  =  Small-Slice.Container.𝕌Free-μ-δ-†

T-equation-1  =  Small-Slice.Container.𝕌Free-eq-ηε
T-equation-2  =  Small-Slice.Container.𝕌Free-eq-δμ
T-equation-3  =  Small-Slice.Container.𝕌Free-eq-με



-----------------------------------
-- Section 6:  Example Processes --
-----------------------------------

-- Subsection 6.1:  Interleaving Concurrency

import Small-Slice.Marbles

-- Definition 20
∥   =  Small-Slice.Marbles.𝕃-∥
∥l  =  Small-Slice.Marbles.𝕃-∥l
∥r  =  Small-Slice.Marbles.𝕃-∥r


-- Proposition 21
∥-unitality      =  Small-Slice.Marbles.𝕃-∥-luni
∥-associativity  =  Small-Slice.Marbles.𝕃-∥-asso
∥-commutativity  =  Small-Slice.Marbles.𝕃-∥-com


-- Subsection 6.2:  Iterated processes

import Small-Slice.Feedback

Iter   =  Small-Slice.Feedback.𝕌Iter
Iterω  =  Small-Slice.Feedback.𝕌Iterω

Iter-is-an-ω-chain  =  Small-Slice.Feedback.𝕌Iter-chain
Iter-preserves-∼    =  Small-Slice.Feedback.𝕌Iter-≡
Iter-naturality-1   =  Small-Slice.Feedback.𝕌Iter-nat₁
Iter-naturality-2   =  Small-Slice.Feedback.𝕌Iter-nat₂

Iterω-preserves-∼   =  Small-Slice.Feedback.𝕌Iterω-≡
Iterω-naturality-1  =  Small-Slice.Feedback.𝕌Iterω-nat₁
Iterω-naturality-2  =  Small-Slice.Feedback.𝕌Iterω-nat₂
Iterω-unfolding     =  Small-Slice.Feedback.𝕌Iterω-unfold


-- Subsection 6.3:  Labelled transition systems

import Small-Slice.LTS

-- Definition 22 (labelled transition system)
LTS  =  Small-Slice.LTS.LTS

LTSCol     =  Small-Slice.LTS.LTS-Col
LTSColω    =  Small-Slice.LTS.LTS-Colω
LTSaccept  =  Small-Slice.LTS.LTS-accept

-- Proposition 23
LTS-soundness     =  Small-Slice.LTS.LTS-sound
LTS-completeness  =  Small-Slice.LTS.LTS-complete



-----------------------------
-- Section 7:  Conclusions --
-----------------------------


-- Subsection 7.1:  Method Comparison

import  Method-Comparison

Erel-ℕ-toss   =   Method-Comparison.Erel-ℕ-toss
Span-ℕ-toss   =   Method-Comparison.Span-ℕ-toss
Slic-ℕ-toss   =   Method-Comparison.Slic-ℕ-toss

Erel-ℕ-example  =  Method-Comparison.Erel-ℕ-example
Span-ℕ-example  =  Method-Comparison.Span-ℕ-example
Slic-ℕ-example  =  Method-Comparison.Slic-ℕ-example



----------------------------------------------------
-- AGDA CATEGORIES LIBRARY NEEDED FOR TERMS BELOW --
----------------------------------------------------

-- -- Uncomment

-- -- Subsection 7.2:  Agda Categories Library

-- import Small-Slice.SF-Cat
-- import Small-Slice.Setoid
-- import Relations.Category

-- SNF-is-a-category      =  Small-Slice.SF-Cat.SSF-Cat
-- SNF-is-monoidal-wrt-×  =  Small-Slice.SF-Cat.⊗-Monoidal 
-- SNF-is-braided-wrt-×   =  Small-Slice.SF-Cat.⊗-braided  
-- SNF-is-Cartesian       =  Small-Slice.SF-Cat.SSF-Cartesian
-- SNF-is-coCartesian     =  Small-Slice.SF-Cat.SSF-Cocartesian

-- SL-forms-a-Setoid-Monad  =  Small-Slice.Setoid.Pow-Monad

-- -- Theorem 24
-- SNF-≡-Rel  =  Relations.Category.SF≡ER
