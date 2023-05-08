module Everything where

-- Tested in Agda version 2.6.1

-- The formalisation linked in this code is compatible with Agda's standard library
-- The formalisation linked in the code of Everything+Categories.agda necessarily uses
-- the optional "Agda categories" library

-- This repository contains the development of formalisations for the category of relations,
-- via a technique self-named "Slice Nondeterminism".

-- A paper on Slice Nondeterminism is currently submitted for evaluation to ITP 2023.
-- The paper focusses on the formalisation done in the Small-Slice subfolder,
-- though it also references some other material

-- The development also contains the partial formalisation of results from the paper:
-- "Nondeterministic Runners, A Model for Interleaving Algebraic Effects"
-- currently submitted to ICTAC 2022.


-- Small Slices: the theory of Slice nondeterminism using a small universe of indexing sets


-- Basics

-- slice endo functor on a small universe of indexing sets (Section 2.1-2.4)
open import Small-Slice.Univ

-- kleisli category over the small slice endofunctor (Section 3.1)
open import Small-Slice.ND-functions

-- Comparison of methods: tossing coins (Section 7.1)
open import Method-Comparison



-- Structure of the category

-- optional properties of morphisms, which specify subcategories (Section 3.2 and 3.3)
open import Small-Slice.Substructure

-- the category has products and coproducts (Section 4.1)
open import Small-Slice.Cartesian

-- the category has a monoidal structure associated to the Cartesian product on sets (Section 4.3)
open import Small-Slice.Monoidal



-- Joins and recursion

-- the category can be enriched with a join semi-lattic structure (Section 2.5 and 4.2)
open import Small-Slice.Semi-Lattice

-- countable joins and omega chains (Section 2.5 and 4.2)
open import Small-Slice.Countable-Join

-- feedback and iteration, towards traced monoidal (Section 6.2)
open import Small-Slice.Feedback



-- Example models

-- free monads from Set lifted to reversible structures as nondeterministic processes (Section 5)
open import Small-Slice.Container

-- marbles: interleaving for lists, a model for concurrency (Section 6.1)
open import Small-Slice.Marbles

-- labelled transition systems (Section 6.3)
open import Small-Slice.LTS

-- Untyped call-by-value lambda calculus with nondeterminism
open import Small-Slice.Lambda




-- =====================================================================================

-- Big Slices: Earlier development using the universe of all sets space of indexing sets

-- Base definition of the category of slices
open import Slice.Base

-- Lattice structure with respect to order induced by morphism existence
open import Slice.Lattice



-- Slice Functions

-- The category of relations done directionally
open import Slice-Functions.Base

-- The dagger operation
open import Slice-Functions.Dagger

-- Wide subcategories
open import Slice-Functions.Subcategories

-- The product in the category of relations, given by disjoint union
open import Slice-Functions.Product

-- Monoidal closed structure by lifting the Cartesian product from Set
open import Slice-Functions.Monoidal

-- Additional structure on the monoidal product: copy, delete, etc.
open import Slice-Functions.Structure



-- Other representations of the category of relations

-- The category of spans
open import Relations.Span

-- The category of extensional relations
open import Relations.Ext-Rel

-- Equivalences of categories
open import Relations.Cat-Equivalences


-- Free monads from Set lifted to the category of relations

-- Free monad over container, a.k.a. inductive trees
open import Monads.Free-Monad

-- Trace monad: The free monad with only unary (actions) and nullary operations (exceptions)
open import Monads.Trace

-- The branch morphism: a monad morphism from trees to traces describing its branches
open import Monads.Branch-Morphism



-- Examples

-- Iterative nondeterministic process
open import Examples.Iterative

-- Labelled transition system
open import Examples.Transition



-- Interleaving concurrency development

-- The parallel operations on Traces from the aforementioned paper,
-- its naturality, relation to strength, symmetry and associativity
open import Parallel.Base

-- Properties of the parallel operations regarding the monad and comonad structur on Traces
open import Parallel.Monoidal

-- The parallel runner
open import Parallel.Runner



-- Trace runners and stateful relators defined with them

-- Trace runners in general
open import Runner.Trace-Runner

-- Trace relators: Lifting relations on sets to relations on traces
-- Contains all the main properties for monadic relators
open import Runner.Trace-Relator

-- Example: error relator with set of undetectable errors
open import Runner.Error-Relator

-- Stateful relators, constructed using runners, state relations and state worlds
open import Runner.Stateful-Relator
