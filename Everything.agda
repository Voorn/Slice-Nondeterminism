module Everything where


-- This repository contains the development of formalisations for the category of relations,
-- via "Slice Nondeterminism", which shall be expanded upon in the future.

-- It also contains the partial formalisation of results from the paper:
-- "Nondeterministic Runners, A Model for Interleaving Algebraic Effects"
-- currently submitted to ICTAC 2022.


-- Slices
open import Slice.Base
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
