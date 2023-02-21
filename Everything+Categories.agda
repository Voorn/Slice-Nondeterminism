module Everything+Categories where

-- This is additional formalisation linking results to the Agda Categories library.
-- Please see details of the core code in:

open import Everything



-- Definition of the category of slice functions when allowing a small universe
-- of indexing sets, together with a variety of properties:
-- Cartesian, cocartesian, and symmetric monoidal over ×

open import Small-Slice.SF-Cat


-- Definition of the category of slice functions when allowing any set as slice index

open import Slice-Functions.Category


-- Slice functions is equivalent to the category of relations

open import Relations.Category
