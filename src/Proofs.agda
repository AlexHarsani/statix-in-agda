module Proofs (L : Set) where

open import Data.List

open import Constraint L
open import Graph L

postulate
    gf-wf-proof : { gf : GraphFragment } → WellFormedness gf
    gf-empty-proof : { gf : GraphFragment } → Empty gf

emp-satisfied : { g : Graph } → { gf : GraphFragment } → Satisfies g emp gf
emp-satisfied = satisfiesEmpty { gfEmptyProof = gf-empty-proof } { gfWfProof = gf-wf-proof }