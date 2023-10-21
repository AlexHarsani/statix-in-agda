module Proofs (L : Set) where

open import Data.List
open import Relation.Binary.PropositionalEquality

open import Constraint L
open import Graph L

postulate
    gf-wf-proof : { gf : GraphFragment } → WellFormedness gf
    gf-empty-proof : { gf : GraphFragment } → Empty gf
    gf-partition-proof : { gf1 gf2 gf3 : GraphFragment } → Partition gf1 gf2 gf3

emp-satisfied : { g : Graph } → { gf : GraphFragment } → Satisfies g emp gf
emp-satisfied = satisfiesEmpty { gfEmptyProof = gf-empty-proof } { gfWfProof = gf-wf-proof }

compound-satisfied : { g : Graph } → { gf : GraphFragment } → Satisfies g (emp * emp) gf
compound-satisfied = satisfiesCompound
    { gf2 = < [] , [] > } {gf3 = < [] , [] > }
    {gf1WfProof = gf-wf-proof} {gf2WfProof = gf-wf-proof} {gf3WfProof = gf-wf-proof} 
    {gfPartitionProof = gf-partition-proof} 
    emp-satisfied emp-satisfied

term-eq-satisfied : { g : Graph } → { gf : GraphFragment } → Satisfies g ((var "x") =t= (var "x")) gf
term-eq-satisfied = satisfiesTermEq { gfEmptyProof = gf-empty-proof } { gfWfProof = gf-wf-proof } { termEq = refl }