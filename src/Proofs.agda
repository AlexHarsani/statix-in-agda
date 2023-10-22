module Proofs (L : Set) where

open import Data.List
open import Relation.Binary.PropositionalEquality

open import Constraint L
open import Graph L

postulate
    gf-wf-proof : { gf : GraphFragment } → WellFormedness gf
    gf-empty-proof : { gf : GraphFragment } → Empty gf
    gf-partition-proof : { gf1 gf2 gf3 : GraphFragment } → Partition gf1 gf2 gf3
    ts-singleton-proof : { ts : TermSet } → { t : Term } → SingletonTermSet t ts
    ts-wf-proof : { ts : TermSet } → WellFormedTermSet ts
    min-ts-proof : { ts ts' : TermSet } → { R : Relation } → ts ≡ minTermSet ts' R


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

exists-satisfied : { g : Graph } → { gf : GraphFragment } → Satisfies g (existsC "x" ((var "x") =t= (var "y"))) gf
exists-satisfied = satisfiesExists 
    { gfWfProof = gf-wf-proof } 
    { t = (var "y") } 
    (satisfiesTermEq { gfEmptyProof = gf-empty-proof } { gfWfProof = gf-wf-proof } { termEq = refl })

single-satisfied : { g : Graph } → { gf : GraphFragment } → {t : Term } → Satisfies g (single (var "x") ( terms ((var "x") ∷ []) )) gf
single-satisfied = satisfiesSingle 
    { tsSingletonProof = ts-singleton-proof } 
    { tsWfProof = ts-wf-proof } 
    { gfEmptyProof = gf-empty-proof } 
    { gfWfProof = gf-wf-proof }

min-satisfied : { g : Graph } → { gf : GraphFragment } → { R : Relation } → Satisfies g (min (terms ((var "x") ∷ [])) R (terms ((var "x") ∷ []))) gf
min-satisfied = satisfiesMin { gfEmptyProof = gf-empty-proof } { gfWfProof = gf-wf-proof } { termSetEq = min-ts-proof }