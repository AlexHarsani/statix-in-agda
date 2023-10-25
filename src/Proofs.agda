module Proofs (L : Set) where

open import Data.List
open import Relation.Binary.PropositionalEquality

open import Constraint L
open import Graph L

-- Some concrete examples of proving constraint satisfiability

-- Some axioms for properties defined in Graph.adga,
-- that are necessary for proofs of satisfiability.
postulate
    gf-wf-proof : { gf : GraphFragment } → WellFormedness gf
    gf-empty-proof : { gf : GraphFragment } → Empty gf
    gf-partition-proof : { gf1 gf2 gf3 : GraphFragment } → Partition gf1 gf2 gf3
    ts-wf-proof : { ts : TermSet } → WellFormedTermSet ts
    min-ts-proof : { ts ts' : TermSet } → { R : Relation } → ts ≡ minTermSet ts' R

-- Empty constraint proof
emp-constraint = emp

emp-satisfied : { g : Graph } → { gf : GraphFragment } → Satisfies g emp-constraint gf
emp-satisfied = satisfiesEmpty { gfEmptyProof = gf-empty-proof } { gfWfProof = gf-wf-proof }

-- Compound constraint proof
compound-constraint = (emp * emp)

compound-satisfied : { g : Graph } → { gf1 gf2 : GraphFragment } → Satisfies g compound-constraint (gf1 ⊔ gf2)
compound-satisfied = satisfiesCompound
    {gf1WfProof = gf-wf-proof} {gf2WfProof = gf-wf-proof} {gfDuWfProof = gf-wf-proof} 
    {gfPartitionProof = gf-partition-proof} 
    (satisfiesEmpty { gfEmptyProof = gf-empty-proof } { gfWfProof = gf-wf-proof }) 
    (satisfiesEmpty { gfEmptyProof = gf-empty-proof } { gfWfProof = gf-wf-proof })

-- Term equality constraint proof
term-eq-constraint = ((var "x") =t= (var "x"))

term-eq-satisfied : { g : Graph } → { gf : GraphFragment } → Satisfies g term-eq-constraint gf
term-eq-satisfied = satisfiesTermEq { gfEmptyProof = gf-empty-proof } { gfWfProof = gf-wf-proof } { termEq = refl }

-- Exists constraint proof
exists-constraint = (existsT "x" ((var "x") =t= (var "y")))

exists-satisfied : { g : Graph } → { gf : GraphFragment } → Satisfies g exists-constraint gf
exists-satisfied = satisfiesExists 
    { gfWfProof = gf-wf-proof } 
    { t = (var "y") } 
    (satisfiesTermEq { gfEmptyProof = gf-empty-proof } { gfWfProof = gf-wf-proof } { termEq = refl })

-- Single constraint proof
single-constraint = (single (var "x") ( terms ((var "x") ∷ []) ))

single-satisfied : { g : Graph } → { gf : GraphFragment } → {t : Term } → Satisfies g single-constraint gf
single-satisfied = satisfiesSingle 
    { tsSingletonProof = refl } 
    { tsWfProof = ts-wf-proof } 
    { gfEmptyProof = gf-empty-proof } 
    { gfWfProof = gf-wf-proof }

-- Min constraint proof
-- preorder relation as specified on page 11 of Knowing When to Ask 
postulate
    R : Relation
    
min-constraint = (min (terms ((var "x") ∷ [])) R (terms ((var "x") ∷ [])))

min-satisfied : { g : Graph } → { gf : GraphFragment } → Satisfies g min-constraint gf
min-satisfied = satisfiesMin { gfEmptyProof = gf-empty-proof } { gfWfProof = gf-wf-proof } { termSetEq = min-ts-proof }

-- Forall empty proof
forall-empty-constraint = (forallT "x" (terms []) emp)

forall-empty-satisfied : { g : Graph } → { gf : GraphFragment } → Satisfies g forall-empty-constraint gf
forall-empty-satisfied = satisfiesForallEmpty 
    { tsEmptyProof = refl } 
    { gfEmptyProof = gf-empty-proof } 
    { gfWfProof = gf-wf-proof }

-- Forall constraint proof
forall-constraint = forallT "x" (terms ((var "y") ∷ [])) (((var "x") =t= (var "y")))

forall-satisfied : { g : Graph } → { gf1 gf2 : GraphFragment } → Satisfies g forall-constraint (gf1 ⊔ gf2)
forall-satisfied = satisfiesForall 
    { tsWfProof = ts-wf-proof } { ts2WfProof = ts-wf-proof }
    { gf1WfProof = gf-wf-proof } { gf2WfProof = gf-wf-proof } { gfDuWfProof = gf-wf-proof }
    { gfPartitionProof = gf-partition-proof }
    (satisfiesTermEq { gfEmptyProof = gf-empty-proof } { gfWfProof = gf-wf-proof }  { termEq = refl } ) 
    (satisfiesForallEmpty { tsEmptyProof = refl } { gfEmptyProof = gf-empty-proof } { gfWfProof = gf-wf-proof } )