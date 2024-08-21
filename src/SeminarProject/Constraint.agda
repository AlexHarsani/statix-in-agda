module Constraint (L : Set) where

open import Data.List
open import Data.String
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

open import Graph L

-- Constraints syntax based on figure 6 of Knowing When to Ask
data Constraint : Set where
    -- true
    emp : Constraint
    -- false
    false : Constraint
    -- separating conjunction
    _*_ : Constraint → Constraint → Constraint
    -- term equality
    _=t=_ : Term → Term → Constraint
    -- existential quantification
    existsT : String → Constraint → Constraint
    -- set singletons
    single : Term → TermSet → Constraint
    -- minimum
    min : TermSet → Relation → TermSet → Constraint
    -- forall
    forallT : String → TermSet → Constraint → Constraint

mutual
    -- helper function for replace term, used for compound terms
    mapReplaceTerm : String → Term → List Term → List Term
    mapReplaceTerm x newTerm (t ∷ ts) = (replaceTerm newTerm x t) ∷ mapReplaceTerm x newTerm ts
    mapReplaceTerm _ _ [] = []

    -- Replaces quantified variables by new term
    replaceTerm : Term → String → Term → Term
    replaceTerm newTerm x oldTerm@(var y) with (x ≟ y)
    ... | yes _ = newTerm
    ... | no _ = oldTerm
    replaceTerm newTerm x (compound f ts) = compound f (mapReplaceTerm x newTerm ts)
    replaceTerm newTerm x oldTerm = oldTerm

-- Substitute function for exists and forall constraints
substitute : Constraint → String → Term → Constraint
substitute emp x t = emp
substitute false x t = false
substitute (c1 * c2) x t = substitute c1 x t * substitute c2 x t
substitute (t1 =t= t2) x t = (replaceTerm t x t1) =t= (replaceTerm t x t2)
substitute (single t1 (terms ts)) x t2 = single (replaceTerm t2 x t1) (terms (map (replaceTerm t2 x) ts))
substitute (min (terms ts1) R (terms ts2)) x t = min ((terms (map (replaceTerm t x) ts1))) R (((terms (map (replaceTerm t x) ts2))))
substitute (existsT y c) x t with (x ≟ y)
... | yes _ = existsT y c
... | no _ = existsT y (substitute c x t)
substitute (forallT y (terms ts) c) x t with (x ≟ y)
... | yes _ = forallT y (terms ts) c
... | no _ = forallT y ((terms (map ((replaceTerm t x)) ts))) (substitute c x t)

-- Constraint satisfiability based on figure 7 of Knowing When to Ask
data Satisfies : Graph → Constraint → GraphFragment → Set where
    -- EMP
    satisfiesEmpty : { g : Graph } → 
        { gf : GraphFragment } →
        { gfEmptyProof : Empty gf } →
        { gfWfProof : WellFormedness gf } → 
        Satisfies g emp gf
    -- CONJ
    satisfiesCompound : { g : Graph } → 
        { c1 c2 : Constraint } → 
        { gf1 gf2 gf3 : GraphFragment } → 
        { gf1WfProof : WellFormedness gf1 } →
        { gf2WfProof : WellFormedness gf2 } →
        { gf3WfProof : WellFormedness gf3 } →
        { gfPartitionProof : Partition gf3 gf1 gf2 } → 
        Satisfies g c1 gf1 →
        Satisfies g c2 gf2 →
        Satisfies g (c1 * c2) gf3
    -- EQ
    satisfiesTermEq : {g : Graph } → 
        { gf : GraphFragment } →
        { gfEmptyProof : Empty gf } →
        { gfWfProof : WellFormedness gf } →
        { t1 t2 : Term } →
        { termEq : t1 ≡ t2 } →
        Satisfies g (t1 =t= t2) gf
    -- EXISTS
    satisfiesExists : { g : Graph } → 
        { c : Constraint } → 
        { x : String } → 
        { gf : GraphFragment } →
        { gfWfProof : WellFormedness gf }
        { t : Term } →
        Satisfies g (substitute c x t) gf →
        Satisfies g (existsT x c) gf
    -- SINGLETON
    satisfiesSingle : { g : Graph } →
        { t : Term } →
        { ts : TermSet } →
        { tsSingletonProof : ts ≡ (terms (t ∷ [])) } →
        { tsWfProof : WellFormedTermSet ts } →
        { gf : GraphFragment } →
        { gfEmptyProof : Empty gf } →
        { gfWfProof : WellFormedness gf } →
        Satisfies g (single t ts) gf
    -- MIN
    satisfiesMin : { g : Graph } → 
        { t t' : TermSet } →
        { R : Relation } →
        { gf : GraphFragment } →
        { gfEmptyProof : Empty gf } →
        { gfWfProof : WellFormedness gf } → 
        { termSetEq : t' ≡ minTermSet t R } →
        Satisfies g (min t R t') gf
    -- FORALL-EMPTY
    satisfiesForallEmpty : { g : Graph } → 
        { x : String } →
        { ts : TermSet } →
        { tsEmptyProof : ts ≡ (terms []) } →
        { c : Constraint } →
        { gf : GraphFragment } →
        { gfEmptyProof : Empty gf } →
        { gfWfProof : WellFormedness gf } → 
        Satisfies g (forallT x ts c) gf
    -- FORALL
    satisfiesForall : { g : Graph } → 
        { x : String } →
        { t : Term } →
        { ts : List Term } →
        { tsWfProof : WellFormedTermSet (terms ts) } →
        { ts2WfProof : WellFormedTermSet (terms (t ∷ ts)) } →
        { c : Constraint } →
        { gf1 gf2 gf3 : GraphFragment } → 
        { gf1WfProof : WellFormedness gf1 } →
        { gf2WfProof : WellFormedness gf2 } →
        { gf3WfProof : WellFormedness gf3 } →
        { gfPartitionProof : Partition gf3 gf1 gf2 } →
        Satisfies g (substitute c x t) gf1 →
        Satisfies g (forallT x (terms ts) c) gf2 →
        Satisfies g (forallT x (terms (t ∷ ts)) c) gf3