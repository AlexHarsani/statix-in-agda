module Constraint (L : Set) where

open import Data.List
open import Data.String
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

open import Graph L

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
    existsC : String → Constraint → Constraint
    -- set singletons
    single : Term → TermSet → Constraint
    -- minimum
    min : TermSet → Relation → TermSet → Constraint
    -- forall
    forallC : String → TermSet → Constraint → Constraint

-- termination checker fails on compound term, 
-- therefore the TERMINATING pragma
{-# TERMINATING #-}
replaceTerm : Term → String → Term → Term
replaceTerm newTerm x oldTerm@(var y) with (x ≟ y)
... | yes _ = newTerm
... | no _ = oldTerm
replaceTerm newTerm x (compound f ts) = compound f (map (replaceTerm newTerm x) ts)
replaceTerm newTerm x oldTerm = oldTerm

substitute : Constraint → String → Term → Constraint
substitute emp x t = emp
substitute false x t = false
substitute (c1 * c2) x t = substitute c1 x t * substitute c2 x t
substitute (t1 =t= t2) x t = (replaceTerm t x t1) =t= (replaceTerm t x t2)
substitute (existsC y c) x t = existsC y (substitute c x t)
substitute (single t1 (terms ts)) x t2 = single (replaceTerm t2 x t1) (terms (map (replaceTerm t2 x) ts))
substitute (min (terms ts1) R (terms ts2)) x t = min ((terms (map (replaceTerm t x) ts1))) R (((terms (map (replaceTerm t x) ts2))))
substitute (forallC y (terms ts) c) x t = forallC y ((terms (map ((replaceTerm t x)) ts))) c

data Satisfies : Graph → Constraint → GraphFragment → Set where
    satisfiesEmpty : { g : Graph } → 
        { gf : GraphFragment } →
        { gfEmptyProof : Empty gf } →
        { gfWfProof : WellFormedness gf } → 
        Satisfies g emp gf
    satisfiesCompound : { g : Graph } → 
        { c1 c2 : Constraint } → 
        { gf1 gf2 gf3 : GraphFragment } → 
        { gf1WfProof : WellFormedness gf1 } →
        { gf2WfProof : WellFormedness gf2 } →
        { gf3WfProof : WellFormedness gf3 } →
        { gfPartitionProof : Partition gf1 gf2 gf3 } → 
        Satisfies g c1 gf2 →
        Satisfies g c2 gf3 →
        Satisfies g (c1 * c2) gf1
    satisfiesTermEq : {g : Graph } → 
        { gf : GraphFragment } →
        { gfEmptyProof : Empty gf } →
        { gfWfProof : WellFormedness gf } →
        { t1 t2 : Term } →
        { termEq : t1 ≡ t2 } →
        Satisfies g (t1 =t= t2) gf
    satisfiesExists : { g : Graph } → 
        { c : Constraint } → 
        { x : String } → 
        { gf : GraphFragment } →
        { gfWfProof : WellFormedness gf }
        { t : Term } →
        Satisfies g (substitute c x t) gf →
        Satisfies g (existsC x c) gf
    satisfiesSingle : { g : Graph } →
        { t : Term } →
        { ts : TermSet } →
        { tsSingletonProof : ts ≡ (terms (t ∷ [])) } →
        { tsWfProof : WellFormedTermSet ts } →
        { gf : GraphFragment } →
        { gfEmptyProof : Empty gf } →
        { gfWfProof : WellFormedness gf } →
        Satisfies g (single t ts) gf
    satisfiesMin : { g : Graph } → 
        { t t' : TermSet } →
        { R : Relation } →
        { gf : GraphFragment } →
        { gfEmptyProof : Empty gf } →
        { gfWfProof : WellFormedness gf } → 
        { termSetEq : t' ≡ minTermSet t R } →
        Satisfies g (min t R t') gf
    satisfiesForallEmpty : { g : Graph } → 
        { x : String } →
        { ts : TermSet } →
        { tsEmptyProof : ts ≡ (terms []) } →
        { c : Constraint } →
        { gf : GraphFragment } →
        { gfEmptyProof : Empty gf } →
        { gfWfProof : WellFormedness gf } → 
        Satisfies g (forallC x ts c) gf
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
        { gfPartitionProof : Partition gf1 gf2 gf3 } →
        Satisfies g (substitute c x t) gf2 →
        Satisfies g (forallC x (terms ts) c) gf3 →
        Satisfies g (forallC x (terms (t ∷ ts)) c) gf1