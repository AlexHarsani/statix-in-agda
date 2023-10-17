module Constraint (L : Set) where

open import Data.List
open import Data.Product
open import Data.String
open import Relation.Nullary

open import Graph L

postulate
    Relation : Set

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
    existsC_inC_ : String → Constraint → Constraint
    -- set singletons
    single : Term → TermSet → Constraint
    -- minimum
    min : Term → Relation → Term → Constraint
    -- forall
    forallC_inC_ : Term → Term → Constraint → Constraint

replaceTerm : Term → String → Term → Term
replaceTerm (var y) x t2 with (x ≟ y) 
... | yes _ = t2
... | no _ = (var y)
replaceTerm t1 x t2 = t1

substitute : Constraint → String → Term → Constraint
substitute (c1 * c2) x t = substitute c1 x t * substitute c2 x t
substitute (t1 =t= t2) x t = (replaceTerm t1 x t) =t= (replaceTerm t2 x t)
substitute (existsC y inC c) x t = existsC y inC (substitute c x t)
substitute c t x = c

data Satisfies : Graph → Constraint → GraphFragment → Set where
    satisfiesEmpty : { g : Graph } → 
        { wfProof : WellFormedness (record { nodes = [] ; edges = [] }) } → 
        Satisfies g emp (record { nodes = [] ; edges = [] })
    satisfiesCompound : { g : Graph } → 
        { c1 c2 : Constraint } → 
        { gf1 gf2 gf3 : GraphFragment } → 
        { gf1WfProof : WellFormedness gf1 } →
        { gf2WfProof : WellFormedness gf2 } →
        { gf3WfProof : WellFormedness gf3 } →
        { partition : Partition gf1 gf2 gf3 } → 
        Satisfies g c1 gf2 →
        Satisfies g c2 gf2 →
        Satisfies g (c1 * c2) gf1
    satisfiesTermEq : {g : Graph } → 
        { wfProof : WellFormedness (record { nodes = [] ; edges = [] }) } →
        { t1 t2 : Term } →
        { termEq : TermEq t1 t2 } →
        Satisfies g (t1 =t= t2) (record { nodes = [] ; edges = [] })
    satisfiesExists : { g : Graph } → 
        { c : Constraint } → 
        { x : String } → 
        { gf : GraphFragment } →
        { wfProof : WellFormedness gf }
        { t : Term } →
        Satisfies g (substitute c x t) gf →
        Satisfies g (existsC x inC c) gf
        