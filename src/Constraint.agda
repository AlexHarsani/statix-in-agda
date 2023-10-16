module Constraint (L : Set) where

open import Data.List
open import Data.Product

open import Graph L

postulate
    Relation : Set

data Constraint : Set₁ where
    -- true
    emp : Constraint
    -- false
    false : Constraint
    -- separating conjunction
    _*_ : Constraint → Constraint → Constraint
    -- term equality
    _=t=_ : Term → Term → Constraint
    -- existential quantification
    existsC_inC_ : Term → Constraint → Constraint
    -- set singletons
    single : Term → TermSet → Constraint
    -- minimum
    min : Term → Relation → Term → Constraint
    -- forall
    forallC_inC_ : Term → Term → Constraint → Constraint

data Satisfies : Graph → Constraint → (Σ GraphFragment WellFormedness) → Set₁ where
    satisfiesEmpty : { g : Graph } → 
        { wfProof : WellFormedness (record { nodes = [] ; edges = [] }) } → 
        Satisfies g emp (record { nodes = [] ; edges = [] } , wfProof)
    satisfiesCompound : { g : Graph } → 
        { c1 c2 : Constraint } → 
        { gf1 gf2 gf3 : GraphFragment } → 
        { gf1WfProof : WellFormedness gf1 } →
        { gf2WfProof : WellFormedness gf2 } →
        { gf3WfProof : WellFormedness gf3 } →
        { partition : Partition gf1 gf2 gf3 } → 
        Satisfies g c1 ((gf2 , gf2WfProof)) →
        Satisfies g c2 ((gf3 , gf3WfProof)) →
        Satisfies g (c1 * c2) (gf1 , gf1WfProof)
    satisfiesTermEq : {g : Graph } → 
        { wfProof : WellFormedness (record { nodes = [] ; edges = [] }) } →
        { t1 t2 : Term } →
        { termEq : TermEq t1 t2 } →
        Satisfies g (t1 =t= t2) (( (record { nodes = [] ; edges = [] }) , wfProof ))
        