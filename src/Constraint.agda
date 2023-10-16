module Constraint (L : Set) where

open import Data.List
open import Data.Product

open import Graph

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
    _=t=_ : (Term L) → (Term L) → Constraint
    -- existential quantification
    existsC_inC_ : (Term L) → Constraint → Constraint
    -- set singletons
    single : (Term L) → (TermSet L) → Constraint
    -- minimum
    min : (Term L) → Relation → (Term L) → Constraint
    -- forall
    forallC_inC_ : (Term L) → (Term L) → Constraint → Constraint

data Satisfies : (Graph L) → Constraint → (Σ (GraphFragment L) (WellFormedness L)) → Set₁ where
    satisfiesEmpty : {g : Graph L} → 
        { wfProof : WellFormedness L (record { nodes = [] ; edges = [] }) } → 
        Satisfies g emp (record { nodes = [] ; edges = [] } , wfProof)
    satisfiesCompound : {g : Graph L} → 
        { c1 c2 : Constraint } → 
        { gf1 gf2 gf3 : GraphFragment L } → 
        { gf1WfProof : WellFormedness L gf1 } →
        { gf2WfProof : WellFormedness L gf2 } →
        { gf3WfProof : WellFormedness L gf3 } →
        { partition : Partition L gf1 gf2 gf3 } → 
        Satisfies g c1 ((gf2 , gf2WfProof)) →
        Satisfies g c2 ((gf3 , gf3WfProof)) →
        Satisfies g (c1 * c2) (gf1 , gf1WfProof)
    satisfiesTermEq : {g : Graph L} → 
        { wfProof : WellFormedness L (record { nodes = [] ; edges = [] }) } →
        { t1 t2 : Term L } →
        { termEq : TermEq L t1 t2 } →
        Satisfies g (t1 =t= t2) (( (record { nodes = [] ; edges = [] }) , wfProof ))
        