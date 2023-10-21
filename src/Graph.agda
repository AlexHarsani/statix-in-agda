module Graph (L : Set) where

open import Data.String
open import Data.List

-- Scope graph node
record Node : Set where
    field
        name : String

-- Scope graph edge
record Edge : Set where
    field
        from : Node
        label : L
        to : Node

-- Scope graph term
data Term : Set where
    var : String → Term
    compound : String → (List Term) → Term
    label : L → Term
    node : Node → Term

postulate
    -- proof that terms are equal
    TermEq : Term → Term → Set

-- Scope graph term set
record TermSet : Set where
    field
        terms : List Term

postulate
    Relation : Set
    EmptyTermSet : TermSet → Set
    SingletonTermSet : Term → TermSet → Set
    WellFormedTermSet : TermSet → Set
    PartitionedTermSet : TermSet → Term → TermSet → Set
    minTermSet : TermSet → Relation → TermSet

-- Scope graph
record Graph : Set where
    field
        nodes : List Node
        edges : L → List Edge
        mapG : (Node → Term)

-- Scope graph fragment
record GraphFragment : Set where
    constructor <_,_>
    field
        nodes : List Node
        edges : List Edge

postulate
    -- proof that graph fragment is empty
    Empty : GraphFragment → Set
    -- proof that graph fragment is well formed
    WellFormedness : GraphFragment → Set
    -- proof that second and third graph fragment are partition of the first graph fragment
    Partition : GraphFragment → GraphFragment → GraphFragment → Set
