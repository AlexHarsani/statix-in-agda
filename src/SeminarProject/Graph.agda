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

-- Scope graph term set
record TermSet : Set where
    constructor terms_
    field
        terms : List Term

postulate
    -- relation for min constraint
    Relation : Set
    -- well-formedness property means, that there are
    -- no duplicate values in term set
    WellFormedTermSet : TermSet → Set
    -- least reaching path, as defined in Knowing When to Ask, page 11
    -- this is necessary for min constraint
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
    -- property that the graph fragment is empty
    Empty : GraphFragment → Set
    -- property that the graph fragment is well formed,
    -- which means, that there are no duplicate nodes and edges
    WellFormedness : GraphFragment → Set
    -- property that second and third graph fragment are a valid partition 
    -- of the first graph fragment
    Partition : GraphFragment → GraphFragment → GraphFragment → Set
