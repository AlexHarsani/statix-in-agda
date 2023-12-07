module Graph (Label : Set) {Term : Set} where

open import Data.List
open import Data.String hiding (_++_)

-- Scope graph node
record Node : Set where
    field
        name : String

-- Scope graph edge
record Edge : Set where
    field
        from : Node
        label : Label
        to : Node

-- Scope graph
record Graph : Set where
    constructor <_,_,_>
    field
        nodes : List Node
        edges : List Edge
        mapG : (Node → Term)

-- Scope graph fragment
record GraphFragment : Set where
    constructor <_,_>
    field
        nodes : List Node
        edges : List Edge

-- Temporary implementation for disjoint union
_⊔_ : GraphFragment → GraphFragment → GraphFragment
< nodes1 , edges1 > ⊔ < nodes2 , edges2 > = < nodes1 ++ nodes2 , edges1 ++ edges2 >
