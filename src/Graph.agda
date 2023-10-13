module Graph where

open import Data.String
open import Data.List

-- Scope graph node
record Node : Set where
    field
        name : String

-- Scope graph edge
record Edge (L : Set) : Set where
    field
        from : Node
        label : L
        to : Node

-- Scope graph term
data Term (L : Set) : Set where
    var : String → Term L
    compound : String → (List (Term L)) → Term L
    label : L → Term L
    node : Node → Term L

-- Scope graph term set
data TermSet (L : Set) : Set where
    setVar : String → TermSet L
    ∅ : TermSet L
    single : Term L → TermSet L
    _⊔_ : TermSet L → TermSet L → TermSet L

-- Scope graph
record Graph : Set₁ where
    field
        nodes : List Node
        edges : {L : Set} → List (Edge L)
        mapG : {L : Set} → (Node → Term L)