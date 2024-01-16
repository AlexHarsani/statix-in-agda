module ScopeGraph (Label : Set) {Term : Set} where

open import Data.Fin
open import Data.List
open import Data.List.Membership.Propositional
open import Data.Nat hiding (_⊔_)
open import Data.Product hiding (map ; <_,_>)
open import Data.String hiding (_++_)
open import Relation.Binary.PropositionalEquality


-- node/scope
record Scope : Set where
    constructor _↦_
    field
        name : Term
        term : Term

-- edge
record Edge : Set where
    constructor edge
    field
        fromScope : Scope
        label : Label
        toScope : Scope

-- scope graph
record ScopeGraph : Set where
    field
        scopes : List Scope
        edges : List Edge

-- scope graph fragment
record ScopeGraphFragment : Set where
    constructor <_,_>
    field
        nodes : List Scope
        edges : List Edge

-- temporary implementation for disjoint union
_⊔_ : ScopeGraphFragment → ScopeGraphFragment → ScopeGraphFragment
< nodes1 , edges1 > ⊔ < nodes2 , edges2 > = < nodes1 ++ nodes2 , edges1 ++ edges2 >

module Path 
    (G : ScopeGraph)
    (pathEmptyToTerm : Scope -> Term) 
    (pathStepToTerm : Scope -> Label -> Term -> Term) where


    postulate
        neighboursOf : Scope → ScopeGraph → List Scope
        getLabel : Scope → Scope → Label
        emptyTerm : Term

    -- reachability
    data _⟶_ : Scope → Scope → Set where
        [] : ∀ {s} → s ⟶ s
        _∷_ : ∀ {s1 s2 s3} → s2 ∈ neighboursOf s1 G → s2 ⟶ s3 → s1 ⟶ s3 

    -- resolution path
    data _↦[_]*_ (s1 : Scope) (allowedWord : {s2 : Scope} → s1 ⟶ s2 → Set) (t : Term) : Set where 
        path : ∀ {s2} → (p : s1 ⟶ s2) → (allowedWord p) → t ≡ Scope.term s2 → (s1 ↦[ allowedWord ]* t) 

    
    answer : { s1 s2 : Scope } → s1 ⟶ s2 → Term
    answer ([] {s}) = pathEmptyToTerm s 
    answer ((_∷_) {s1} {s2} {s3} _ p) = pathStepToTerm s1 (getLabel s1 s2) (answer p)
