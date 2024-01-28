module ScopeGraph (Label : Set) {Term : Set} where

open import Data.Fin
open import Data.List
open import Data.List.Membership.Propositional
open import Data.Nat hiding (_⊔_)
open import Data.Product hiding (map ; <_,_>)
open import Data.String hiding (_++_)
open import Data.Unit
open import Relation.Nullary
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
    constructor G<_,_>
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
    (pathEmptyToTerm : Scope -> Term) 
    (pathStepToTerm : Scope -> Label -> Term -> Term) 
    {G : ScopeGraph} where

    -- reachability
    data _⟶_ : Scope → Scope → Set where
        [] : ∀ {s} → s ⟶ s
        _∷_ : ∀ {s1 s2 s3} → { l : Label } → (edge s1 l s2) ∈ ScopeGraph.edges G → s2 ⟶ s3 → s1 ⟶ s3 

    -- resolution path
    data _↦[_]*_ (s1 : Scope) (allowedWord : {s2 : Scope} → s1 ⟶ s2 → Set) (D : Term → Set) : Set where 
        path : ∀ {s2} → (p : s1 ⟶ s2) → (allowedWord p) → D (Scope.term s2) → (s1 ↦[ allowedWord ]* D) 

    pathToTerm : { s1 s2 : Scope } → s1 ⟶ s2 → Term
    pathToTerm ([] {s}) = pathEmptyToTerm s 
    pathToTerm ((_∷_) {s1} {s2} {s3} {l} _ p) = pathStepToTerm s1 l (pathToTerm p)

    resolutionPathToTerm : { s : Scope } {allowedWord : {s2 : Scope} → s ⟶ s2 → Set} {D : Term → Set} → s ↦[ allowedWord ]* D → Term
    resolutionPathToTerm (path p aw dp) = pathToTerm p
    
    noPathMissing : {s : Scope} {D : Term → Set} {aw : {s2 : Scope} → s ⟶ s2 → Set} → List (s ↦[ aw ]* D) → ScopeGraph → Set
    noPathMissing ps G = ⊤
