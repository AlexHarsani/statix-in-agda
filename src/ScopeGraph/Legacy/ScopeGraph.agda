module ScopeGraph.Legacy.ScopeGraph (Label : Set) where

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
record Scope T1 T2 : Set where
    constructor _↦_
    field
        name : T1
        term : T2

-- edge
record Edge T1 T2 : Set where
    constructor edge
    field
        fromScope : Scope T1 T2
        label : Label
        toScope : Scope T1 T2

-- scope graph
record ScopeGraph T1 T2 : Set where
    constructor G<_,_>
    field
        scopes : List (Scope T1 T2)
        edges : List (Edge T1 T2)

-- scope graph fragment
record ScopeGraphFragment T1 T2 : Set where
    constructor <_,_>
    field
        nodes : List (Scope T1 T2)
        edges : List (Edge T1 T2)

-- temporary implementation for disjoint union
_⊔_ : {T1 T2 : Set} → ScopeGraphFragment T1 T2 → ScopeGraphFragment T1 T2 → ScopeGraphFragment T1 T2
< nodes1 , edges1 > ⊔ < nodes2 , edges2 > = < nodes1 ++ nodes2 , edges1 ++ edges2 >

module Path 
    (pathEmptyToTerm : {T T1 T2 : Set} → Scope T1 T2 -> T) 
    (pathStepToTerm : {T T1 T2 : Set} → Scope T1 T2 -> Label -> T -> T) 
    {G : {T1 T2 : Set} → ScopeGraph T1 T2} where

    -- reachability
    data _⟶_ T1 T2 : Scope T1 T2 → Scope T1 T2 → Set where
        [] : {s : Scope T1 T2} → _⟶_ T1 T2 s s
        _∷_ : {s1 s2 s3 : Scope T1 T2} → { l : Label } → (edge s1 l s2) ∈ ScopeGraph.edges (G {T1} {T2}) → _⟶_ T1 T2 s2 s3 → _⟶_ T1 T2 s1 s3

    -- resolution path
    data _↦[_]*_ {T1 T2 : Set} (s1 : Scope T1 T2) (allowedWord : {s2 : Scope T1 T2} → _⟶_ T1 T2 s1 s2 → Set) (D : T2 → Set) : Set where 
        path : {s2 : Scope T1 T2} → (p : _⟶_ T1 T2 s1 s2) → (allowedWord p) → D (Scope.term s2) → (s1 ↦[ allowedWord ]* D) 

    pathToTerm : {T T1 T2 : Set} → { s1 s2 : Scope T1 T2 } → _⟶_ T1 T2 s1 s2 → T
    pathToTerm ([] {s}) = pathEmptyToTerm s 
    pathToTerm ((_∷_) {s1} {s2} {s3} {l} _ p) = pathStepToTerm s1 l (pathToTerm p)

    resolutionPathToTerm : {T T1 T2 : Set} { s : Scope T1 T2 } {allowedWord : {s2 : Scope T1 T2} → _⟶_ T1 T2 s s2 → Set} {D : T2 → Set} → s ↦[ allowedWord ]* D → T
    resolutionPathToTerm (path p aw dp) = pathToTerm p
    
    noPathMissing : {T T1 T2 : Set} {s : Scope T1 T2} {D : T2 → Set} {aw : {s2 : Scope T1 T2} → _⟶_ T1 T2 s s2 → Set} → List (s ↦[ aw ]* D) → ScopeGraph T1 T2 → Set
    noPathMissing ps G = ⊤
