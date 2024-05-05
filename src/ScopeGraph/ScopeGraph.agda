module ScopeGraph.ScopeGraph (Label : Set) (Scope : Set) where

open import Data.List
open import Data.Nat
open import Data.Product hiding (<_,_>)
open import Data.List.Membership.Propositional
open import Data.Unit
open import Data.List.Relation.Unary.All
open import Relation.Nullary

ScopeData : Set → Set
ScopeData Term = (List (Label × Scope)) × Term

edges = proj₁ 
decl = proj₂

ScopeGraph : Set → Set
ScopeGraph Term = Scope → ScopeData Term


module ScopeGraphFragments where

    Edge = (Scope × Label × Scope)

    record ScopeGraphFragment : Set where
        constructor <_,_>
        field
            fragmentNodes : List Scope
            fragmentEdges : List Edge

    empGf : ScopeGraphFragment
    empGf = < [] , [] >

    data DisjointGraphFragments (gf1 : ScopeGraphFragment) : ScopeGraphFragment → Set where
        disjointEmpty : ∀ {edges} → DisjointGraphFragments gf1 < [] , edges >
        disjointNonEmpty : {nodes : List Scope} {edges : List Edge} {scope : Scope} → 
            (scope ∉ (ScopeGraphFragment.fragmentNodes gf1)) →
            DisjointGraphFragments gf1 < nodes , edges > → 
            DisjointGraphFragments gf1 < scope ∷ nodes , edges >

    mergeFragments : (gf1 gf2 : ScopeGraphFragment) → ScopeGraphFragment
    mergeFragments < fragmentNodes1 , fragmentEdges1 > < fragmentNodes2 , fragmentEdges2 > = 
        < fragmentNodes1 ++ fragmentNodes2 , fragmentEdges1 ++ fragmentEdges2 >


module Path where

    open import Relation.Binary.Core

    data Path : Set where
        last' : Scope → Path
        _::'_ : (Scope × Label) → Path → Path

    pathLength : Path → ℕ
    pathLength (last' x) = 1
    pathLength (x ::' p) = 1 + pathLength p

    validPath : {Term : Set} → ScopeGraph Term → Path → Set
    validPath G (last' x) = ⊤
    validPath G ((s1 , l) ::' (last' s2)) = ((l , s2) ∈ edges (G s1))
    validPath G ((s1 , l1) ::' ((s2 , l2) ::' p)) = (l1 , s2) ∈ edges (G s1) × (validPath G ((s2 , l2) ::' p))

    firstScope : Path → Scope
    firstScope (last' x) = x
    firstScope (x ::' p) = proj₁ x

    validEnd : {Term : Set} → ScopeGraph Term → (Term → Set) → Path → Set
    validEnd g D (last' x) = D (decl (g x))
    validEnd g D (x ::' p) = validEnd g D p

    min : (A : List Path) → (_≤_ : Rel Path Agda.Primitive.lzero) → Path → Dec Set
    min A R p = yes (p ∈ A → ∀ {q} → q ∈ A → R q p → R p q)

    minPaths : (A : List Path) → (R : (Rel Path Agda.Primitive.lzero)) → List Path
    minPaths A R = filter (min A R) A