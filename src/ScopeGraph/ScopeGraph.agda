module ScopeGraph.ScopeGraph (Label : Set) where

open import Data.List
open import Data.Nat
open import Data.Fin
open import Data.Product hiding (<_,_> ; map)
open import Data.List.Membership.Propositional
open import Data.Unit
open import Relation.Nullary
open import Relation.Binary
open import Data.List.Relation.Unary.All hiding (map)
open import Data.Bool.Base as Bool
  using (Bool ; true ; false ; if_then_else_)

ScopeData : Set → Set → Set
ScopeData Scope Term = (List (Label × Scope)) × Term

edges = proj₁ 
decl = proj₂

ScopeGraph : Set → Set → Set
ScopeGraph Scope Term = Scope → ScopeData Scope Term


module ScopeGraphFragments where

    Edge : {Scope Term : Set} → ScopeGraph Scope Term → Set
    Edge {Scope} g = (Scope × Label × Scope)

    record ScopeGraphFragment {Scope Term : Set} (g : ScopeGraph Scope Term) : Set where
        constructor <_,_>
        field
            fragmentNodes : List Scope
            fragmentEdges : List (Edge g)

    empGf : {Scope Term : Set} {g : ScopeGraph Scope Term} → ScopeGraphFragment g
    empGf = < [] , [] >

    data DisjointGraphFragments {Scope Term : Set} {g : ScopeGraph Scope Term} 
      (gf1 : ScopeGraphFragment g) : ScopeGraphFragment g → Set where
        disjointEmpty : ∀ {edges} → DisjointGraphFragments gf1 < [] , edges >
        disjointNonEmpty : {nodes : List Scope} {edges : List (Edge g)} {scope : Scope} → 
            (scope ∉ (ScopeGraphFragment.fragmentNodes gf1)) →
            DisjointGraphFragments gf1 < nodes , edges > → 
            DisjointGraphFragments gf1 < scope ∷ nodes , edges >

    mergeFragments : {Scope Term : Set} {g : ScopeGraph Scope Term} 
      (gf1 gf2 : ScopeGraphFragment g) → ScopeGraphFragment g
    mergeFragments < fragmentNodes1 , fragmentEdges1 > < fragmentNodes2 , fragmentEdges2 > = 
        < fragmentNodes1 ++ fragmentNodes2 , fragmentEdges1 ++ fragmentEdges2 >

    getOutgoingEdges : {k : ℕ} {Term : Set} (g : ScopeGraph (Fin k) Term) → Fin k → List (Edge g)
    getOutgoingEdges g source = map (λ { (label , target) → source , label , target }) (proj₁ (g source))
 
    functionToFragment : {k : ℕ} {Term : Set} (g : ScopeGraph (Fin k) Term) → ScopeGraphFragment g
    functionToFragment {n} g = < allFin n , concat (map (getOutgoingEdges g) (allFin n))  >


module Path where

    open import Relation.Binary.Core

    data Path {Scope Term : Set} (g : ScopeGraph Scope Term) : Set where
        last' : Scope → Path g
        _::'_ : (Scope × Label) → Path g → Path g

    pathLength : {Scope Term : Set} {g : ScopeGraph Scope Term} → Path g → ℕ
    pathLength (last' x) = zero
    pathLength (x ::' p) = suc (pathLength p)

    validPath : {Scope Term : Set} → (g : ScopeGraph Scope Term) → Path g → Set
    validPath G (last' x) = ⊤
    validPath G ((s1 , l) ::' (last' s2)) = ((l , s2) ∈ edges (G s1))
    validPath G ((s1 , l1) ::' ((s2 , l2) ::' p)) = (l1 , s2) ∈ edges (G s1) × (validPath G ((s2 , l2) ::' p))

    firstScope : {Scope Term : Set} {g : ScopeGraph Scope Term} → Path g → Scope
    firstScope (last' x) = x
    firstScope (x ::' p) = proj₁ x

    validEnd : {Scope Term : Set} → (g : ScopeGraph Scope Term) → (Term → Set) → Path g → Set
    validEnd g D (last' x) = D (decl (g x))
    validEnd g D (x ::' p) = validEnd g D p
    
    isMin : {Scope Term : Set} {g : ScopeGraph Scope Term} {R : (Rel (Path g) Agda.Primitive.lzero)} → 
      Decidable R → (A : List (Path g)) → Path g → Bool
    isMin R? [] p = true
    isMin R? (q ∷ A) p = if does (R? q p) 
        then if does (R? p q) then isMin R? A p else false 
        else isMin R? A p

    minPaths : {Scope Term : Set} {g : ScopeGraph Scope Term} {R : (Rel (Path g) Agda.Primitive.lzero)} → 
      Decidable R → (A A' : List (Path g)) → List (Path g)
    minPaths R? [] A' = []
    minPaths R? (p ∷ A) A' = if isMin R? A' p then p ∷ minPaths R? A A' else minPaths R? A A'