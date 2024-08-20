module ScopeGraph (Label : Set) where

open import Data.Fin
open import Data.List
open import Data.List.Membership.Propositional
open import Data.Nat
open import Data.Product hiding (<_,_> ; map)
open import Data.Unit
open import Data.Bool.Base as Bool
  using (Bool ; true ; false ; if_then_else_)
open import Relation.Binary
open import Relation.Nullary

ScopeData : ℕ → Set → Set
ScopeData numberOfScopes Term = (List (Label × (Fin numberOfScopes))) × Term

ScopeGraph : ℕ → Set → Set
ScopeGraph numberOfScopes Term = (Fin numberOfScopes) → ScopeData numberOfScopes Term


edges = proj₁ 
decl = proj₂

module ScopeGraphFragments where

    Edge : {numberOfScopes : ℕ} {Term : Set} → ScopeGraph numberOfScopes Term → Set
    Edge {numberOfScopes} g = ((Fin numberOfScopes) × Label × (Fin numberOfScopes))

    record ScopeGraphFragment {numberOfScopes : ℕ} {Term : Set} 
      (g : ScopeGraph numberOfScopes Term) : Set where
        constructor <_,_>
        field
            fragmentNodes : List (Fin numberOfScopes)
            fragmentEdges : List (Edge g)

    empGf : {numberOfScopes : ℕ} {Term : Set} {g : ScopeGraph numberOfScopes Term} → ScopeGraphFragment g
    empGf = < [] , [] >

    data DisjointGraphFragments {numberOfScopes : ℕ} {Term : Set} {g : ScopeGraph numberOfScopes Term} 
      : ScopeGraphFragment g → ScopeGraphFragment g → Set where
        disjointEmpty : ∀ {gf2} {edges} → DisjointGraphFragments < [] , edges > gf2
        disjointNonEmpty : ∀ {gf2} {nodes : List (Fin numberOfScopes)} {edges : List (Edge g)} 
            {scope : Fin numberOfScopes} → 
            (scope ∉ (ScopeGraphFragment.fragmentNodes gf2)) →
            DisjointGraphFragments < nodes , edges > gf2 → 
            DisjointGraphFragments < scope ∷ nodes , edges > gf2

    mergeFragments : {numberOfScopes : ℕ} {Term : Set} {g : ScopeGraph numberOfScopes Term} 
      (gf1 gf2 : ScopeGraphFragment g) → ScopeGraphFragment g
    mergeFragments < fragmentNodes1 , fragmentEdges1 > < fragmentNodes2 , fragmentEdges2 > = 
        < fragmentNodes1 ++ fragmentNodes2 , fragmentEdges1 ++ fragmentEdges2 >

    getOutgoingEdges : {numberOfScopes : ℕ} {Term : Set} (g : ScopeGraph numberOfScopes Term) → Fin numberOfScopes → List (Edge g)
    getOutgoingEdges g source = map (λ { (label , target) → source , label , target }) (proj₁ (g source))
 
    functionToFragment : {numberOfScopes : ℕ} {Term : Set} (g : ScopeGraph numberOfScopes Term) → ScopeGraphFragment g
    functionToFragment {n} g = < allFin n , concat (map (getOutgoingEdges g) (allFin n))  >

    data SubFragment {numberOfScopes : ℕ} {Term : Set} {g : ScopeGraph numberOfScopes Term} 
      : ScopeGraphFragment g → ScopeGraphFragment g → Set where
        subFragmentEmp : ∀ {fragment-larger} {edges} → SubFragment < [] , edges > fragment-larger
        subFragment : ∀ {nodes} {edges} {fragment-larger} {s} → s ∈ ScopeGraphFragment.fragmentNodes fragment-larger → 
          SubFragment < nodes , edges > fragment-larger → SubFragment < s ∷ nodes , edges > fragment-larger


module Path where

    open import Relation.Binary.Core

    data Path {numberOfScopes : ℕ} {Term : Set} (g : ScopeGraph numberOfScopes Term) : Set where
        last' : (Fin numberOfScopes) → Path g
        _::'_ : ((Fin numberOfScopes) × Label) → Path g → Path g

    pathLength : {numberOfScopes : ℕ} {Term : Set} {g : ScopeGraph numberOfScopes Term} → Path g → ℕ
    pathLength (last' x) = zero
    pathLength (x ::' p) = suc (pathLength p)

    validPath : {numberOfScopes : ℕ} {Term : Set} → (g : ScopeGraph numberOfScopes Term) → Path g → Set
    validPath G (last' x) = ⊤
    validPath G ((s1 , l) ::' (last' s2)) = ((l , s2) ∈ edges (G s1))
    validPath G ((s1 , l1) ::' ((s2 , l2) ::' p)) = (l1 , s2) ∈ edges (G s1) × (validPath G ((s2 , l2) ::' p))

    firstScope : {numberOfScopes : ℕ} {Term : Set} {g : ScopeGraph numberOfScopes Term} → Path g → (Fin numberOfScopes)
    firstScope (last' x) = x
    firstScope (x ::' p) = proj₁ x

    validEnd : {numberOfScopes : ℕ} {Term : Set} → (g : ScopeGraph numberOfScopes Term) → (Term → Set) → Path g → Set
    validEnd g D (last' x) = D (decl (g x))
    validEnd g D (x ::' p) = validEnd g D p

    noCycle' : {numberOfScopes : ℕ} {Term : Set} {g : ScopeGraph numberOfScopes Term} → Path g → List (Fin numberOfScopes) → Set
    noCycle' (last' x) visited = x ∉ visited
    noCycle' (x ::' path) visited = (proj₁ x ∉ visited) × noCycle' path (proj₁ x ∷ visited)

    noCycle : {numberOfScopes : ℕ} {Term : Set} {g : ScopeGraph numberOfScopes Term} → Path g → Set
    noCycle path = noCycle' path []

    isMin : {numberOfScopes : ℕ} {Term : Set} {g : ScopeGraph numberOfScopes Term} {R : (Rel (Path g) Agda.Primitive.lzero)} → 
      Decidable R → (A : List (Path g)) → Path g → Bool
    isMin R? [] p = true
    isMin R? (q ∷ A) p = if does (R? q p) 
        then if does (R? p q) then isMin R? A p else false 
        else isMin R? A p

    minPaths : {numberOfScopes : ℕ} {Term : Set} {g : ScopeGraph numberOfScopes Term} {R : (Rel (Path g) Agda.Primitive.lzero)} → 
      Decidable R → (A A' : List (Path g)) → List (Path g)
    minPaths R? [] A' = []
    minPaths R? (p ∷ A) A' = if isMin R? A' p then p ∷ minPaths R? A A' else minPaths R? A A'