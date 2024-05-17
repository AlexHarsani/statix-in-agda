module Statix.ConstraintData (Label : Set) (Scope : Set) where

open import Data.Empty
open import Data.List
open import Data.List.Membership.Propositional
open import Data.Product hiding (<_,_>)
open import Data.Unit
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.Bundles using (TotalPreorder)
open import Relation.Binary
open import Data.Nat.Properties
open import Relation.Binary.Core
open import Relation.Binary.Structures using (IsPreorder ; IsTotalPreorder)

open import ScopeGraph.ScopeGraph Label Scope
open ScopeGraphFragments
open Path

data Constraint {Term : Set} (g : ScopeGraph Term) : Set₁ where
    -- true
    EmpC : Constraint g
    -- false
    FalseC : Constraint g
    -- separating conjunction
    _*C_ : (c1 : Constraint g) → (c2 : Constraint g) → Constraint g
    -- term equality
    EqC : {Term' : Set} → (t1 t2 : Term') → Constraint g
    -- existential quantification
    ExistsC : {Term' : Set} → (f : Term' → Constraint g) → Constraint g
    -- singleton
    SingleC : {Term' : Set} → Term' → (List Term') → Constraint g
    -- forall
    ForallC : {Term' : Set} → (List Term') → (Term' → Constraint g) → Constraint g
    -- node assertion
    NodeC : (s : Scope) → Term → Constraint g
    -- edge assertion
    EdgeC : (e : Edge) → Constraint g
    -- data
    DataC : Scope → Term → Constraint g
    -- query
    QueryC : Scope → (r : Path → Set) → (D : Term → Set) → (List Path → Constraint g) → Constraint g
    -- min
    MinC : (paths paths' : List Path) → {R : Rel Path Agda.Primitive.lzero} → Decidable R → (IsPreorder _≡_ R) → Constraint g

record ValidQuery {Term : Set} (g : ScopeGraph Term) (s : Scope) (r : Path → Set) (D : Term → Set) : Set where
    constructor query-proof
    field
        paths : List Path
        -- all paths are validPath
        valid-paths : ∀ {path} → path ∈ paths → r path → validPath g path
        -- all lead go from s to s' based on D
        resolution-paths : ∀ {path} → path ∈ paths → firstScope path ≡ s → validEnd g D path
        -- no path is missing
        no-path-missing : ⊤

sat-helper : (c1-sat c2-sat : (Σ Set λ s → (s → ScopeGraphFragment))) → (Σ Set λ s → (s → ScopeGraphFragment))
sat-helper c1-sat c2-sat = Σ (proj₁ c1-sat × proj₁ c2-sat) 
    ((λ (c1-proof , c2-proof) → DisjointGraphFragments (proj₂ c1-sat c1-proof) (proj₂ c2-sat c2-proof))) , 
    λ ((c1-proof , c2-proof) , disjoint) → mergeFragments (proj₂ c1-sat c1-proof) (proj₂ c2-sat c2-proof)

sat : {Term : Set} (g : ScopeGraph Term) → Constraint g → (Σ Set λ s → (s → ScopeGraphFragment))
sat g EmpC = ⊤ , λ s → empGf
sat g FalseC = ⊥ , λ s → empGf
sat g (c1 *C c2) = sat-helper (sat g c1) (sat g c2)
sat g (EqC t1 t2) = (t1 ≡ t2) , λ s → empGf
sat g (ExistsC {Term} cf) = (Σ Term λ t → proj₁ (sat g (cf t))) , λ (t , c-proof) → proj₂ (sat g (cf t)) c-proof
sat g (SingleC t ts) = ((t ∷ []) ≡ ts) , λ single-proof → empGf
sat g (ForallC [] cf) = sat g EmpC
sat g (ForallC (t ∷ ts) cf) = sat-helper (sat g (cf t)) (sat g (ForallC ts cf))
sat g (NodeC s t) = (decl (g s) ≡ t) , λ node-proof → < s ∷ [] , [] >
sat g (EdgeC e@(s₁ , l , s₂)) = ((l , s₂) ∈ edges (g s₁)) , λ edge-proof → < [] , e ∷ [] >
sat g (DataC s t) = (decl (g s) ≡ t) , λ data-proof → < [] , [] >
sat g (QueryC s r D cf) = (Σ (ValidQuery g s r D) (λ s → proj₁ (sat g (cf (ValidQuery.paths s))))) , 
                            λ sat-proof → proj₂ (sat g (cf (ValidQuery.paths (proj₁ sat-proof)))) (proj₂ sat-proof)
sat g (MinC paths paths' R? isPreorder) = (minPaths R? paths paths ≡ paths')  , λ _ → empGf
