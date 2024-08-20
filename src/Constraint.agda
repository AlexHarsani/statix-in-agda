module Constraint (Label : Set) where

open import Data.Empty
open import Data.Fin
open import Data.List
open import Data.List.Membership.Propositional
open import Data.List.Relation.Binary.Permutation.Propositional
open import Data.Nat
open import Data.Product hiding (<_,_>)
open import Data.Unit
open import Relation.Binary
open import Relation.Binary.PropositionalEquality

open import ScopeGraph Label
open Path
open ScopeGraphFragments

data Constraint {numberOfScopes : ℕ} {Term : Set} (g : ScopeGraph numberOfScopes Term) : Set₁ where
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
    NodeC : (s : (Fin numberOfScopes)) → Term → Constraint g
    -- edge assertion
    EdgeC : (e : Edge g) → Constraint g
    -- data
    DataC : (Fin numberOfScopes) → Term → Constraint g
    -- query
    QueryC : (s : Fin numberOfScopes) → (r : (Path g) → Set) → (D : Term → Set) → (cf : List (Path g) → Constraint g) → Constraint g
    -- min
    MinC : (paths paths' : List (Path g)) → {R : Rel (Path g) Agda.Primitive.lzero} → Decidable R → (IsPreorder _≡_ R) → Constraint g

validC : {numberOfScopes : ℕ} {Term : Set} (g : ScopeGraph numberOfScopes Term) → Constraint g
validC g = EmpC *C EmpC

record ValidQuery {numberOfScopes : ℕ} {Term : Set} (g : ScopeGraph numberOfScopes Term) 
  (s : Fin numberOfScopes) (r : (Path g) → Set) (D : Term → Set) : Set where
    constructor query-proof
    field
        paths : List (Path g)
        well-formed : ∀ {path} → path ∈ paths → validPath g path
        non-cyclic : ∀ {path} → path ∈ paths → noCycle path
        allowed : ∀ {path} → path ∈ paths → r path
        valid-start : ∀ {path} → path ∈ paths → firstScope path ≡ s
        valid-end : ∀ {path} → path ∈ paths → validEnd g D path
        no-path-missing : ∀ {path} → noCycle path → 
            r path → validPath g path → 
            firstScope path ≡ s → validEnd g D path → 
            path ∈ paths

sat-helper : {numberOfScopes : ℕ} {Term : Set} {g : ScopeGraph numberOfScopes Term} 
    (c1-sat c2-sat : (Σ Set λ s → (s → ScopeGraphFragment g))) → (Σ Set λ s → (s → ScopeGraphFragment g))
sat-helper c1-sat c2-sat = Σ (proj₁ c1-sat × proj₁ c2-sat) 
    ((λ (c1-proof , c2-proof) → DisjointGraphFragments (proj₂ c1-sat c1-proof) (proj₂ c2-sat c2-proof))) , 
    λ ((c1-proof , c2-proof) , disjoint) → mergeFragments (proj₂ c1-sat c1-proof) (proj₂ c2-sat c2-proof)

satisfies = proj₁
fragment = proj₂

sat : {numberOfScopes : ℕ} {Term : Set} (g : ScopeGraph numberOfScopes Term) → 
        Constraint g → (Σ Set λ s → (s → ScopeGraphFragment g))
sat g EmpC = ⊤ , λ s → empGf
sat g FalseC = ⊥ , λ s → empGf
sat g (c1 *C c2) = sat-helper (sat g c1) (sat g c2)
sat g (EqC t1 t2) = (t1 ≡ t2) , λ s → empGf
sat g (ExistsC {Term} cf) = (Σ Term λ t → proj₁ (sat g (cf t))) , λ (t , c-proof) → proj₂ (sat g (cf t)) c-proof
sat g (SingleC t ts) = ((t ∷ []) ≡ ts) , λ single-proof → empGf
sat g (ForallC [] cf) = sat g EmpC
sat g (ForallC (t ∷ ts) cf) = sat-helper (sat g (cf t)) (sat g (ForallC ts cf))
sat g (NodeC s t) = (decl (g s) ≡ t) , λ _ → < s ∷ [] , [] >
sat g (EdgeC e@(s₁ , l , s₂)) = ((l , s₂) ∈ edges (g s₁)) , 
    λ _ → < [] , e ∷ [] >
sat g (DataC s t) = (decl (g s) ≡ t) , λ _ → < [] , [] >
sat g (QueryC s r D cf) = (Σ (ValidQuery g s r D) (λ s → proj₁ (sat g (cf (ValidQuery.paths s))))) , 
                            λ sat-proof → proj₂ (sat g (cf (ValidQuery.paths (proj₁ sat-proof)))) (proj₂ sat-proof)
sat g (MinC paths paths' R? isPreorder) = (minPaths R? paths paths ≡ paths')  , λ _ → empGf

validTopLevelGraphFragment : {numberOfScopes : ℕ} {Term : Set} {g : ScopeGraph numberOfScopes Term} → 
    (c : Constraint g) → (c-proof : proj₁ (sat g c)) → Set
validTopLevelGraphFragment {_} {_} {g} c c-proof =  
    (ScopeGraphFragment.fragmentNodes (proj₂ (sat g c) c-proof) ↭ 
        (ScopeGraphFragment.fragmentNodes (functionToFragment g))) × 
    (ScopeGraphFragment.fragmentEdges (proj₂ (sat g c) c-proof) ↭ 
        ScopeGraphFragment.fragmentEdges (functionToFragment g))

