module Constraint (Label : Set) {Term : Set} where

open import Data.Empty
open import Data.List
open import Data.List.Membership.Propositional
open import Data.Product hiding (<_,_>)
open import Data.Unit
open import Relation.Binary.PropositionalEquality

open import ScopeGraph Label {Term}

postulate
    pathEmptyToTerm : Scope -> Term
    pathStepToTerm : Scope -> Label -> Term -> Term
    G : ScopeGraph

open Path G pathEmptyToTerm pathStepToTerm

postulate
    allowedWord : { s1 s2 : Scope} → s1 ⟶ s2 → Set


Constraint = ScopeGraph → ScopeGraphFragment → Set

-- true
Emp : Constraint
Emp G gf = gf ≡ < [] , [] >

-- false
False : Constraint
False G gf = ⊥

-- separating conjunction
record _*_ (c1 c2 : Constraint) (G : ScopeGraph) (gf : ScopeGraphFragment) : Set where
    constructor _⟨_⟩_
    field
        { gf1 gf2 } : ScopeGraphFragment
        c1-sat : c1 G gf1
        gf-partition : gf1 ⊔ gf2 ≡ gf
        c2-sat : c2 G gf2

-- term equality
Eq : Term → Term → Constraint
Eq t1 t2 G gf = (Emp G gf) × (t1 ≡ t2)

-- existential quantification
ExistsC : (Term → Constraint) → Constraint
ExistsC cf G gf = Σ Term λ t → cf t G gf

-- set singletons
Single : Term → (List Term) → Constraint
Single t ts G gf = (Emp G gf) × ((t ∷ []) ≡ ts)

-- forall
ForallC : (List Term) → (Term → Constraint) → Constraint
ForallC [] cf G gf = Emp G gf
ForallC (t ∷ ts) cf = cf t * ForallC ts cf

-- scope graph constraints

-- node assertion
NodeC : Scope → Term → Constraint
NodeC scope@(s ↦ t') t G gf = (gf ≡ < scope ∷ [] , [] >) × (scope ∈ ScopeGraph.scopes G) × (t ≡ t')

-- edge assertion
EdgeC : Scope → Edge → Constraint
EdgeC s e G gf = (gf ≡ < [] , e ∷ [] >) × (e ∈ ScopeGraph.edges G)

-- query
Query : { s : Scope } { t : Term } → s ↦[ allowedWord ]* t → (Term → Constraint) → Constraint
Query (path p aw eq) cf G gf = cf (answer p) G gf

-- data
DataOf : Scope → Term → Constraint
DataOf (s ↦ t') t G gf = Emp G gf × t ≡ t'


-- Example proofs

sat-emp : {G : ScopeGraph} → Emp G < [] , [] >
sat-emp = refl

sat-conj : {G : ScopeGraph} → (Emp * Emp) G < [] , [] >
sat-conj = refl ⟨ refl ⟩ refl

sat-eq : {G : ScopeGraph} → { t : Term } → Eq t t G < [] , [] >
sat-eq = refl , refl

sat-exists : {G : ScopeGraph} → ( t : Term ) → ExistsC (λ y → Eq t y) G < [] , [] >
sat-exists t = t , refl , refl

sat-single : {G : ScopeGraph} → { t : Term } → Single t (t ∷ []) G < [] , [] >
sat-single = refl , refl

sat-forall : {G : ScopeGraph} → { t : Term } → ForallC (t ∷ []) (λ y → Eq t y) G < [] , [] >
sat-forall = (refl , refl) ⟨ refl ⟩ refl