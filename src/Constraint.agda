module Constraint (Label : Set) {Term : Set} where

open import Data.Empty
open import Data.List
open import Data.List.Membership.Propositional
open import Data.List.Relation.Unary.Any hiding (map)
open import Data.Product hiding (<_,_> ; map)
open import Data.Unit
open import Relation.Binary.PropositionalEquality

open import ScopeGraph Label {Term}

postulate
    pathEmptyToTerm : Scope -> Term
    pathStepToTerm : Scope -> Label -> Term -> Term

open Path pathEmptyToTerm pathStepToTerm


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
EdgeC : Edge → Constraint
EdgeC e G gf = (gf ≡ < [] , e ∷ [] >) × (e ∈ ScopeGraph.edges G)

-- query
record Query (s : Scope) (D : Term → Set) (G : ScopeGraph) (aw : {s2 : Scope} → _⟶_  {G} s s2 → Set) ( cf : List Term → Constraint) (gf : ScopeGraphFragment) : Set where
    constructor ->>
    field
        paths : List (s ↦[ aw ]* D)
        no-path-missing : noPathMissing paths G
        apply-terms : cf (map resolutionPathToTerm paths) G gf

-- data
DataOf : Scope → Term → Constraint
DataOf (s ↦ t') t G gf = Emp G gf × t ≡ t'


-- Example proofs

-- proof emp
sat-emp : {G : ScopeGraph} → Emp G < [] , [] >
sat-emp = refl

-- proof conj
sat-conj : {G : ScopeGraph} → (Emp * Emp) G < [] , [] >
sat-conj = refl ⟨ refl ⟩ refl

-- proof eq
sat-eq : {G : ScopeGraph} → { t : Term } → Eq t t G < [] , [] >
sat-eq = refl , refl

-- proof exists
sat-exists : {G : ScopeGraph} → ( t : Term ) → ExistsC (λ y → Eq t y) G < [] , [] >
sat-exists t = t , refl , refl

-- proof single
sat-single : {G : ScopeGraph} → { t : Term } → Single t (t ∷ []) G < [] , [] >
sat-single = refl , refl

-- proof forall
sat-forall : {G : ScopeGraph} → { t : Term } → ForallC (t ∷ []) (λ y → Eq t y) G < [] , [] >
sat-forall = (refl , refl) ⟨ refl ⟩ refl

postulate
    name1 name2 : Term
    dataTerm1 dataTerm2 : Term
    label : Label
s = name1 ↦ dataTerm1
G1 = G< s ∷ [] , [] >
gf1 = < s ∷ [] , [] >

-- proof node
sat-node : NodeC s dataTerm1 G1 gf1
sat-node = refl , here refl , refl

s1 = name1 ↦ dataTerm1
s2 = name2 ↦ dataTerm2
e = (edge s1 label s2)
G2 = G< s1 ∷ s2 ∷ [] , e ∷ [] >
gf2 = < [] , e ∷ [] >

-- proof edge
sat-edge : EdgeC e G2 gf2
sat-edge = refl , here refl

path3 = pathStepToTerm s1 label (pathEmptyToTerm s2)

-- proof query
sat-query : Query s1 (λ t → t ≡ dataTerm2) G2 (λ p → ⊤) (λ ts → ForallC ts (λ y → Eq path3 y)) < [] , [] >
sat-query = ->> (path (here refl ∷ []) tt refl ∷ []) tt (((refl , refl) ⟨ refl ⟩ refl))
