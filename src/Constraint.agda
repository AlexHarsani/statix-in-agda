module Constraint (Label : Set) {Term : Set} where

open import Data.Empty
open import Data.List
open import Data.Product hiding (<_,_>)
open import Data.Unit
open import Relation.Binary.PropositionalEquality

open import Graph Label {Term}

Constraint = GraphFragment → Set

-- true
Emp : Constraint
Emp gf = gf ≡ < [] , [] >

-- false
False : Constraint
False gf = ⊥

-- separating conjunction
record _*_ (c1 c2 : Constraint) (gf : GraphFragment) : Set where
    constructor _⟨_⟩_
    field
        { gf1 gf2 } : GraphFragment
        c1-sat : c1 gf1
        gf-partition : gf1 ⊔ gf2 ≡ gf
        c2-sat : c2 gf2

-- term equality
Eq : Term → Term → Constraint
Eq t1 t2 gf = (Emp gf) × (t1 ≡ t2)

-- existential quantification
ExistsC : (Term → Constraint) → Constraint
ExistsC cf gf = Σ Term λ t → cf t gf

-- set singletons
Single : Term → (List Term) → Constraint
Single t ts gf = (Emp gf) × ((t ∷ []) ≡ ts)

-- forall
ForallC : (List Term) → (Term → Constraint) → Constraint
ForallC [] cf gf = Emp gf
ForallC (t ∷ ts) cf = (cf t) * (ForallC ts cf)

-- Example proofs

sat-emp : Emp < [] , [] >
sat-emp = refl

sat-conj : (Emp * Emp) < [] , [] >
sat-conj = refl ⟨ refl ⟩ refl

sat-eq : { t : Term } → Eq t t < [] , [] >
sat-eq = refl , refl

sat-exists : ( t : Term ) → ExistsC (λ y → Eq t y) < [] , [] >
sat-exists t = t , refl , refl

sat-single : { t : Term } → Single t (t ∷ []) < [] , [] >
sat-single = refl , refl

sat-forall : { t : Term } → ForallC (t ∷ []) (λ y → Eq t y) < [] , [] >
sat-forall = (refl , refl) ⟨ refl ⟩ refl