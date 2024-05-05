module Test.ConstraintFunctionExperiments where

open import Data.List
open import Data.Nat hiding (_*_)
open import Data.Empty
open import Data.Fin hiding (_+_)
open import Data.Product hiding (<_,_>)
open import Data.List.Membership.Propositional
open import Data.List.Relation.Unary.Any hiding (map)
open import Data.Unit
open import Data.List.Relation.Binary.Disjoint.Setoid
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary using (¬_; yes; no)

postulate
    Label : Set

open import Statix.ConstraintFunction Label (Fin 2)
open import ScopeGraph.ScopeGraph Label (Fin 2)
open ScopeGraphFragments

postulate
    Term : Set
    graph : ScopeGraph Term
    t1 t2 t' : Term
    l : Label


emp-proof : proj₁ (Emp graph)
emp-proof = tt

eq-proof : proj₁ (Eq t1 t1 graph)
eq-proof = refl

exists-proof : proj₁ (ExistsC (λ t → Eq t t1) graph)
exists-proof = t1 , refl

conj-proof : proj₁ ((Emp * Emp) graph)
conj-proof = (tt , tt) , disjointEmpty

conj-gf-proof : proj₂ (((Emp * Emp) graph)) conj-proof ≡ empGf
conj-gf-proof = refl

edges-list : List Edge
edges-list = (zero , l , suc zero) ∷ (suc zero , l , zero) ∷ []

graph2 : ScopeGraph Term
graph2 zero = (l , suc zero) ∷ [] , t'
graph2 (suc zero) = (l , zero) ∷ [] , t'

forall-proof : proj₁ (ForallC edges-list (λ e → EdgeC e) graph2)
forall-proof = (here refl , (here refl , tt) , disjointEmpty) , disjointEmpty

forall-fragment : proj₂ (ForallC edges-list (λ e → EdgeC e) graph2) forall-proof ≡ < [] , edges-list >
forall-fragment = refl

scope-list : List (Fin 2)
scope-list = zero ∷ (suc zero) ∷ []

scope-list' : List (Fin 2)
scope-list' = (suc zero) ∷ []

forall-proof2 : proj₁ (ForallC scope-list (λ s → NodeC s t') graph2)
forall-proof2 = (refl , (refl , tt) , disjointEmpty) , disjointNonEmpty (λ { (here ()) ; (there ())}) disjointEmpty

forall-fragment2 : proj₂ (ForallC scope-list (λ s → NodeC s t') graph2) forall-proof2 ≡ < scope-list , [] >
forall-fragment2 = refl