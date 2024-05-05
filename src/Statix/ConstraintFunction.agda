module Statix.ConstraintFunction (Label : Set) (Scope : Set) where

open import Data.Empty
open import Data.Fin.Base hiding (_+_ ; _-_)
open import Data.Nat.Base hiding (_*_)
open import Data.List
open import Data.List.Membership.Propositional
open import Data.List.Relation.Unary.Any hiding (map)
open import Data.Product hiding (<_,_> ; map)
open import Data.Unit
open import Data.Sum
open import Relation.Binary.PropositionalEquality

open import ScopeGraph.ScopeGraph Label Scope
open ScopeGraphFragments
open Path

Constraint : Set → Set₁
Constraint Term = ScopeGraph Term → (Σ Set λ a → (a → ScopeGraphFragment))

Emp : {Term : Set} → Constraint Term
Emp g = ⊤ , λ _ → empGf

-- false
False : {Term : Set} → Constraint Term
False g = ⊥ , λ _ → empGf

-- separating conjunction
_*_ : {Term : Set} →
       (c1 c2 : Constraint Term) →
       Constraint Term
(c1 * c2) g = Σ (proj₁ (c1 g) × proj₁ (c2 g)) (λ (c1-proof , c2-proof) → 
                    DisjointGraphFragments (proj₂ (c1 g) c1-proof) (proj₂ (c2 g) c2-proof)) , 
                λ ((c1-proof , c2-proof) , disjoint) → mergeFragments (proj₂ (c1 g) c1-proof) (proj₂ (c2 g) c2-proof)
        
-- term equality
Eq : {Term : Set} → Term → Term → Constraint Term
Eq t1 t2 g = (t1 ≡ t2) , λ ts-eq → empGf

-- existential quantification
ExistsC : {Term : Set} → (Term → Constraint Term) → Constraint Term
ExistsC {Term} cf G = 
    (Σ Term λ t → proj₁ ((cf t) G)) , 
    λ (t , c-proof) → proj₂ (cf t G) c-proof

-- singleton
Single : {Term : Set} → Term → (List Term) → Constraint Term
Single t ts G = ((t ∷ []) ≡ ts) , λ single-proof → empGf
    
-- forall
ForallC : {TermG Term : Set} →
    (List Term) → 
    (Term → Constraint TermG) → 
    Constraint TermG
ForallC [] cf = Emp
ForallC (t ∷ ts) cf = cf t * ForallC ts cf

-- node assertion
NodeC : {Term : Set} → (s : Scope) → Term → Constraint Term
NodeC s t G = (decl (G s) ≡ t) , λ node-proof → < s ∷ [] , [] >

-- edge assertion
EdgeC : {Term : Set} → (e : Edge) → Constraint Term
EdgeC e@(s₁ , l , s₂) G = ((l , s₂) ∈ edges (G s₁)) , λ edge-proof → < [] , e ∷ [] >

-- data
DataOf : {Term : Set} → Scope → Term → Constraint Term
DataOf s t G = (decl (G s) ≡ t) , λ data-proof → empGf
