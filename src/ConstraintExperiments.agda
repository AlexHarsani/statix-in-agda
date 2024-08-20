module ConstraintExperiments where

open import Data.Empty
open import Data.Fin
open import Data.List
open import Data.List.Relation.Unary.Any
open import Data.Nat
open import Data.Product
open import Data.Unit
open import Relation.Binary
open import Relation.Binary.Core
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

postulate
    Label : Set

open import Constraint Label
open import ScopeGraph Label
open Path
open ScopeGraphFragments

postulate
    Term : Set
    graph : ScopeGraph 2 Term
    t' : Term
    l p d : Label

data Type' : Set where
    t1' : Type'
    t2' : Type'

postulate
    graph' : ScopeGraph 2 Type'


emp-proof : satisfies (sat graph EmpC)
emp-proof = tt

false-proof : satisfies (sat graph FalseC) → ⊥
false-proof ()

conj-proof : satisfies (sat graph (EmpC *C EmpC))
conj-proof = (tt , tt) , disjointEmpty

eq-proof : satisfies (sat graph (EqC t1' t1'))
eq-proof = refl

exists-proof : satisfies (sat graph (ExistsC λ t → EqC t t1'))
exists-proof = t1' , refl

graph2 : ScopeGraph 2 Type'
graph2 zero = (l , suc zero) ∷ [] , t1'
graph2 (suc zero) = (l , zero) ∷ [] , t2'

conj-invalid-proof : satisfies (sat graph2 (NodeC zero t1' *C NodeC zero t1')) → ⊥
conj-invalid-proof = λ { ((fst , snd) , disjointNonEmpty x snd') → x (here refl) }

conj-nodes-proof : satisfies (sat graph2 (NodeC (suc zero) t2' *C NodeC zero t1'))
conj-nodes-proof = (refl , refl) , disjointNonEmpty (λ { (here ()) ; (there ()) }) disjointEmpty

path-shorter : Path graph2
path-shorter = last' zero

path-longer : Path graph2
path-longer = (zero , l) ::' ((( suc zero , l )) ::' last' zero)

shorter : Rel (Path graph2) Agda.Primitive.lzero
shorter p1 p2 = Data.Nat._≤_ (pathLength p1) (pathLength p2)

shorter? : Decidable shorter
shorter? (last' x) (last' y) = yes z≤n
shorter? (last' x) (y ::' q) = yes z≤n
shorter? (x ::' p) (last' y) = no λ ()
shorter? (x ::' p) (y ::' q) with shorter? p q
... | yes proof = yes (s≤s proof)
... | no proof = no λ { (s≤s proof') → proof proof' }

proof-refl : _≡_ ⇒ shorter
proof-refl {last' x} refl = z≤n
proof-refl {x ::' xs} refl = s≤s (proof-refl {xs} refl)

proof-trans : { i j k : (Path graph2) } → shorter i j → shorter j k → shorter i k
proof-trans {last' x} {last' y} {last' z} t1 t2 = t2
proof-trans {last' x} {last' y} {z ::' zs} t1 t2 = t2
proof-trans {last' x} {y ::' ys} {z ::' zs} t1 t2 = z≤n
proof-trans {x ::' xs} {y ::' ys} {z ::' zs} (s≤s t1) (s≤s t2) = s≤s (proof-trans {xs} {ys} {zs} t1 t2)

shorterPreorder : IsPreorder _≡_ shorter
shorterPreorder = record { 
        isEquivalence = record {
            refl = refl ;
            sym = λ { refl → refl } ;
            trans = λ { refl → λ { t → t }} 
        } ; 
        reflexive = proof-refl ; 
        trans = proof-trans 
    }

paths' = path-shorter ∷ path-shorter ∷ []
paths = path-shorter ∷ path-shorter ∷ path-longer ∷ []

open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

min-proof : satisfies (sat graph2 (MinC paths paths' shorter? shorterPreorder))
min-proof = refl

paths'' : List (Path graph2)
paths'' = []

min-proof' : satisfies (sat graph2 (MinC paths paths'' shorter? shorterPreorder)) → ⊥
min-proof' = λ ()
 