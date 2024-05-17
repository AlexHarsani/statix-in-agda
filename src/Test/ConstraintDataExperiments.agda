module Test.ConstraintDataExperiments where

open import Data.List
open import Data.Empty
open import Data.Fin
open import Data.String hiding (length)
open import Data.Nat
open import Data.Bool
open import Relation.Binary
open import Data.Product
open import Data.List.Relation.Unary.Any
open import Data.Unit
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.Core
open import Relation.Binary.Structures using (IsPreorder ; IsTotalPreorder)
open import Data.List.Relation.Unary.All renaming (_∷_ to _∷A_ ; [] to []A)


postulate
    Label : Set

Scope = (Fin 2)

open import Statix.ConstraintData Label
open import ScopeGraph.ScopeGraph Label
open ScopeGraphFragments
open Path

postulate
    Term : Set
    graph : ScopeGraph Scope Term
    t' : Term
    l p d : Label

data Type' : Set where
    t1' : Type'
    t2' : Type'

postulate
    graph' : ScopeGraph Scope Type'


emp-proof : proj₁ (sat graph EmpC)
emp-proof = tt

false-proof : proj₁ (sat graph FalseC) → ⊥
false-proof ()

conj-proof : proj₁ (sat graph (EmpC *C EmpC))
conj-proof = (tt , tt) , disjointEmpty

eq-proof : proj₁ (sat graph (EqC t1' t1'))
eq-proof = refl

exists-proof : proj₁ (sat graph (ExistsC λ t → EqC t t1'))
exists-proof = t1' , refl

graph2 : ScopeGraph Scope Type'
graph2 zero = (l , suc zero) ∷ [] , t1'
graph2 (suc zero) = (l , zero) ∷ [] , t2'

conj-invalid-proof : proj₁ (sat graph2 (NodeC zero t1' *C NodeC zero t1')) → ⊥
conj-invalid-proof = λ { ((fst , snd) , disjointNonEmpty x snd') → x (here refl) }

conj-nodes-proof : proj₁ (sat graph2 (NodeC (suc zero) t2' *C NodeC zero t1'))
conj-nodes-proof = (refl , refl) , disjointNonEmpty (λ { (here ()) ; (there ()) }) disjointEmpty

path-1 : Path graph2
path-1 = (zero , l) ::' (last' (suc zero))

queryC-proof : proj₁ (sat graph2 (QueryC zero (λ path → ⊤) (λ t → t ≡ t2') λ ts → ForallC ts λ t → EqC path-1 t))
queryC-proof = (query-proof (path-1 ∷ []) (λ { (here refl) → λ _ → here refl} ) (λ { (here refl) → λ _ → refl}) tt) , 
    (refl , tt) , disjointEmpty


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

min-proof : proj₁ (sat graph2 (MinC paths paths' shorter? shorterPreorder))
min-proof = refl

paths'' : List (Path graph2)
paths'' = []

min-proof' : proj₁ (sat graph2 (MinC paths paths'' shorter? shorterPreorder)) → ⊥
min-proof' = λ ()
