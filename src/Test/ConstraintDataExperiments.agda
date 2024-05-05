module Test.ConstraintDataExperiments where

open import Data.List
open import Data.Empty
open import Data.Fin
open import Data.String hiding (length)
open import Data.Nat
open import Data.Bool
open import Data.Product
open import Data.List.Relation.Unary.Any
open import Data.Unit
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.Core
open import Relation.Binary.Structures using (IsPreorder ; IsTotalPreorder)
open import Data.List.Relation.Unary.All renaming (_∷_ to _∷A_ ; [] to []A)


postulate
    Label : Set

Scope = (Fin 2)

open import Statix.ConstraintData Label Scope
open import ScopeGraph.ScopeGraph Label Scope
open ScopeGraphFragments
open Path

postulate
    Term : Set
    graph : ScopeGraph Term
    t' : Term
    l p d : Label

data Type' : Set where
    t1' : Type'
    t2' : Type'

postulate
    graph' : ScopeGraph Type'


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

graph2 : ScopeGraph Type'
graph2 zero = (l , suc zero) ∷ [] , t1'
graph2 (suc zero) = (l , zero) ∷ [] , t2'

conj-invalid-proof : proj₁ (sat graph2 (NodeC zero t1' *C NodeC zero t1')) → ⊥
conj-invalid-proof = λ { ((fst , snd) , disjointNonEmpty x snd') → x (here refl) }

conj-nodes-proof : proj₁ (sat graph2 (NodeC (suc zero) t2' *C NodeC zero t1'))
conj-nodes-proof = (refl , refl) , disjointNonEmpty (λ { (here ()) ; (there ()) }) disjointEmpty

path-1 : Path
path-1 = (zero , l) ::' (last' (suc zero))

queryC-proof : proj₁ (sat graph2 (QueryC zero (λ path → ⊤) (λ t → t ≡ t2') λ ts → ForallC ts λ t → EqC path-1 t))
queryC-proof = (query-proof (path-1 ∷ []) (λ { (here refl) → λ _ → here refl} ) (λ { (here refl) → λ _ → refl}) tt) , 
    (refl , tt) , disjointEmpty


path-shorter : Path
path-shorter = last' zero

path-longer : Path
path-longer = (zero , l) ::' ((( suc zero , l )) ::' last' zero)

shorter : Rel Path Agda.Primitive.lzero
shorter p1 p2 = Data.Nat._≤_ (pathLength p1) (pathLength p2)

proof-refl : _≡_ ⇒ shorter
proof-refl {last' x} refl = z≤n
proof-refl {x ::' xs} refl = s≤s (proof-refl {xs} refl)

proof-trans : { i j k : Path } → shorter i j → shorter j k → shorter i k
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

paths' = path-shorter ∷ []
paths = path-shorter ∷ path-longer ∷ []

min-proof : proj₁ (sat graph (MinC paths paths' shorter shorterPreorder))
min-proof = (λ t1 → λ { (here refl) → λ z → z
                      ; (there (here refl)) → λ _ → z≤n }) ∷A []A
    


data Type : Set where
    num : Type
    _to_ : Type → Type → Type

data Expr : Set  where
    numLit : ℕ → Expr
    _+'_ : Expr → Expr → Expr
    fun<_of_>body_ : Expr → Type → Expr → Expr
    var : String → Expr
    fun_app_ : Expr → Expr → Expr
    lett_be_inn_ : Expr → Expr → Expr → Expr


typeOfExpression : (g : ScopeGraph Expr) → Scope → Expr → Type → Constraint g
typeOfExpression g s (numLit x) t = EqC num t
typeOfExpression g s (e1 +' e2) t = EqC num t *C 
    (typeOfExpression g s e1 num *C typeOfExpression g s e2 num)
typeOfExpression g s (fun< x of t1 >body body) t = ExistsC λ t2 → ExistsC λ sf → EqC t (t1 to t2) *C 
   ((ExistsC λ sx → EdgeC (sf , d , sx) *C NodeC sx x) *C (EdgeC (sf , p , s) *C typeOfExpression g s body t1)) 
typeOfExpression g s (var x) t = QueryC s (λ _ → ⊤) (λ e → e ≡ var x) λ paths → ForallC paths λ path → SingleC path paths
typeOfExpression g s (fun e1 app e2) t2 = ExistsC λ t1 → typeOfExpression g s e1 (t1 to t2) *C typeOfExpression g s e2 t1
typeOfExpression g s (lett x be e1 inn e2) t2 = ExistsC λ t1 → ExistsC λ sb → (typeOfExpression g s e1 t1 *C 
    (ExistsC (λ sx → EdgeC (sb , d , sx) *C NodeC sx x) *C (EdgeC (sb , p , s) *C typeOfExpression g sb e2 t2)))

