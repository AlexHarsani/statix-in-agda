module Test.SimplyTypedLambda where

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


data Label : Set where
    l : Label
    d : Label

open import Statix.ConstraintData Label
open import ScopeGraph.ScopeGraph Label
open ScopeGraphFragments
open Path

data Type : Set where
    num : Type
    bool : Type
    _to_ : Type → Type → Type

data Expr : Set  where
    numLit : ℕ → Expr
    boolLit : Bool → Expr
    _+'_ : Expr → Expr → Expr
    fun<_of_>body_ : Expr → Type → Expr → Expr
    var : String → Expr
    fun_app_ : Expr → Expr → Expr
    lett_be_inn_ : Expr → Expr → Expr → Expr

data NodeTerm : Set where
    _|'_ : Expr → Type → NodeTerm
    empNode : NodeTerm

typeOfExpression : {Scope : Set} → (g : ScopeGraph Scope NodeTerm) → Scope → Expr → Type → Constraint Scope g
typeOfExpression g s (numLit x) t = EqC num t
typeOfExpression g s (boolLit x) t = EqC bool t
typeOfExpression g s (e1 +' e2) t = EqC num t *C 
    (typeOfExpression g s e1 num *C typeOfExpression g s e2 num)
typeOfExpression g s (fun< x of t1 >body body) t = ExistsC λ t2 → ExistsC λ sf → EqC t (t1 to t2) *C 
   ((ExistsC λ sx → EdgeC (sf , d , sx) *C NodeC sx (x |' t1)) *C (EdgeC (sf , l , s) *C typeOfExpression g s body t2)) 
typeOfExpression g s (var x) t = QueryC s (λ _ → ⊤) (λ d → d ≡ (var x |' t)) λ paths → ExistsC λ path → SingleC path paths
typeOfExpression g s (fun e1 app e2) t2 = ExistsC λ t1 → typeOfExpression g s e1 (t1 to t2) *C typeOfExpression g s e2 t1
typeOfExpression g s (lett x be e1 inn e2) t2 = ExistsC λ t1 → ExistsC λ sb → (typeOfExpression g s e1 t1 *C 
    (ExistsC (λ sx → EdgeC (sb , d , sx) *C NodeC sx (x |' t1)) *C (EdgeC (sb , l , s) *C typeOfExpression g sb e2 t2)))


graph1 : ScopeGraph (Fin 3) NodeTerm
graph1 zero = (d , (suc zero)) ∷ [] , empNode
graph1 (suc zero) = (l , zero) ∷ (d , (suc (suc zero))) ∷ [] , empNode
graph1 (suc (suc zero)) = [] , ((var "x") |' bool)

program1 : Expr 
program1 = lett var "x" be (boolLit true) inn var "x"

type-check-proof : proj₁ (sat (Fin 3) graph1 (typeOfExpression graph1 zero program1 bool))  
type-check-proof = bool , suc zero , 
    (refl , ((suc (suc zero) , ( there (here refl) , refl) , disjointNonEmpty (λ { () }) disjointEmpty) , 
    (here refl , 
        (query-proof 
            (((zero , d) ::' ((suc zero , d) ::' last' (suc (suc zero)))) ∷ []) 
            (λ { (here refl) → λ { tt → here refl , there (here refl) } }) 
            (λ { (here refl) → λ t → refl }) 
            tt) , 
        ((zero , d) ::' ((suc zero , d) ::' last' (suc (suc zero)))) , refl) ,
    disjointEmpty) , 
    disjointEmpty) , disjointNonEmpty (λ { () }) disjointEmpty   


graph2 : ScopeGraph (Fin 3) NodeTerm
graph2 zero = (d , (suc zero)) ∷ [] , empNode
graph2 (suc zero) = (l , zero) ∷ (d , (suc (suc zero))) ∷ [] , empNode
graph2 (suc (suc zero)) = [] , ((var "x") |' num)

program2 : Expr 
program2 = lett var "x" be (numLit 2) inn (var "x" +' var "x")

type-check-proof2 : proj₁ (sat (Fin 3) graph2 (typeOfExpression graph2 zero program2 num))  
type-check-proof2 = num , suc zero , 
    (refl , ((suc (suc zero) , ( there (here refl) , refl) , disjointNonEmpty (λ { () }) disjointEmpty) , 
    (here refl , 
        (refl , (
            ((query-proof 
                (((zero , d) ::' ((suc zero , d) ::' last' (suc (suc zero)))) ∷ []) 
                (λ { (here refl) → λ { tt → here refl , there (here refl) } }) 
                (λ { (here refl) → λ t → refl }) 
                tt) 
            , ((zero , d) ::' ((suc zero , d) ::' last' (suc (suc zero)))) , refl) , 
            (query-proof 
                ((((zero , d) ::' ((suc zero , d) ::' last' (suc (suc zero)))) ∷ [])) 
                ((λ { (here refl) → λ { tt → here refl , there (here refl) } } )) 
                ((λ { (here refl) → λ t → refl })) tt) 
            , ((zero , d) ::' ((suc zero , d) ::' last' (suc (suc zero)))) , refl) , 
            disjointEmpty) , disjointEmpty) ,
    disjointEmpty) , 
    disjointEmpty) , disjointNonEmpty (λ { () }) disjointEmpty 