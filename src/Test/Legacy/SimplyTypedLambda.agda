module Test.Legacy.SimplyTypedLambda (Label : Set) where

open import Agda.Primitive
open import Data.Bool
open import Data.List
open import Data.Nat hiding (_+_ ; _*_)
open import Data.Product hiding (<_,_>)
open import Data.String
open import Data.Unit
open import Relation.Binary.PropositionalEquality

open import Statix.ConstraintData Label (Fin 2)
open import ScopeGraph.ScopeGraph Label


data Type : Set where
    num : Type
    _to_ : Type → Type → Type

data Expr : Set  where
    numLit : ℕ → Expr
    _+_ : Expr → Expr → Expr
    fun<_of_>body_ : Expr → Type → Expr → Expr
    var : String → Expr
    fun_app_ : Expr → Expr → Expr
    lett_be_inn_ : Expr → Expr → Expr → Expr

data ScopeName : Set where
    s'_ : String → ScopeName

data ScopeContent : Set where
    _:::_ : Expr → Type → ScopeContent


typeOfExpression : (Scope ScopeName ScopeContent) → Expr → Type → Constraint
typeOfExpression s (numLit n) t = Eq num t
typeOfExpression s (var x) t = {!   !}
typeOfExpression s (e1 + e2) t = Eq num t * 
    (typeOfExpression s e1 num * typeOfExpression s e2 num)
-- typeOfExpression s (fun< x of t1 >body e) t = ExistsC λ t2 → ExistsC λ sf → Eq (t1 to t2) t * Eq (scope "x") sf
typeOfExpression s (fun e1 app e2) t2 = ExistsC λ t1 → typeOfExpression s e1 (t1 to t2) * typeOfExpression s e2 t1
-- -- typeOfExpression s (lett e₁ be e₂ inn e₃) t = {!   !}
typeOfExpression s e t = {!   !}


-- data TypeOfExpression : Scope → Expr → Type → Constraint where
--     typeOfExpressionNum : { G : ScopeGraph } → { n : ℕ } → { t : Type } → { gf : ScopeGraphFragment } → { s : Scope } →
--         Eq num t G gf → TypeOfExpression s (numLit n) t G gf
--     typeOfExpressionAdd : { G : ScopeGraph } → { e1 e2 : Expr } → { t : Type } → { gf : ScopeGraphFragment } → { s : Scope } →
--         (Eq num t * (TypeOfExpression s e1 num * TypeOfExpression s e2 num)) G gf →
--         TypeOfExpression s (e1 + e2) t G gf
--     typeOfExpressionFun : { G : ScopeGraph } → { x e : Expr } → { t t1 : Type } → { gf : ScopeGraphFragment } → { s : Scope } →
--         (ExistsC λ t2 → ExistsC {Term = Scope} λ sf → Eq {Term = {! Type  !}} {! t  !} {!   !}) G gf → {!   !}