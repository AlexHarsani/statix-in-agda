module SimpleTypeSystemData (Label : Set) where

open import Agda.Primitive
open import Data.Bool
open import Data.List
open import Data.Nat hiding (_+_ ; _*_)
open import Data.Product hiding (<_,_>)
open import Data.Unit
open import Relation.Binary.PropositionalEquality

open import ScopeGraph Label
open import Constraint Label

data Expr : Set  where
    numLit : ℕ → Expr
    boolLit : Bool → Expr
    _+_ : Expr → Expr → Expr
    _>'_ : Expr → Expr → Expr
    if'_then_else_ : Expr → Expr → Expr → Expr

data Type : Set where
    bool : Type
    num : Type

data TypeOfExpression : Expr → Type → Constraint where
    typeOfExpressionNum : { G : ScopeGraph } → { n : ℕ } → { t : Type } → { gf : ScopeGraphFragment } →
        Eq num t G gf → TypeOfExpression (numLit n) t G gf
    typeOfExpressionBool : { G : ScopeGraph } → { b : Bool } → { t : Type } → { gf : ScopeGraphFragment } →
        Eq bool t G gf → TypeOfExpression (boolLit b) t G gf
    typeOfExpressionAdd : { G : ScopeGraph } → { e1 e2 : Expr } → { t : Type } → { gf : ScopeGraphFragment } →
        (Eq num t * (TypeOfExpression e1 num * TypeOfExpression e2 num)) G gf →
        TypeOfExpression (e1 + e2) t G gf
    typeOfExpressionLess : { G : ScopeGraph } → { e1 e2 : Expr } → { t : Type } → { gf : ScopeGraphFragment } →
        (Eq bool t * (TypeOfExpression e1 num * TypeOfExpression e2 num)) G gf →
        TypeOfExpression (e1 >' e2) t G gf
    typeOfExpressionIf : { G : ScopeGraph } → { cond e1 e2 : Expr } → { t : Type } → { gf : ScopeGraphFragment } →
        (TypeOfExpression cond bool * (TypeOfExpression e1 t * TypeOfExpression e2 t)) G gf →
        TypeOfExpression (if' cond then e1 else e2) t G gf


-- Type check examples
graphFragment : ScopeGraphFragment {Type}
graphFragment = < [] , [] >

-- Example 1
expr1 = (numLit 1) + (numLit 2)
ty1 = num

typeCheckExpression1 : {G : ScopeGraph} → TypeOfExpression expr1 ty1 G graphFragment
typeCheckExpression1 = typeOfExpressionAdd ((refl , refl) ⟨ refl ⟩ 
    ((typeOfExpressionNum (refl , refl)) ⟨ refl ⟩ (typeOfExpressionNum (refl , refl))))

-- Example 2
expr2 = if' (boolLit true) then ((numLit 1)) else (numLit 0)
ty2 = num

typeCheckExpression2 : {G : ScopeGraph} → TypeOfExpression expr2 ty2 G graphFragment
typeCheckExpression2 = typeOfExpressionIf (typeOfExpressionBool (refl , refl) ⟨ refl ⟩ 
    (typeOfExpressionNum (refl , refl) ⟨ refl ⟩ typeOfExpressionNum (refl , refl)))
