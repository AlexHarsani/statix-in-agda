module SimpleTypeSystemData (Label : Set) where

open import Agda.Primitive
open import Data.Bool
open import Data.List
open import Data.Nat hiding (_+_ ; _*_)
open import Data.Product hiding (<_,_>)
open import Data.Unit
open import Relation.Binary.PropositionalEquality

open import Graph Label
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
    typeOfExpressionNum : { n : ℕ } → { t : Type } → { gf : GraphFragment } →
        Eq num t gf → TypeOfExpression (numLit n) t gf
    typeOfExpressionBool : { b : Bool } → { t : Type } → { gf : GraphFragment } →
        Eq bool t gf → TypeOfExpression (boolLit b) t gf
    typeOfExpressionAdd : { e1 e2 : Expr } → { t : Type } → { gf : GraphFragment } →
        (Eq num t * (TypeOfExpression e1 num * TypeOfExpression e2 num)) gf →
        TypeOfExpression (e1 + e2) t gf
    typeOfExpressionLess : { e1 e2 : Expr } → { t : Type } → { gf : GraphFragment } →
        (Eq bool t * (TypeOfExpression e1 num * TypeOfExpression e2 num)) gf →
        TypeOfExpression (e1 >' e2) t gf
    typeOfExpressionIf : { cond e1 e2 : Expr } → { t : Type } → { gf : GraphFragment } →
        (TypeOfExpression cond bool * (TypeOfExpression e1 t * TypeOfExpression e2 t)) gf →
        TypeOfExpression (if' cond then e1 else e2) t gf


-- Type check examples
graphFragment : GraphFragment {Type}
graphFragment = < [] , [] >

-- Example 1
expr1 = (numLit 1) + (numLit 2)
ty1 = num

typeCheckExpression1 : TypeOfExpression expr1 ty1 graphFragment
typeCheckExpression1 = typeOfExpressionAdd ((refl , refl) ⟨ refl ⟩ 
    ((typeOfExpressionNum (refl , refl)) ⟨ refl ⟩ (typeOfExpressionNum (refl , refl))))

-- Example 2
expr2 = if' (boolLit true) then ((numLit 1)) else (numLit 0)
ty2 = num

typeCheckExpression2 : TypeOfExpression expr2 ty2 graphFragment
typeCheckExpression2 = typeOfExpressionIf (typeOfExpressionBool (refl , refl) ⟨ refl ⟩ 
    (typeOfExpressionNum (refl , refl) ⟨ refl ⟩ typeOfExpressionNum (refl , refl)))
