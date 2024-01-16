module SimpleTypeSystemFunction (Label : Set) where

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

typeOfExpression : Expr → Type → Constraint
typeOfExpression (numLit n) t = Eq num t
typeOfExpression (boolLit b) t = Eq bool t
typeOfExpression (e1 + e2) t = Eq num t * 
    (typeOfExpression e1 num * typeOfExpression e2 num)
typeOfExpression (e1 >' e2) t = Eq bool t * 
    (typeOfExpression e1 num * typeOfExpression e2 num)
typeOfExpression (if' cond then e1 else e2) t = typeOfExpression cond bool * 
    (typeOfExpression e1 t * typeOfExpression e2 t)


-- Type check examples
graphFragment : ScopeGraphFragment {Type}
graphFragment = < [] , [] >

-- Example 1
expr1 = (numLit 1) + (numLit 2)
ty1 = num

typeCheckExpression1 : {G : ScopeGraph} → typeOfExpression expr1 ty1 G graphFragment
typeCheckExpression1 = 
    (refl , refl) 
    ⟨ refl ⟩ 
    ((refl , refl) ⟨ refl ⟩ (refl , refl))

-- Example 2
expr2 = if' ((numLit 3) >' (numLit 2)) then ((numLit 1) + (numLit 2)) else (numLit 1)
ty2 = num

typeCheckExpression2 : {G : ScopeGraph} → typeOfExpression expr2 ty2 G graphFragment
typeCheckExpression2 = 
    ((refl , refl) ⟨ refl ⟩ ((refl , refl) ⟨ refl ⟩ (refl , refl)))
    ⟨ refl ⟩ 
    (typeCheckExpression1 ⟨ refl ⟩ (refl , refl))

