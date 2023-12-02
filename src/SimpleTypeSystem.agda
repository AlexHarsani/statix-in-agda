module SimpleTypeSystem (Label : Set) where

open import Agda.Primitive
open import Data.Bool
open import Data.List
open import Data.Nat hiding (_+_ ; _*_)
open import Data.Product hiding (<_,_>)
open import Data.Unit
open import Relation.Binary.PropositionalEquality

data Expr : Set  where
    num : ℕ → Expr
    bool : Bool → Expr
    _+_ : Expr → Expr → Expr
    if'_then_else_ : Expr → Expr → Expr → Expr

data Type : Set where
    bool : Type
    num : Type

data Term : Set where
    expr : Expr → Term
    ty : Type → Term

open import Graph Label Term
open import Constraint Label Term

typeOfExpression : Term → Term → Constraint
typeOfExpression (expr (num n)) t = Eq (ty num) t
typeOfExpression (expr (bool b)) t = Eq (ty bool) t
typeOfExpression (expr (e1 + e2)) t = Eq (ty num) t * 
    (typeOfExpression (expr e1) (ty num) * typeOfExpression (expr e2) (ty num))
typeOfExpression (expr (if' cond then e1 else e2)) t = typeOfExpression (expr cond) (ty bool) * 
    (typeOfExpression (expr e1) t * typeOfExpression (expr e2) t)
typeOfExpression e t = False


-- Type check examples

graphFragment = < [] , [] >

-- Example 1
expr1 = expr ((num 1) + (num 2))
ty1 = ty num

typeCheckExpression1 : typeOfExpression expr1 ty1 graphFragment
typeCheckExpression1 = (refl , refl) ⟨ refl ⟩ ((refl , refl) ⟨ refl ⟩ (refl , refl))

-- Example 2
expr2 = expr (if' (bool true) then ((num 1) + (num 2)) else (num 1))
ty2 = ty num

typeCheckExpression2 : typeOfExpression expr2 ty2 graphFragment
typeCheckExpression2 = (refl , refl) ⟨ refl ⟩ (typeCheckExpression1 ⟨ refl ⟩ (refl , refl))

-- Example 3, does not type check
expr3 = expr ((num 1) + (bool true))
ty3 = ty num

typeCheckExpression3 : typeOfExpression expr3 ty3 graphFragment
typeCheckExpression3 = (refl , refl) ⟨ refl ⟩ ((refl , refl) ⟨ refl ⟩ (refl , {!   !}))

