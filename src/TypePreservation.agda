module TypePreservation where

open import Data.Fin hiding (_+_ ; _≥_)
open import Data.List
open import Data.List.Membership.Propositional
open import Data.List.Relation.Unary.Any
open import Data.Maybe
open import Data.Nat
open import Data.Product hiding (<_,_>)
open import Data.String
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

data Label : Set where
    l : Label
    d : Label

open import Constraint Label
open import ScopeGraph Label
open Path
open ScopeGraphFragments

data Type : Set where
    num : Type
    Ship : Type

data Expr : Set  where
    numLit : ℕ → Expr
    _+'_ : Expr → Expr → Expr

data NodeTerm : Set where
    _|'_ : Expr → Type → NodeTerm
    empNode : NodeTerm

variable
    numberOfScopes : ℕ
    g : ScopeGraph numberOfScopes NodeTerm

typeOfExpression' : (g : ScopeGraph numberOfScopes NodeTerm) → 
    (Fin numberOfScopes) → Expr → Type → Constraint g
typeOfExpression' g s (numLit x) t = EqC num t
typeOfExpression' g s (e1 +' e2) t = EqC num t *C 
    (typeOfExpression' g s e1 num *C typeOfExpression' g s e2 num)

data ExprView : Expr → Set where        
    numView : ∀ {n} → ExprView (numLit n)
    addLitView : {n1 n2 : ℕ} → ExprView ((numLit n1) +' (numLit n2))
    addOneView : ∀ {n1 : ℕ} {e2 : Expr} → ExprView ((numLit n1) +' e2)
    addView : ∀ {e1 e2} → ExprView (e1 +' e2)

view : (e : Expr) → ExprView e
view (numLit x) = numView
view ((numLit n1) +' (numLit n2)) = addLitView
view ((numLit n1) +' e2) = addOneView
view (e +' e₁) = addView

eval : Expr → Expr
eval e with view e
... | numView {n} = e
... | addLitView {n1} {n2} = (numLit (n1 + n2))
... | addOneView {n1} {e2} = (numLit n1) +' eval e2
... | addView {e1} {e2} = ((eval e1) +' e2)

if-disjoint-then-present-only-in-one : {gf1 gf2 : ScopeGraphFragment g} → 
    DisjointGraphFragments gf1 gf2 → 
    ∀ {s} → s ∈ ScopeGraphFragment.fragmentNodes gf1 → s ∉ ScopeGraphFragment.fragmentNodes gf2
if-disjoint-then-present-only-in-one disjointEmpty = λ ()
if-disjoint-then-present-only-in-one (disjointNonEmpty x disjoint) (here refl) = x
if-disjoint-then-present-only-in-one (disjointNonEmpty x disjoint) (there in-gf2) = 
    if-disjoint-then-present-only-in-one disjoint in-gf2

smaller-fragment-still-disjoint : {gf1 gf1' gf2 : ScopeGraphFragment g} →
    SubFragment gf1' gf1 →
    DisjointGraphFragments gf1 gf2 →
    DisjointGraphFragments gf1' gf2
smaller-fragment-still-disjoint subFragmentEmp disjoint = disjointEmpty
smaller-fragment-still-disjoint (subFragment in-gf1 sub) (disjointNonEmpty x₁ disjoint) = 
    disjointNonEmpty 
        (if-disjoint-then-present-only-in-one ((disjointNonEmpty x₁ disjoint)) in-gf1) 
        (smaller-fragment-still-disjoint sub (disjointNonEmpty x₁ disjoint))



∈-cons : ∀ {x x' : Fin numberOfScopes} {xs} →
    x ∈ xs →
    x ∈ x' ∷ xs
∈-cons (here refl) = there (here refl)
∈-cons (there bbb) = there (there bbb)

∈-concat-left : ∀ {x : Fin numberOfScopes} {xs ys : List (Fin numberOfScopes)} →
    x ∈ xs →
    x ∈ (xs Data.List.++ ys)
∈-concat-left (here refl) = here refl
∈-concat-left (there px) = there (∈-concat-left px)


∈-concat-right : ∀ {x : Fin numberOfScopes} {xs ys : List (Fin numberOfScopes)} → 
    x ∈ xs → 
    x ∈ (ys Data.List.++ xs)
∈-concat-right {ys = []} in-xs = in-xs
∈-concat-right {ys = y ∷ ys} in-xs = there (∈-concat-right in-xs)


subfragment-nodes-concat : ∀ {edges edges' : List (Edge g)} →
    {nodes nodes' nodes'' : List (Fin numberOfScopes)} →
    SubFragment {g = g} < nodes , edges > < nodes' , edges' > →
    SubFragment {g = g} < nodes , edges > < nodes'' Data.List.++ nodes' , edges' >
subfragment-nodes-concat subFragmentEmp = subFragmentEmp
subfragment-nodes-concat {nodes'' = nodes''} (subFragment x sub) = subFragment (∈-concat-right {ys = nodes''} x) (subfragment-nodes-concat sub)

subfragment-same-nodes : ∀ {edges edges' : List (Edge g)} →
    (nodes : List (Fin numberOfScopes)) →
    SubFragment {g = g} < nodes , edges > < nodes , edges' >
subfragment-same-nodes [] = subFragmentEmp
subfragment-same-nodes (x ∷ nodes) = subFragment (here refl) (subfragment-nodes-concat (subfragment-same-nodes nodes))

subfragment-merge-left : ∀ {edges edges'} →
    (nodes : List (Fin numberOfScopes)) →
    (gf : ScopeGraphFragment g) →
    SubFragment < nodes , edges > (mergeFragments gf < nodes , edges' >)
subfragment-merge-left [] gf = subFragmentEmp
subfragment-merge-left nodes < [] , fragmentEdges > = subfragment-same-nodes nodes
subfragment-merge-left (s ∷ nodes) < fragmentNodes , fragmentEdges > =
    subFragment 
        (∈-concat-right (here refl)) 
        (subfragment-nodes-concat {nodes = nodes} {nodes' = s ∷ nodes} {nodes'' = fragmentNodes} (subfragment-merge-left nodes < s ∷ [] , fragmentEdges >))


subfragment-merge-preservation : {gf1 gf1' gf2 : ScopeGraphFragment g} →
    SubFragment gf1' gf1 →
    SubFragment (mergeFragments gf1' gf2) (mergeFragments gf1 gf2)
subfragment-merge-preservation {gf1 = gf1} {gf2 = < nodes , edges >}  subFragmentEmp = subfragment-merge-left nodes gf1
subfragment-merge-preservation (subFragment (here refl) sub) = subFragment (here refl) (subfragment-merge-preservation sub)
subfragment-merge-preservation (subFragment (there x) sub) = subFragment (∈-cons (∈-concat-left x)) (subfragment-merge-preservation sub)


mutual
    type-preservation-proof : (g : ScopeGraph numberOfScopes NodeTerm) →
        (s : Fin numberOfScopes) →
        (e : Expr) (t : Type) →
        satisfies (sat g (typeOfExpression' g s e t)) → 
        satisfies (sat g (typeOfExpression' g s (eval e) t))
    type-preservation-proof g s (numLit x) num hypothesis = hypothesis
    type-preservation-proof g s (e1 +' e2) num ((+-num , (e1-num , e2-num) , d1) , d2) with view (e1 +' e2)
    ... | addLitView = refl
    ... | addOneView = (refl , (refl , e2-type-preservation) , disjointEmpty) , disjointEmpty
        where
            e2-type-preservation = type-preservation-proof g s e2 num e2-num
    ... | addView = (refl , (e1-type-preservation , e2-num) , 
            smaller-fragment-still-disjoint (no-nodes-added e1) d1) , disjointEmpty
        where
            e1-type-preservation = type-preservation-proof g s e1 num e1-num
            
    no-nodes-added : {s : Fin numberOfScopes} → (e : Expr) →
        {e-num : satisfies (sat g (typeOfExpression' g s e num))} →
        SubFragment 
            (fragment (sat g (typeOfExpression' g s (eval e) num)) (type-preservation-proof g s e num e-num)) 
            (fragment (sat g (typeOfExpression' g s e num)) e-num)
    no-nodes-added (numLit x) = subFragmentEmp
    no-nodes-added (e1 +' e2) with view (e1 +' e2)
    ... | addLitView = subFragmentEmp
    ... | addOneView = no-nodes-added e2
    ... | addView = subfragment-merge-preservation (no-nodes-added e1)


    
    