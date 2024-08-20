module Test.TypePreservation where

open import Data.List
open import Data.Empty
open import Data.Maybe
open import Data.Fin hiding (_+_ ; _≥_)
open import Data.String hiding (length)
open import Data.Nat
open import Data.Bool
open import Data.Product hiding (<_,_>)
open import Data.List.Relation.Unary.Any
open import Data.List.Relation.Unary.Any.Properties
open import Data.List.Membership.Propositional
open import Data.Unit
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.Core
open import Relation.Nullary
open import Relation.Binary.Structures using (IsPreorder ; IsTotalPreorder)
open import Data.List.Relation.Unary.All renaming (_∷_ to _∷A_ ; [] to []A)
open import Data.List.Relation.Binary.Permutation.Propositional
open import Function using (case_of_)
open import Data.List.Relation.Binary.Sublist.Propositional
open import Data.List.Membership.Setoid.Properties

data Label : Set where
    l : Label
    d : Label

open import Statix.ConstraintData Label
open import ScopeGraph.ScopeGraph Label
open ScopeGraphFragments
open Path

data Type : Set where
    num : Type
    Ship : Type
    noType : Type

data Expr : Set  where
    numLit : ℕ → Expr
    _+'_ : Expr → Expr → Expr

data NodeTerm : Set where
    _|'_ : Expr → Type → NodeTerm
    empNode : NodeTerm

typeOfExpression' : {numberOfScopes : ℕ} → (g : ScopeGraph numberOfScopes NodeTerm) → 
    (Fin numberOfScopes) → Expr → Type → Constraint g
typeOfExpression' g s (numLit x) t = EqC num t
typeOfExpression' g s (e1 +' e2) t = EqC num t *C 
    (typeOfExpression' g s e1 num *C typeOfExpression' g s e2 num)


Env = List (String × Expr × Type)

lookupEnv : String → Env → Maybe Expr
lookupEnv x [] = nothing
lookupEnv x ((y , expr , ty) ∷ env) with x Data.String.≟ y
... | yes _ = just expr
... | no _ = lookupEnv x env

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

eval : Expr → Env → Expr
eval e env with view e
... | numView {n} = e
... | addLitView {n1} {n2} = (numLit (n1 + n2))
... | addOneView {n1} {e2} = (numLit n1) +' eval e2 env
... | addView {e1} {e2} = ((eval e1 env) +' e2)

if-disjoint-then-present-only-in-one : {numberOfScopes : ℕ} {g : ScopeGraph numberOfScopes NodeTerm}
    {gf1 gf2 : ScopeGraphFragment g} → 
    DisjointGraphFragments gf1 gf2 → 
    ∀ {s} → s ∈ ScopeGraphFragment.fragmentNodes gf1 → s ∉ ScopeGraphFragment.fragmentNodes gf2
if-disjoint-then-present-only-in-one disjointEmpty = λ ()
if-disjoint-then-present-only-in-one (disjointNonEmpty x disjoint) (here refl) = x
if-disjoint-then-present-only-in-one (disjointNonEmpty x disjoint) (there in-gf2) = 
    if-disjoint-then-present-only-in-one disjoint in-gf2

smaller-fragment-still-disjoint : {numberOfScopes : ℕ} {g : ScopeGraph numberOfScopes NodeTerm}
    {gf1 gf1' gf2 : ScopeGraphFragment g} →
    SubFragment gf1' gf1 →
    DisjointGraphFragments gf1 gf2 →
    DisjointGraphFragments gf1' gf2
smaller-fragment-still-disjoint subFragmentEmp disjoint = disjointEmpty
smaller-fragment-still-disjoint (subFragment in-gf1 sub) (disjointNonEmpty x₁ disjoint) = 
    disjointNonEmpty 
        (if-disjoint-then-present-only-in-one ((disjointNonEmpty x₁ disjoint)) in-gf1) 
        (smaller-fragment-still-disjoint sub (disjointNonEmpty x₁ disjoint))



∈-cons : {numberOfScopes : ℕ} → ∀ {x x' : Fin numberOfScopes} {xs} →
    x ∈ xs →
    x ∈ x' ∷ xs
∈-cons (here refl) = there (here refl)
∈-cons (there bbb) = there (there bbb)

∈-concat-left : {numberOfScopes : ℕ} → ∀ {x : Fin numberOfScopes} {xs ys : List (Fin numberOfScopes)} →
    x ∈ xs →
    x ∈ (xs Data.List.++ ys)
∈-concat-left (here refl) = here refl
∈-concat-left (there px) = there (∈-concat-left px)


∈-concat-right : {numberOfScopes : ℕ} → ∀ {x : Fin numberOfScopes} {xs ys : List (Fin numberOfScopes)} → 
    x ∈ xs → 
    x ∈ (ys Data.List.++ xs)
∈-concat-right {ys = []} in-xs = in-xs
∈-concat-right {ys = y ∷ ys} in-xs = there (∈-concat-right in-xs)


subfragment-nodes-concat : ∀ {numberOfScopes : ℕ} {g : ScopeGraph numberOfScopes NodeTerm} {edges edges' : List (Edge g)} →
    {nodes nodes' nodes'' : List (Fin numberOfScopes)} →
    SubFragment {g = g} < nodes , edges > < nodes' , edges' > →
    SubFragment {g = g} < nodes , edges > < nodes'' Data.List.++ nodes' , edges' >
subfragment-nodes-concat subFragmentEmp = subFragmentEmp
subfragment-nodes-concat {nodes'' = nodes''} (subFragment x sub) = subFragment (∈-concat-right {ys = nodes''} x) (subfragment-nodes-concat sub)

subfragment-same-nodes : ∀ {numberOfScopes : ℕ} {g : ScopeGraph numberOfScopes NodeTerm} {edges edges' : List (Edge g)} →
    (nodes : List (Fin numberOfScopes)) →
    SubFragment {g = g} < nodes , edges > < nodes , edges' >
subfragment-same-nodes [] = subFragmentEmp
subfragment-same-nodes (x ∷ nodes) = subFragment (here refl) (subfragment-nodes-concat (subfragment-same-nodes nodes))

subfragment-merge-left : ∀ {numberOfScopes : ℕ} {g : ScopeGraph numberOfScopes NodeTerm} {edges edges'} →
    (nodes : List (Fin numberOfScopes)) →
    (gf : ScopeGraphFragment g) →
    SubFragment < nodes , edges > (mergeFragments gf < nodes , edges' >)
subfragment-merge-left [] gf = subFragmentEmp
subfragment-merge-left nodes < [] , fragmentEdges > = subfragment-same-nodes nodes
subfragment-merge-left (s ∷ nodes) < fragmentNodes , fragmentEdges > =
    subFragment 
        (∈-concat-right (here refl)) 
        (subfragment-nodes-concat {nodes = nodes} {nodes' = s ∷ nodes} {nodes'' = fragmentNodes} (subfragment-merge-left nodes < s ∷ [] , fragmentEdges >))


subfragment-merge-preservation : {numberOfScopes : ℕ} {g : ScopeGraph numberOfScopes NodeTerm} →
            {gf1 gf1' gf2 : ScopeGraphFragment g} →
            SubFragment gf1' gf1 →
            SubFragment (mergeFragments gf1' gf2) (mergeFragments gf1 gf2)
subfragment-merge-preservation {gf1 = gf1} {gf2 = < nodes , edges >}  subFragmentEmp = subfragment-merge-left nodes gf1
subfragment-merge-preservation (subFragment (here refl) sub) = subFragment (here refl) (subfragment-merge-preservation sub)
subfragment-merge-preservation (subFragment (there x) sub) = subFragment (∈-cons (∈-concat-left x)) (subfragment-merge-preservation sub)


mutual
    type-preservation-proof : {numberOfScopes : ℕ} (g : ScopeGraph numberOfScopes NodeTerm) →
        (s : Fin numberOfScopes) →
        (e : Expr) (t : Type) (env : Env) →
        proj₁ (sat g (typeOfExpression' g s e t)) → 
        proj₁ (sat g (typeOfExpression' g s (eval e env) t))
    type-preservation-proof g s (numLit x) num env hypothesis = hypothesis
    type-preservation-proof g s (e1 +' e2) num env ((+-num , (e1-num , e2-num) , d1) , d2) with view (e1 +' e2)
    ... | addLitView = refl
    ... | addOneView = (refl , (refl , e2-type-preservation) , disjointEmpty) , disjointEmpty
        where
            e2-type-preservation = type-preservation-proof g s e2 num env e2-num
    ... | addView = (refl , (e1-type-preservation , e2-num) , 
            smaller-fragment-still-disjoint (no-nodes-added e1) d1) , disjointEmpty
        where
            e1-type-preservation = type-preservation-proof g s e1 num env e1-num
            
    no-nodes-added : {numberOfScopes : ℕ} {g : ScopeGraph numberOfScopes NodeTerm} {s' : Fin numberOfScopes} {env : Env} →
        (e : Expr) →
        {e-num : satisfies (sat g (typeOfExpression' g s' e num))} →
        SubFragment 
            (fragment (sat g (typeOfExpression' g s' (eval e env) num)) (type-preservation-proof g s' e num env e-num)) 
            (fragment (sat g (typeOfExpression' g s' e num)) e-num)
    no-nodes-added (numLit x) = subFragmentEmp
    no-nodes-added (e1 +' e2) with view (e1 +' e2)
    ... | addLitView = subFragmentEmp
    ... | addOneView = no-nodes-added e2
    ... | addView = subfragment-merge-preservation (no-nodes-added e1)


    
    