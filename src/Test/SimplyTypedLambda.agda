module Test.SimplyTypedLambda where

open import Data.List
open import Data.Empty
open import Data.Maybe
open import Data.Fin hiding (_+_ ; _≥_)
open import Data.String hiding (length)
open import Data.Nat
open import Data.Bool
open import Data.Product hiding (<_,_>)
open import Data.List.Relation.Unary.Any
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
open import Relation.Binary.Structures using (IsPreorder ; IsTotalPreorder)
open import Relation.Binary.Definitions



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
    fun<_of_>body_ : String → Type → Expr → Expr
    var : String → Expr
    fun_app_ : Expr → Expr → Expr
    lett_be_inn_ : String → Expr → Expr → Expr

data NodeTerm : Set where
    _|'_ : Expr → Type → NodeTerm
    empNode : NodeTerm

typeOfExpression' : {numberOfScopes : ℕ} → (g : ScopeGraph numberOfScopes NodeTerm) → (Fin numberOfScopes) → 
    Expr → Type → Constraint g
typeOfExpression' g s (numLit x) t = EqC num t
typeOfExpression' g s (boolLit x) t = EqC bool t
typeOfExpression' g s (e1 +' e2) t = EqC num t *C 
    (typeOfExpression' g s e1 num *C typeOfExpression' g s e2 num)
typeOfExpression' g s (fun< x of t1 >body body) t = ExistsC λ t2 → ExistsC λ sf → (NodeC sf empNode) *C 
    (EdgeC (s , d , sf) *C (EqC t (t1 to t2) *C 
    ((ExistsC λ sx → EdgeC (sf , d , sx) *C NodeC sx (var x |' t1)) *C (EdgeC (sf , l , s) *C 
    typeOfExpression' g sf body t2))))
typeOfExpression' g s (fun e1 app e2) t2 = ExistsC λ t1 → typeOfExpression' g s e1 (t1 to t2) *C 
    typeOfExpression' g s e2 t1
typeOfExpression' g s (var x) t = QueryC s (λ _ → ⊤) (λ d → d ≡ (var x |' t)) λ paths → 
    ExistsC λ path → SingleC path paths
typeOfExpression' g s (lett x be e1 inn e2) t2 = (ExistsC λ t1 → ExistsC λ sb → (NodeC sb empNode) *C 
    (EdgeC (s , d , sb) *C (typeOfExpression' g s e1 t1 *C 
    (ExistsC (λ sx → EdgeC (sb , d , sx) *C NodeC sx (var x |' t1)) *C (EdgeC (sb , l , s) *C 
    typeOfExpression' g sb e2 t2)))))

typeOfExpression : {numberOfScopes : ℕ} → (g : ScopeGraph numberOfScopes NodeTerm) → 
    (Fin numberOfScopes) → Expr → Type → Constraint g
typeOfExpression g s e t = NodeC s empNode *C typeOfExpression' g s e t


module Proofs where

    graph1 : ScopeGraph 3 NodeTerm
    graph1 zero = (d , (suc zero)) ∷ [] , empNode
    graph1 (suc zero) = (l , zero) ∷ (d , (suc (suc zero))) ∷ [] , empNode
    graph1 (suc (suc zero)) = [] , ((var "x") |' bool)

    program1 : Expr 
    program1 = lett "x" be (boolLit true) inn var "x"

    type-check-proof : proj₁ (sat graph1 (typeOfExpression graph1 zero program1 bool))  
    type-check-proof = (refl , bool , suc zero , 
        (refl , (here refl , (refl , ((suc (suc zero) , (there (here refl) , refl) , disjointEmpty) , 
        (here refl , ((query-proof 
                    ((((suc zero , d) ::' last' (suc (suc zero)))) ∷ [])
                    (λ { (here refl) → there (here refl) })
                    (λ { (here refl) → (λ { () }) , λ { (here ())
                                                    ; (there ()) } })
                    (λ { (here refl) → tt })
                    (λ { (here refl) → refl })
                    (λ { (here refl) → refl })
                    λ { {last' zero} noCycle → λ validWord → λ validPath → λ { () }
                    ; {last' (suc (suc zero))} noCycle → λ validWord → λ validPath → λ { () }
                    ; {(suc zero , d) ::' last' (suc (suc zero))} noCycle → λ validWord → λ validPath → λ validStart → λ validEnd → here refl
                    ; {(suc zero , l) ::' last' (suc (suc zero))} noCycle → λ validWord → λ {  (there (here ()))
                                                                                            ; (there (there ())) }
                    ; {(suc zero , label) ::' ((zero , label2) ::' ((zero , label3) ::' path))} (a , b , c , rest) → ⊥-elim (c (here refl))
                    ; {(suc zero , label) ::' ((zero , label2) ::' ((suc zero , label3) ::' path))} (a , b , c , rest) → ⊥-elim (c (there (here refl)))
                    ; {(suc zero , label) ::' ((zero , label2) ::' ((suc (suc zero) , label3) ::' path))} noCycle → λ validWord → λ { (fst , here () , snd)
                                                                                                                                    ; (fst , there () , snd) }
                    ; {(suc zero , label) ::' ((zero , label2) ::' (last' (suc (suc zero))))} noCycle → λ validWord → λ { (fst , here ())
                                                                                                                        ; (fst , there ()) }
                    ; {(suc zero , label) ::' ((suc zero , label2) ::' path)} (a , b , c) → ⊥-elim (b (here refl))
                    ; {(suc zero , label) ::' ((suc (suc zero) , label2) ::' ((suc (suc zero) , label3) ::' path))} (a , b , c , rest) → ⊥-elim (c (here refl))
                    }
                    )) , (((suc zero , d) ::' last' (suc (suc zero)))) , refl) , disjointEmpty) , 
        disjointNonEmpty (λ { () }) disjointEmpty) , disjointEmpty) , disjointEmpty) , 
        disjointNonEmpty (λ { (here ())
                            ; (there ()) }) disjointEmpty) , disjointNonEmpty (λ { (there (here ()))
                                                                                 ; (there (there ())) }) disjointEmpty
    
    type-check-fragment : validTopLevelGraphFragment ((typeOfExpression graph1 zero program1 bool)) type-check-proof
    type-check-fragment =  refl , prep (zero , d , suc zero) (_↭_.swap (suc zero , d , suc (suc zero)) (suc zero , l , zero) refl)


    graph2 : ScopeGraph 3 NodeTerm
    graph2 zero = (d , (suc zero)) ∷ [] , empNode
    graph2 (suc zero) = (l , zero) ∷ (d , (suc (suc zero))) ∷ [] , empNode
    graph2 (suc (suc zero)) = [] , ((var "x") |' num)

    program2 : Expr 
    program2 = fun< "x" of num >body var "x"

    type-check-proof2 : proj₁ (sat graph2 (typeOfExpression graph2 zero program2 (num to num)))
    type-check-proof2 = (refl , num , suc zero , (refl , (here refl , (refl , ((suc (suc zero) , 
        (there (here refl) , refl) , disjointEmpty) , (here refl , query-proof 
            (((((suc zero , d) ::' last' (suc (suc zero)))) ∷ [])) 
            ((λ { (here refl) → there (here refl) })) 
            ((λ { (here refl) → (λ { () }) , λ { (here ()) ; (there ()) } })) 
            ((λ { (here refl) → tt })) 
            (λ { (here refl) → refl }) 
            ((λ { (here refl) → refl })) 
            (λ { {last' zero} noCycle → λ validWord → λ validPath → λ { () }
                    ; {last' (suc (suc zero))} noCycle → λ validWord → λ validPath → λ { () }
                    ; {(suc zero , d) ::' last' (suc (suc zero))} noCycle → λ validWord → λ validPath → λ validStart → λ validEnd → here refl
                    ; {(suc zero , l) ::' last' (suc (suc zero))} noCycle → λ validWord → λ {  (there (here ()))
                                                                                            ; (there (there ())) }
                    ; {(suc zero , label) ::' ((zero , label2) ::' ((zero , label3) ::' path))} (a , b , c , rest) → ⊥-elim (c (here refl))
                    ; {(suc zero , label) ::' ((zero , label2) ::' ((suc zero , label3) ::' path))} (a , b , c , rest) → ⊥-elim (c (there (here refl)))
                    ; {(suc zero , label) ::' ((zero , label2) ::' ((suc (suc zero) , label3) ::' path))} noCycle → λ validWord → λ { (fst , here () , snd)
                                                                                                                                    ; (fst , there () , snd) }
                    ; {(suc zero , label) ::' ((zero , label2) ::' (last' (suc (suc zero))))} noCycle → λ validWord → λ { (fst , here ())
                                                                                                                        ; (fst , there ()) }
                    ; {(suc zero , label) ::' ((suc zero , label2) ::' path)} (a , b , c) → ⊥-elim (b (here refl))
                    ; {(suc zero , label) ::' ((suc (suc zero) , label2) ::' ((suc (suc zero) , label3) ::' path))} (a , b , c , rest) → ⊥-elim (c (here refl))
                    }) , ((((suc zero , d) ::' last' (suc (suc zero))))) , refl) , disjointEmpty) , disjointNonEmpty (λ { () }) disjointEmpty) , disjointEmpty) , disjointEmpty) , disjointNonEmpty (λ { (here ()) ; (there ()) }) disjointEmpty) , disjointNonEmpty (λ { (there (here ())) ; (there (there ())) }) disjointEmpty   

    type-check-fragment2 : validTopLevelGraphFragment ((typeOfExpression graph2 zero program2 (num to num))) type-check-proof2
    type-check-fragment2 = refl , prep (zero , d , suc zero) (_↭_.swap (suc zero , d , suc (suc zero)) (suc zero , l , zero)  refl)

    program3 : Expr
    program3 = fun program2 app numLit 3

    type-check-proof3 : proj₁ (sat graph2 (typeOfExpression graph2 zero program3 num))
    type-check-proof3 = (refl , num , ((num , suc zero , (refl , (here refl , (refl , 
        ((suc (suc zero) , (there (here refl) , refl) , disjointEmpty) , (here refl , query-proof 
            (((((suc zero , d) ::' last' (suc (suc zero)))) ∷ [])) 
            ((λ { (here refl) → there (here refl) })) 
            ((λ { (here refl) → (λ { () }) , λ { (here ()) ; (there ()) } })) 
            ((λ { (here refl) → tt })) 
            (λ { (here refl) → refl }) 
            ((λ { (here refl) → refl })) ((λ { {last' zero} noCycle → λ validWord → λ validPath → λ { () }
                    ; {last' (suc (suc zero))} noCycle → λ validWord → λ validPath → λ { () }
                    ; {(suc zero , d) ::' last' (suc (suc zero))} noCycle → λ validWord → λ validPath → λ validStart → λ validEnd → here refl
                    ; {(suc zero , l) ::' last' (suc (suc zero))} noCycle → λ validWord → λ {  (there (here ()))
                                                                                            ; (there (there ())) }
                    ; {(suc zero , label) ::' ((zero , label2) ::' ((zero , label3) ::' path))} (a , b , c , rest) → ⊥-elim (c (here refl))
                    ; {(suc zero , label) ::' ((zero , label2) ::' ((suc zero , label3) ::' path))} (a , b , c , rest) → ⊥-elim (c (there (here refl)))
                    ; {(suc zero , label) ::' ((zero , label2) ::' ((suc (suc zero) , label3) ::' path))} noCycle → λ validWord → λ { (fst , here () , snd)
                                                                                                                                    ; (fst , there () , snd) }
                    ; {(suc zero , label) ::' ((zero , label2) ::' (last' (suc (suc zero))))} noCycle → λ validWord → λ { (fst , here ())
                                                                                                                        ; (fst , there ()) }
                    ; {(suc zero , label) ::' ((suc zero , label2) ::' path)} (a , b , c) → ⊥-elim (b (here refl))
                    ; {(suc zero , label) ::' ((suc (suc zero) , label2) ::' ((suc (suc zero) , label3) ::' path))} (a , b , c , rest) → ⊥-elim (c (here refl))
                    })) , (((suc zero , d) ::' last' (suc (suc zero)))) , refl) , disjointEmpty) , disjointNonEmpty (λ { () }) disjointEmpty) , disjointEmpty) , disjointEmpty) , 
        disjointNonEmpty (λ { (here ()) ; (there ()) }) disjointEmpty) , refl) , disjointNonEmpty (λ { () }) (disjointNonEmpty (λ { () }) disjointEmpty)) , disjointNonEmpty (λ { (there (here ())) ; (there (there ())) }) disjointEmpty  

    type-check-fragment3 : validTopLevelGraphFragment ((typeOfExpression graph2 zero program3 (num))) type-check-proof3
    type-check-fragment3 = refl , prep (zero , d , suc zero) (_↭_.swap (suc zero , d , suc (suc zero)) (suc zero , l , zero) refl)  