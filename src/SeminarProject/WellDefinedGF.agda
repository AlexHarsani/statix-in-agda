module WellDefinedGF (L : Set) where

open import Data.List
open import Data.String hiding (_++_)
open import Relation.Binary.PropositionalEquality

open import Graph L
open import Constraint L

_⊔_ : GraphFragment → GraphFragment → GraphFragment
< nodes1 , edges1 > ⊔ < nodes2 , edges2 > = < nodes1 ++ nodes2 , edges1 ++ edges2 >

WellFormedGF = GraphFragment → Set

empGF : WellFormedGF
empGF gf = gf ≡ < [] , [] >

record _*'_ (WF1 WF2 : WellFormedGF) (gf : GraphFragment) : Set where
    constructor _⟨_⟩_
    field
        { gf1 gf2 } : GraphFragment
        gf1-wf : WF1 gf1
        gf-partition : gf1 ⊔ gf2 ≡ gf
        gf2-wf : WF2 gf2

_⇒_ : WellFormedGF → WellFormedGF → WellFormedGF
WF1 ⇒ WF2 = λ gf → WF1 gf → WF2 gf

∀[_] : WellFormedGF → Set
∀[ WF ] = ∀ { gf : GraphFragment } → WF gf

data Sat (G : Graph) : Constraint → WellFormedGF where
    satEmp : ∀[ empGF ⇒ Sat G emp ]
    satConj : { c1 c2 : Constraint } → ∀[ (Sat G c1 *' Sat G c2) ⇒ Sat G (c1 * c2) ]
    satEq : {t1 t2 : Term} → { termEq : t1 ≡ t2 } → ∀[ empGF ⇒ Sat G (t1 =t= t2) ]
    satExists : (x : String) → (c : Constraint) → {t : Term} → ∀[ Sat G (substitute c x t) ⇒ Sat G (existsT x c) ]
    satSingle : ( t : Term ) → ( ts : TermSet ) → { tsSingletonProof : ts ≡ (terms (t ∷ [])) } → 
        ∀[ empGF ⇒ Sat G (single t ts) ]
    satMin : ( t t' : TermSet ) → ( R : Relation ) → { minTermSetEq : t' ≡ minTermSet t R } →
        ∀[ empGF ⇒ Sat G (min t R t') ]
    satForallEmpty : ( x : String ) → ( ts : TermSet ) → ( c : Constraint ) → { tsEmpty : ts ≡ (terms []) } →
        ∀[ empGF ⇒ Sat G (forallT x ts c) ]
    satForall : (x : String) → ( c : Constraint ) → ( t : Term ) → ( ts : List Term ) →
        ∀[ (Sat G (substitute c x t) *' Sat G (forallT x (terms ts) c)) ⇒ Sat G (forallT x (terms (t ∷ ts)) c) ]

emp-sat : { G : Graph } → Sat G emp < [] , [] >
emp-sat = satEmp refl

conj-sat : { G : Graph } → Sat G (emp * emp) < [] , [] >
conj-sat = satConj (satEmp refl ⟨ refl ⟩ satEmp refl)

eq-sat : { G : Graph } → Sat G ((var "x") =t= (var "x")) < [] , [] >
eq-sat = satEq { termEq = refl } refl

exists-sat : { G : Graph } → { gf : GraphFragment } → Sat G (existsT "x" ((var "x") =t= (var "y"))) < [] , [] >
exists-sat = satExists "x" ((var "x") =t= (var "y")) (satEq { termEq = refl } refl)

single-sat : { G : Graph } → Sat G (single (var "x") ( terms ((var "x") ∷ []) )) < [] , [] >
single-sat = satSingle (var "x") (terms ((var "x") ∷ [])) { tsSingletonProof = refl } refl

postulate
    R : Relation
    min-ts-proof : { ts ts' : TermSet } → { R : Relation } → ts ≡ minTermSet ts' R
    
min-sat : { G : Graph } → Sat G (min (terms ((var "x") ∷ [])) R (terms ((var "x") ∷ []))) < [] , [] >
min-sat = satMin (terms ((var "x") ∷ [])) (terms ((var "x") ∷ [])) R { minTermSetEq = min-ts-proof } refl

forall-empty-sat : { G : Graph } → Sat G (forallT "x" (terms []) emp) < [] , [] >
forall-empty-sat = satForallEmpty "x" (terms []) emp { tsEmpty = refl } refl

forall-sat : { G : Graph } → Sat G (forallT "x" (terms ((var "y") ∷ [])) (((var "x") =t= (var "y")))) < [] , [] >
forall-sat = satForall "x" ((var "x") =t= (var "y")) ((var "y")) [] (
        satEq { termEq = refl } refl
        ⟨ refl ⟩ 
        satForallEmpty "x" ((terms [])) ((var "x") =t= (var "y")) { tsEmpty = refl } refl
    )
