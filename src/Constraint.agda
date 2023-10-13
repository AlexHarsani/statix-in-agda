module Constraint where

open import Data.List
open import Data.Unit
open import Data.Empty

open import Support
open import Graph

postulate
    Relation : Set

data Constraint : Set₁ where
    -- true
    emp : Constraint
    -- false
    false : Constraint
    -- separating conjunction
    _*_ : Constraint → Constraint → Constraint
    -- term equality
    _=t=_ : {L : Set} → Term L → Term L → Constraint
    -- existential quantification
    existsC_inC_ : {L : Set} → Term L → Constraint → Constraint
    -- set singletons
    single : {L : Set} → Term L → TermSet L → Constraint
    -- minimum
    min : {L : Set} → TermSet L → Relation → TermSet L → Constraint
    -- forall
    forallC_inC_ : {L : Set} → Term L → TermSet L → Constraint → Constraint

_withS_⊨_ : Graph → Support → Constraint → Set
g withS empty ⊨ emp = ⊤
g withS (σ₁ ⊔ σ₂) ⊨ (c₁ * c₂) = {!   !} and {!   !}

-- g withS (σ₁ ⊔ σ₂) ⊨ (c₁ * c₂) = (g withS σ₁ ⊨ c₁) and (g withS σ₂ ⊨ c₂)
g withS s ⊨ c = ⊥
-- g withS ⊥ ⊨ (t₁ =t= t₂) = t₁ === t₂
-- g withS ⊥ ⊨ (single t ts) = true
-- g withS ⊥ ⊨ (min ts₁ R ts₂) = {!   !}
-- g withS s ⊨ c = false
