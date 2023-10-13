{-# OPTIONS --allow-unsolved-metas #-}
module Support where

open import Data.List
open import Data.Bool

open import Graph

isDisjoint : {A : Set₁} → A → A → Set
isDisjoint s1 s2 = {!   !}

-- Scope graph support
-- proof that it is disjoint union
data Support : Set₁ where
    empty : Support
    <_,_> : {L : Set} → List Node → List (Edge L) → Support
    _⊔_ : (s1 s2 : Support) → {isDisjoint s1 s2} → Support


