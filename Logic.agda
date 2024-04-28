{-# OPTIONS --safe #-}

module Logic where

open import Data.Product using (_×_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open Data.Product using (_,_; swap; proj₁; proj₂) public
open import Data.Unit using (⊤)
open import Relation.Nullary using (yes; no; Dec)

infixr 2 _∧_
infixr 1 _∨_

_∧_ = _×_
_∨_ = _⊎_

pattern left l = inj₁ l
pattern right r = inj₂ r

-- maybe use Dec.from-yes?
-- let the computer do tedious proofs for us
-- https://stackoverflow.com/questions/30862844/how-to-prove-there-exist-a-rational-which-is-less-than-some-rational-in-agda
FromDec : ∀ {A : Set} → Dec A → Set
FromDec {A = A} (yes _) = A
FromDec         (no _) = ⊤

fromDec : ∀ {A : Set} (d : Dec A) → FromDec d
fromDec (yes p) = p
fromDec (no _) = _
