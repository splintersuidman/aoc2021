{-# OPTIONS --guardedness #-}

module Util where

open import Data.List as List using (List; []; _∷_)
open import Data.Maybe as Maybe using (Maybe; nothing; just)
open import Data.String as String using (String)
open import Data.Sum as ⊎ using (_⊎_; inj₁; inj₂)
open import Function
open import Level as Level

private
  variable
    a : Level
    A : Set a

catMaybes : List (Maybe A) → List A
catMaybes [] = []
catMaybes (just x ∷ xs) = x ∷ catMaybes xs
catMaybes (nothing ∷ xs) = catMaybes xs

module _ {A : Set} where
  open import Text.Parser 0ℓ
  open import Relation.Unary

  runParserMaybe : ∀[ Parser [ A ] ] → String → Maybe A
  runParserMaybe parser input = case runParser parser input of λ
    { (inj₁ _) → nothing
    ; (inj₂ result) → just result
    }
