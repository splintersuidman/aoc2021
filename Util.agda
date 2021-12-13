{-# OPTIONS --without-K --guardedness #-}

module Util where

open import Data.List as List
open import Data.Maybe as Maybe using (Maybe; nothing; just)
open import Level as Level

private
  variable
    a : Level
    A : Set a

catMaybes : List (Maybe A) → List A
catMaybes [] = []
catMaybes (just x ∷ xs) = x ∷ catMaybes xs
catMaybes (nothing ∷ xs) = catMaybes xs
