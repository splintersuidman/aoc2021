{-# OPTIONS --without-K --guardedness #-}

module Base where

open import Data.Nat as ℕ
open import Data.Nat.Show as ℕ
open import Data.Product as ×
open import Data.String as String
open import Data.Unit as ⊤
open import Function
open import IO
open import Level renaming (suc to lsuc)

record Solution {a} : Set (lsuc a) where
  field
    {A} : Set a
    parse : String → A
    solve₁ : A → String
    solve₂ : A → String

module _ {a} (solution : Solution {a}) where
  open Solution solution

  solve : String → String × String
  solve = < solve₁ , solve₂ > ∘ parse

  solveFile : ℕ → String → IO ⊤
  solveFile n filename = do
    (sol₁ , sol₂) ← solve <$> readFiniteFile filename
    putStrLn $ "Day " ++ ℕ.show n ++ ", part 1:"
    putStrLn sol₁
    putStrLn $ "Day " ++ ℕ.show n ++ ", part 2:"
    putStrLn sol₂
    pure tt
