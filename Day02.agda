{-# OPTIONS --without-K --guardedness #-}

module Day02 where

open import Data.Bool as Bool
open import Data.Integer as ℤ hiding (show)
open import Data.Integer.Show renaming (show to showℤ)
open import Data.List as List
open import Data.Maybe as Maybe using (Maybe; nothing; just)
open import Data.Nat as ℕ using (ℕ)
open import Data.Nat.Show as ℕ
open import Data.Product as ×
open import Data.String as String
open import Data.Unit as ⊤
open import Function
open import IO
open import Level as Level
open import Util

data Command : Set where
  forward : ℕ → Command
  down    : ℕ → Command
  up      : ℕ → Command

parse : List String → Maybe Command
parse ("forward" ∷ x ∷ []) = Maybe.map forward $ readMaybe 10 x
parse ("down"    ∷ x ∷ []) = Maybe.map down $ readMaybe 10 x
parse ("up"      ∷ x ∷ []) = Maybe.map up $ readMaybe 10 x
parse _                    = nothing

command₁ : Command → ℤ × ℤ → ℤ × ℤ
command₁ (forward z) (x , y) = (x + (+ z) , y)
command₁ (down z) (x , y) = (x , y + (+ z))
command₁ (up z) (x , y) = (x , y - (+ z))

solve₁ : List Command → ℤ
solve₁ = uncurry _*_ ∘ foldr command₁ (+ 0 , + 0)

command₂ : ℤ × ℤ × ℤ → Command → ℤ × ℤ × ℤ
command₂ (x , y , a) (down z) = (x , y , a + (+ z))
command₂ (x , y , a) (up z) = (x , y , a - (+ z))
command₂ (x , y , a) (forward z) = (x + (+ z) , y + a * (+ z) , a)

solve₂ : List Command → ℤ
solve₂ = (λ (x , y , a) → x * y) ∘ foldl command₂ (+ 0 , + 0 , + 0)

main = run $ do
  input ← catMaybes ∘ List.map (parse ∘ words) ∘ lines
    <$> readFiniteFile "input02"
  putStrLn $ showℤ $ solve₁ input
  putStrLn $ showℤ $ solve₂ input
  pure tt
