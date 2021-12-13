{-# OPTIONS --without-K --guardedness #-}

module Day01 where

open import Data.Bool as Bool
open import Data.List as List
open import Data.Maybe as Maybe using (Maybe; nothing; just)
open import Data.Nat as ℕ
open import Data.Nat.Show as ℕ
open import Data.Product as ×
open import Data.String as String
open import Data.Unit as ⊤
open import Function
open import IO
open import Level as Level

private
  variable
    a b c d : Level
    A : Set a
    B : Set b
    C : Set c
    D : Set d

catMaybes : List (Maybe A) → List A
catMaybes [] = []
catMaybes (just x ∷ xs) = x ∷ catMaybes xs
catMaybes (nothing ∷ xs) = catMaybes xs

solve₁ : List ℕ → ℕ
solve₁ ds = sum $
  List.zipWith (λ d d′ → if d <ᵇ d′ then 1 else 0) ds (drop 1 ds)

-- zip₃ : List A → List B → List C → List (A × B × C)
-- zip₃ xs ys zs = List.zip xs (List.zip ys zs)

zipWith₃ : (A → B → C → D) → List A → List B → List C → List D
zipWith₃ f xs ys zs = zipWith (flip _$_) zs (zipWith f xs ys)

solve₂ : List ℕ → ℕ
solve₂ ds = solve₁ $
  zipWith₃ (λ d₁ d₂ d₃ → d₁ + d₂ + d₃) ds (drop 1 ds) (drop 2 ds)

main = run $ do
  input ← catMaybes ∘ List.map (readMaybe 10) ∘ lines
    <$> readFiniteFile "input01"
  putStrLn $ ℕ.show $ solve₁ input
  putStrLn $ ℕ.show $ solve₂ input
  pure tt
