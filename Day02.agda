{-# OPTIONS --guardedness #-}

module Day02 where

open import Data.Bool as Bool
open import Data.Integer as ℤ hiding (show)
open import Data.Integer.Show renaming (show to showℤ)
open import Data.List as List using (List; []; _∷_)
open import Data.List.NonEmpty as List⁺ using (List⁺)
open import Data.Maybe as Maybe using (Maybe; nothing; just)
open import Data.Nat as ℕ using (ℕ)
open import Data.Nat.Show as ℕ
open import Data.Product as ×
open import Data.String as String
open import Data.Sum as ⊎ using (_⊎_; inj₁; inj₂)
open import Data.Unit as ⊤
open import Function
open import Level as Level

open import Base
open import Util

data Command : Set where
  forward : ℕ → Command
  down    : ℕ → Command
  up      : ℕ → Command

module _ where
  open import Text.Parser 0ℓ
  open import Relation.Unary

  parseCommand : ∀[ Parser [ Command ] ]
  parseCommand =
    let
      parseForward = text "forward" ?&> spaces ?&> forward <$> decimalℕ
      parseUp      = text "up"      ?&> spaces ?&> up      <$> decimalℕ
      parseDown    = text "down"    ?&> spaces ?&> down    <$> decimalℕ
    in parseForward <|> parseUp <|> parseDown

  parseCommands : ∀[ Parser [ List Command ] ]
  parseCommands = List⁺.toList <$> list⁺ (spaces ?&> parseCommand <&? box spaces)

command₁ : Command → ℤ × ℤ → ℤ × ℤ
command₁ (forward z) (x , y) = (x + (+ z) , y)
command₁ (down z) (x , y) = (x , y + (+ z))
command₁ (up z) (x , y) = (x , y - (+ z))

solve₁ : List Command → ℤ
solve₁ = uncurry _*_ ∘ List.foldr command₁ (+ 0 , + 0)

command₂ : ℤ × ℤ × ℤ → Command → ℤ × ℤ × ℤ
command₂ (x , y , a) (down z) = (x , y , a + (+ z))
command₂ (x , y , a) (up z) = (x , y , a - (+ z))
command₂ (x , y , a) (forward z) = (x + (+ z) , y + a * (+ z) , a)

solve₂ : List Command → ℤ
solve₂ = (λ (x , y , a) → x * y) ∘ List.foldl command₂ (+ 0 , + 0 , + 0)

solution : Solution
solution = record
  { parse = runParserMaybe parseCommands
  ; solve₁ = Maybe.maybe (showℤ ∘ solve₂) "No parse"
  ; solve₂ = Maybe.maybe (showℤ ∘ solve₂) "No parse"
  }
