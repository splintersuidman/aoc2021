{-# OPTIONS --guardedness #-}

module Day05 where

open import Data.Bool as Bool
open import Data.List as List using (List; []; _∷_)
open import Data.List.NonEmpty as List⁺ using (List⁺)
import Data.List.Sort as List
open import Data.Maybe as Maybe using (Maybe; nothing; just)
open import Data.Nat as ℕ
import Data.Nat.Properties as ℕ
open import Data.Nat.Show as ℕ
open import Data.Product as × using (_×_; _,_; proj₁; proj₂; uncurry)
import Data.Product.Properties as ×
import Data.Product.Relation.Binary.Lex.NonStrict as ×
open import Data.String as String using (String)
open import Data.Unit as ⊤
open import Data.Vec as Vec using (Vec; []; _∷_)
open import Function
open import Level as Level
open import Relation.Nullary using (does; no; yes)

open import Base
open import Util

Point : Set
Point = ℕ × ℕ

Line : Set
Line = Point × Point

module Parser where
  open import Text.Parser 0ℓ
  open import Relation.Unary

  point : ∀[ Parser [ Point ] ]
  point = _,_ <$> decimalℕ <*> box (char ',' &> box decimalℕ)

  arrow : ∀[ Parser [ ⊤ ] ]
  arrow = tt <$ (spaces ?&> text "->" <&? box spaces)

  line : ∀[ Parser [ Line ] ]
  line = _,_ <$> point <*> box (arrow &> box point)

  parser : ∀[ Parser [ List Line ] ]
  parser = List⁺.toList <$> list⁺ (spaces ?&> line <&? box spaces)

open Parser using (parser)

horizontalOrVertical : Line → Bool
horizontalOrVertical ((x₁ , y₁) , (x₂ , y₂)) = (x₁ ≡ᵇ x₂) ∨ (y₁ ≡ᵇ y₂)

between : ℕ → ℕ → List ℕ
between x y = if x ≤ᵇ y
  then List.map (x +_) (List.upTo (1 + y ∸ x))
  else (List.reverse $ List.map (y +_) (List.upTo (1 + x ∸ y)))

-- Points on a horizontal or vertical line
pointsₕᵥ : Line → List Point
pointsₕᵥ ((x₁ , y₁) , (x₂ , y₂)) = List.cartesianProduct (between x₁ x₂) (between y₁ y₂)

module _ {a} {A : Set a} where
  open import Relation.Binary using (Rel; Decidable)

  runLengthEncode : ∀ {ℓ} {R : Rel A ℓ} → Decidable R → List A → List (ℕ × A)
  runLengthEncode R? [] = []
  runLengthEncode R? (x ∷ xs) with runLengthEncode R? xs
  ... | [] = (1 , x) ∷ []
  ... | (n , y) ∷ ys with does (R? x y)
  ...   | false = (1 , x) ∷ (n , y) ∷ ys
  ...   | true = (1 + n , x) ∷ ys

solve₁ : List Line → ℕ
solve₁ =
    List.length
  ∘ List.filter ((1 ℕ.<?_) ∘ proj₁)
  ∘ runLengthEncode (×.≡-dec ℕ._≟_ ℕ._≟_)
  ∘ List.sort (×.×-decTotalOrder ℕ.≤-decTotalOrder ℕ.≤-decTotalOrder)
  ∘ List.concatMap pointsₕᵥ
  ∘ List.filter (T? ∘ horizontalOrVertical)

-- Points on a horizontal, vertical or diagonal line
points : Line → List Point
points ((x₁ , y₁) , (x₂ , y₂)) =
  if does (x₁ ℕ.≟ x₂) then
    List.map (x₁ ,_) (between y₁ y₂)
  else if does (y₁ ℕ.≟ y₂) then
    List.map (_, y₁) (between x₁ x₂)
  else
    List.zip (between x₁ x₂) (between y₁ y₂)

solve₂ : List Line → ℕ
solve₂ =
    List.length
  ∘ List.filter ((1 ℕ.<?_) ∘ proj₁)
  ∘ runLengthEncode (×.≡-dec ℕ._≟_ ℕ._≟_)
  ∘ List.sort (×.×-decTotalOrder ℕ.≤-decTotalOrder ℕ.≤-decTotalOrder)
  ∘ List.concatMap points

solution : Solution
solution = record
  { parse = runParserMaybe parser
  ; solve₁ = Maybe.maybe (ℕ.show ∘ solve₁) "No parse"
  ; solve₂ = Maybe.maybe (ℕ.show ∘ solve₂) "No parse"
  }
