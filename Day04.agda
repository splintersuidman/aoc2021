{-# OPTIONS --guardedness #-}

module Day04 where

open import Data.Bool as Bool
open import Data.List as List using (List; []; _∷_)
open import Data.List.NonEmpty as List⁺ using (List⁺)
open import Data.Maybe as Maybe using (Maybe; nothing; just)
open import Data.Nat as ℕ
open import Data.Nat.Show as ℕ
open import Data.Product as × using (_×_; _,_; proj₁; proj₂; uncurry)
open import Data.String as String using (String)
open import Relation.Nullary using (does; no; yes)
open import Data.Vec as Vec using (Vec; []; _∷_)
open import Function
open import Level as Level

open import Base
open import Util

record Board : Set where
  constructor mkBoard
  field
    board : Vec (Vec (ℕ × Bool) 5) 5

  won? : Bool
  won? = does (any? (all? (T? ∘ proj₂)) board)
       ∨ does (any? (all? (T? ∘ proj₂)) (Vec.transpose board))
    where
      open import Data.Vec.Relation.Unary.All using (all?)
      open import Data.Vec.Relation.Unary.Any using (any?)

open Board

score : Board → ℕ
score =
    List.sum
  ∘ List.map proj₁
  ∘ List.filter (Bool._≟_ false ∘ proj₂)
  ∘ Vec.toList
  ∘ Vec.concat
  ∘ board

map : (ℕ → Bool → ℕ × Bool) → Board → Board
map f = mkBoard ∘ Vec.map (Vec.map λ{ (n , m) → f n m }) ∘ board

set : Bool → ℕ → Board → Board
set m n = map λ k m′ → if n ℕ.≡ᵇ k then (k , m) else (k , m′)

mark : ℕ → Board → Board
mark = set true

unmark : ℕ → Board → Board
unmark = set false

module _ where
  open import Text.Parser 0ℓ
  open import Relation.Unary

  drawsₚ : ∀[ Parser [ List ℕ ] ]
  drawsₚ = List⁺.toList <$> list⁺ (decimalℕ <&? box (char ',') <|> decimalℕ)

  boardₚ : ∀[ Parser [ Board ] ]
  boardₚ = mkBoard ∘ Vec.map (Vec.map (_, false))
    <$> replicate 5 (replicate 5 (spaces ?&> decimalℕ <&? box spaces))

  boardsₚ : ∀[ Parser [ List Board ] ]
  boardsₚ = List⁺.toList <$> list⁺ boardₚ

  parser : ∀[ Parser [ List ℕ × List Board ] ]
  parser = _,_ <$> drawsₚ <*> box boardsₚ

solve₁′ : List ℕ → List Board → Maybe ℕ
solve₁′ [] boards = nothing
solve₁′ (draw ∷ draws) boards =
  let
    boards′ = List.map (mark draw) boards
  in case any? (T? ∘ won?) boards′ of λ
    { (no _) → solve₁′ draws boards′
    ; (yes any) → just $ draw * score (lookup any)
    }
  where
    open import Data.List.Relation.Unary.Any using (any?; lookup)

solve₁ : List ℕ × List Board → Maybe ℕ
solve₁ = uncurry solve₁′

solve₂′ : List ℕ → List Board → Maybe ℕ
solve₂′ [] boards = nothing
solve₂′ (draw ∷ draws) boards =
  let
    boards′ = List.map (unmark draw) boards
  in case any? (Bool._≟_ false ∘ won?) boards′ of λ
    { (no _) → solve₂′ draws boards′
    ; (yes any) → just $ draw * score (mark draw $ lookup any)
    }
  where
    open import Data.List.Relation.Unary.Any using (any?; lookup)

solve₂ : List ℕ × List Board → Maybe ℕ
solve₂ (draws , boards) =
  let
    final : List Board
    final = List.map (λ b → List.foldr mark b draws) boards

    winning : List Board
    winning = List.filter (T? ∘ won?) final
  in solve₂′ (List.reverse draws) winning

solution : Solution
solution = record
  { parse = runParserMaybe parser
  ; solve₁ = Maybe.maybe (Maybe.fromMaybe "No solution" ∘ Maybe.map ℕ.show ∘ solve₁) "No parse"
  ; solve₂ = Maybe.maybe (Maybe.fromMaybe "No solution" ∘ Maybe.map ℕ.show ∘ solve₂) "No parse"
  }
