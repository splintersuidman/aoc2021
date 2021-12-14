{-# OPTIONS --guardedness #-}

module Day03 where

open import Data.Bool as Bool
open import Data.Char as Char
open import Data.List as List using (List; []; _∷_)
open import Data.List.NonEmpty as List⁺ using (List⁺)
open import Data.Maybe as Maybe using (Maybe; nothing; just)
open import Data.Nat as ℕ
open import Data.Nat.Show as ℕ
open import Data.Product as ×
open import Data.String as String using (String)
open import Data.Unit as ⊤
open import Data.Vec as Vec using (Vec; []; _∷_)
open import Function
open import Level as Level

open import Base
open import Util

module _ where
  open import Text.Parser 0ℓ
  open import Relation.Unary

  bit : ∀[ Parser [ Bool ] ]
  bit =  false <$ char '0'
     <|> true <$ char '1'

  firstLine : ∀[ Parser [ List⁺ Bool ] ]
  firstLine = list⁺ bit

  line : (n : ℕ) → {NonZero n} → ∀[ Parser [ Vec Bool n ] ]
  line n {nonZero} = replicate n {nonZero} bit

  parser : ∀[ Parser [ ∃[ n ] (List (Vec Bool n)) ] ]
  parser = do
    first′ ← firstLine
    let
      n = List⁺.length first′
      first : Vec Bool n
      first = List⁺.toVec first′

      make : List⁺ (Vec Bool n) → ∃[ m ] (List (Vec Bool m))
      make xs = (n , first ∷ List⁺.toList xs)
    -- TODO: this list does not have to be non-empty.
    box $ make <$> list⁺ (spaces ?&> line n <&? box spaces)

count : {m n : ℕ} → Vec (Vec Bool m) n → Vec (ℕ × ℕ) n
count = Vec.map countCol
  where
    countBit : Bool → ℕ × ℕ → ℕ × ℕ
    countBit false (zeros , ones) = (1 + zeros , ones)
    countBit true (zeros , ones) = (zeros , 1 + ones)

    countCol : {m : ℕ} → Vec Bool m → ℕ × ℕ
    countCol = Vec.foldr (const $ ℕ × ℕ) countBit (0 , 0)

binaryToℕ : {n : ℕ} → Vec Bool n → ℕ
binaryToℕ = Vec.foldr (const ℕ) (λ b n → if b then 1 + 2 * n else 2 * n) 0 ∘ Vec.reverse

solve₁′ : {n : ℕ} → List (Vec Bool n) → ℕ
solve₁′ ns =
  let
    counts = count $ Vec.transpose $ Vec.fromList $ ns
    γ-bin = Vec.map choose-γ counts
    ε-bin = Vec.map not γ-bin
    γ = binaryToℕ γ-bin
    ε = binaryToℕ ε-bin
  in γ * ε
  where
    choose-γ : ℕ × ℕ → Bool
    choose-γ (zeros , ones) = if zeros ≤ᵇ ones then true else false

solve₁ : ∃[ n ] (List (Vec Bool n)) → ℕ
solve₁ (_ , xs) = solve₁′ xs

solution : Solution
solution = record
  { parse = runParserMaybe parser
  ; solve₁ = maybe (ℕ.show ∘ solve₁) "No parse"
    -- TODO
  ; solve₂ = const "Not solved yet"
  } where
  open import Data.Maybe
