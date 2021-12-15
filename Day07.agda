{-# OPTIONS --guardedness #-}

-- Some comments about this solution:
--
-- Let c₁, …, cₙ ∈ ℕ be the positions of the crabs. In part 1, we are
-- looking for a x ∈ ℕ that minimises ∑ᵢ₌₀ⁿ |cᵢ-x|. It can be shown
-- that this minimum is assumed at the median of the positions cᵢ.
-- Since the number of positions is even, in solve₁ we try both ⌊n/2⌋
-- and ⌈n/2⌉.
--
-- In part 2, we are looking for a x ∈ ℕ that minimised ½∑ᵢ₌₀ (xᵢ-c)².
-- It is exactly the mean of the positions cᵢ that minimises this sum.
-- Because of rounding, again, we try both ⌊c̅⌋ and ⌈c̅⌉.

module Day07 where

open import Data.Bool as Bool
open import Data.Fin as Fin using (#_)
open import Data.List as List using (List; []; _∷_)
open import Data.List.NonEmpty as List⁺ using (List⁺)
import Data.List.Sort as List
open import Data.Maybe as Maybe using (Maybe; nothing; just)
open import Data.Nat as ℕ
open import Data.Nat.DivMod as ℕ
import Data.Nat.Properties as ℕ
open import Data.Nat.Show as ℕ
open import Data.Product as × using (_×_; _,_; proj₁; proj₂; uncurry)
import Data.Product.Properties as ×
import Data.Product.Relation.Binary.Lex.NonStrict as ×
open import Data.String as String using (String)
open import Data.Unit as ⊤
open import Data.Vec as Vec using (Vec; []; _∷_; _∷ʳ_; _[_]%=_)
open import Function
open import Level as Level
open import Relation.Nullary using (does; no; yes)

open import Base
open import Util

cost₁ : ℕ → List ℕ → ℕ
cost₁ x = List.sum ∘ List.map ∣ x -_∣

solve₁ : List⁺ ℕ → Maybe ℕ
solve₁ cs′ =
  let
    cs = List.sort ℕ.≤-decTotalOrder $ List⁺.toList cs′
  in case List.splitAt ⌊ List.length cs /2⌋ cs of λ
    { ([] , _) → nothing
    ; (_ ∷ _ , []) → nothing
    ; (l ∷ _ , r ∷ _) → just $ cost₁ l cs ⊓ cost₁ r cs
    }

-- NOTE: division here is very slow. _/ 2 is better than ⌊_/2⌋, but
-- still it takes ~40× longer than using cost₁. It is probably linear
-- in the size of the number, and the numbers are quite large.
cost₂ : ℕ → List ℕ → ℕ
cost₂ x = List.sum ∘ List.map fuel
  where
    fuel : ℕ → ℕ
    fuel cᵢ = let dist = ∣ x - cᵢ ∣ in (dist * (1 + dist)) / 2

solve₂ : List⁺ ℕ → ℕ
solve₂ cs′ =
  let
    n = List⁺.length cs′
    cs = List⁺.toList cs′
    c̅ = List.sum cs / n
  in cost₂ c̅ cs ⊓ cost₂ (1 + c̅) cs

solution : Solution
solution = record
  { parse = runParserMaybe $
      spaces ?&> list⁺ (decimalℕ <&? box (char ',') <|> decimalℕ) <&? box spaces
  ; solve₁ = Maybe.maybe (Maybe.fromMaybe "No solution" ∘ Maybe.map ℕ.show ∘ solve₁) "No parse"
  ; solve₂ = Maybe.maybe (ℕ.show ∘ solve₂) "No parse"
  } where
    open import Text.Parser 0ℓ
