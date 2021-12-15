{-# OPTIONS --guardedness #-}

module Day06 where

open import Data.Bool as Bool
open import Data.Fin as Fin using (#_)
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
open import Data.Vec as Vec using (Vec; []; _∷_; _∷ʳ_; _[_]%=_)
open import Function
open import Level as Level
open import Relation.Nullary using (does; no; yes)

open import Base
open import Util

private
  variable
    a : Level
    A : Set a

repeat : ℕ → (A → A) → A → A
repeat ℕ.zero f x = x
repeat (ℕ.suc n) f x = f (repeat n f x)

init : List ℕ → Vec ℕ 9
init = List.foldr count (Vec.replicate 0)
  where
    count : ℕ → Vec ℕ 9 → Vec ℕ 9
    count n fs with n ℕ.<? 9
    ... | yes n<9 = fs [ Fin.fromℕ< n<9 ]%= (1 +_)
    ... | no n≥9 = fs

update : Vec ℕ 9 → Vec ℕ 9
update (zeros ∷ fs) = (fs ∷ʳ zeros) [ # 6 ]%= (zeros +_)

solve₁ : List ℕ → ℕ
solve₁ = Vec.sum ∘ repeat 80 update ∘ init

solve₂ : List ℕ → ℕ
solve₂ = Vec.sum ∘ repeat 256 update ∘ init

solution : Solution
solution = record
  { parse = runParserMaybe $
      List⁺.toList <$> (spaces ?&> list⁺ (decimalℕ <&? box (char ',') <|> decimalℕ) <&? box spaces)
  ; solve₁ = Maybe.maybe (ℕ.show ∘ solve₁) "No parse"
  ; solve₂ = Maybe.maybe (ℕ.show ∘ solve₂) "No parse"
  } where
    open import Text.Parser 0ℓ
