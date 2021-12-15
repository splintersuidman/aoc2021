{-# OPTIONS --guardedness #-}

module Main where

open import Data.Fin as Fin
open import Data.List as List
open import Relation.Nullary using (yes; no)
open import Data.Maybe as Maybe using (Maybe; nothing; just)
open import Data.Nat as ℕ hiding (_⊔_)
open import Data.Nat.Show as ℕ
open import Data.Product as ×
open import Data.String as String
open import Data.Unit as ⊤
open import Data.Vec as Vec using (Vec; []; _∷_)
open import Function
open import IO
open import Level
open import System.Environment

open import Base
import Day01
import Day02
import Day03
import Day04
import Day05

∃′ : ∀ {a} {b} {A : Set a} → ({A} → Set b) → Set (a ⊔ b)
∃′ f = Σ _ (λ x → f {x})

solutions : Vec (∃′ Solution) _
solutions
  = (0ℓ , Day01.solution)
  ∷ (0ℓ , Day02.solution)
  ∷ (0ℓ , Day03.solution)
  ∷ (0ℓ , Day04.solution)
  ∷ (0ℓ , Day05.solution)
  ∷ []

readMaybeDay : String → Maybe (Fin _)
readMaybeDay str with ℕ.readMaybe 10 str
... | nothing = nothing
... | just zero = nothing
... | just (suc d) with d ℕ.<? Vec.length solutions
...   | yes pr = just $ fromℕ< pr
...   | no ¬pr = nothing

main = run $ getArgs >>= λ
  { (day ∷ filename ∷ []) → case readMaybeDay day of λ
    { (just d) → solveFile (proj₂ $ Vec.lookup solutions d) (ℕ.suc $ Fin.toℕ d) filename
    ; nothing → do
        putStrLn $
          "Incorrect day; maximum can be " String.++ ℕ.show (Vec.length solutions)
        pure tt
    }
  ; _ → do
      putStrLn "Usage ./Main <day> <filename>"
      pure tt
  }
