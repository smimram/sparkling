module Interval where

open import Program

data Interval : (P : Prog) → Set where
  CC : {P : Prog} → Pos P → Pos P → Interval P
  OC : {P : Prog} → Pos P → Pos P → Interval P
  CO : {P : Prog} → Pos P → Pos P → Interval P
  OO : {P : Prog} → Pos P → Pos P → Interval P
