module Parallel where

open import Program
open import Interval

data PProg : Set where
  Thread : Prog → PProg
  Par : PProg → PProg → PProg

data PInterval : PProg → Set where
  Thread : {P : Prog} → Interval P → PInterval (Thread P)
  Par : {P Q : PProg} → PInterval P → PInterval Q → PInterval (Par P Q)
