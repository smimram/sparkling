open import Data.Product

data Prog : Set where
  PAct : Prog
  PSeq : Prog → Prog → Prog

data State : Set where
  SAct : State
  SSeq : State → State → State
  SSeqₗ : State → State → State
  SSeqᵣ : State → State
  SDone : State

prog-to-state : Prog → State
prog-to-state PAct = SAct
prog-to-state (PSeq P Q) = SSeq (prog-to-state P) (prog-to-state Q)

data _↝_ : (P : State) (Q : State) → Set where
  ↝-Act : SAct ↝ SDone
  ↝-Seq-b : (P Q : State) → SSeq P Q ↝ SSeqₗ P Q
  ↝-Seq-l : {P P' : State} (_ : P ↝ P') (Q : State) → SSeqₗ P Q ↝ SSeqₗ P' Q
  ↝-Seq-lr : (Q : State) → SSeqₗ SDone Q ↝ SSeqᵣ Q
  ↝-Seq-r : {Q Q' : State} (_ : Q ↝ Q') → SSeqᵣ Q ↝ SSeqᵣ Q'
  ↝-Seq-e : SSeqᵣ SDone ↝ SDone

data _≤_ : (P : State) (Q : State) → Set where

-- data State-path : (P : State) (Q : State) → Set where
  -- State-path-empty : (P : State) → State-path P P
  -- State-path-cons : {P Q R : State} (_ : P ↝ Q) (_ : State-path Q R) → State-path P R

-- data PState (P : Prog) : (S : State) → Set where
  -- PS-prog : PState P (prog-to-state P)
  -- PS-red : {S S' : State} (_ : PState P S) (_ : S ↝ S') → PState P S'

-- Interval (P : Prog) : Set
-- Interval P = PState P × State P

-- meet : (I : Interval) (J : Interval) → Interval
-- meet I J = {!!}
