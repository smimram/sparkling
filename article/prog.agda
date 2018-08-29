data Prog : Set where
  PAct : Prog
  PSeq : Prog → Prog → Prog

data State : Set where
  SAct : State
  SSeq : State → State → State
  SDone : State

prog-to-state : Prog → State
prog-to-state PAct = SAct
prog-to-state (PSeq P Q) = SSeq (prog-to-state P) (prog-to-state Q)

data _↝_ : (P : State) (Q : State) → Set where
  ↝-Act : SAct ↝ SDone
  ↝-Seq-l : {P P' : State} (_ : P ↝ P') (Q : State) → SSeq P Q ↝ SSeq P' Q
  ↝-Seq-r : {Q Q' : State} (_ : Q ↝ Q') → SSeq SDone Q ↝ SSeq SDone Q'

