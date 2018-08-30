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
