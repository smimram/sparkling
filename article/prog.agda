open import Data.Product

data Prog : Set where
  PAct : Prog
  PSeq : Prog → Prog → Prog

-- Pos ?
data State : Prog → Set where
  SBot : (P : Prog) → State P
  STop : (P : Prog) → State P
  SSeqₗ : {P : Prog} → State P → (Q : Prog) → State (PSeq P Q)
  SSeqᵣ : (P : Prog) → {Q : Prog} → State Q → State (PSeq P Q)

data _↝_ : {P : Prog} (p : State P) (q : State P) → Set where
  ↝-Act : SBot PAct ↝ STop PAct
  ↝-Seq-b : (P Q : Prog) → SBot (PSeq P Q) ↝ SSeqₗ (SBot P) Q
  ↝-Seq-l : {P : Prog} {p p' : State P} (_ : p ↝ p') (Q : Prog) → SSeqₗ p Q ↝ SSeqₗ p' Q
  ↝-Seq-lr : (P Q : Prog) → SSeqₗ (STop P) Q ↝ SSeqᵣ P (SBot Q)
  ↝-Seq-r : (P : Prog) {Q : Prog} {q q' : State Q} (_ : q ↝ q') → SSeqᵣ P q ↝ SSeqᵣ P q'
  ↝-Seq-e : (P Q : Prog) → SSeqᵣ P (STop Q) ↝ STop (PSeq P Q)

data _≤_ : {P : Prog} (p q : State P) → Set where
  ≤-refl : (SBot PAct) ≤ (SBot PAct)
  ≤-botop : {P : Prog} → (SBot P) ≤ (STop P)
  -- ≤-Seq : {P Q : Prog} {p p' : State P} {q q' : State Q} (_ : p ≤ p') (_ : q ≤ q') → S

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
