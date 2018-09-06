open import Data.Product

data Prog : Set where
  Act : Prog
  Seq : Prog → Prog → Prog

data Pos : Prog → Set where
  Bot : (P : Prog) → Pos P
  Top : (P : Prog) → Pos P
  Seqₗ : {P : Prog} → Pos P → (Q : Prog) → Pos (Seq P Q)
  Seqᵣ : (P : Prog) → {Q : Prog} → Pos Q → Pos (Seq P Q)

data _↝_ : {P : Prog} (p : Pos P) (q : Pos P) → Set where
  ↝-Act : Bot Act ↝ Top Act
  ↝-Seq-b : (P Q : Prog) → Bot (Seq P Q) ↝ Seqₗ (Bot P) Q
  ↝-Seq-l : {P : Prog} {p p' : Pos P} → (p ↝ p') → (Q : Prog) → Seqₗ p Q ↝ Seqₗ p' Q
  ↝-Seq-lr : (P Q : Prog) → Seqₗ (Top P) Q ↝ Seqᵣ P (Bot Q)
  ↝-Seq-r : (P : Prog) {Q : Prog} {q q' : Pos Q} → (q ↝ q') → Seqᵣ P q ↝ Seqᵣ P q'
  ↝-Seq-e : (P Q : Prog) → Seqᵣ P (Top Q) ↝ Top (Seq P Q)

data _≤_ : {P : Prog} (p q : Pos P) → Set where
  ≤-refl : {P : Prog} (p : Pos P) → p ≤ p
  ≤-trans : {P : Prog} (p q r : Pos P) → (p ≤ q) → (q ≤ r) → (p ≤ r)
  ≤-botop : {P : Prog} → (Bot P) ≤ (Top P)
  ≤-Seqₗ : {P : Prog} {p p' : Pos P} → (p ≤ p') → (Q : Prog) → Seqₗ p Q ≤ Seqₗ p' Q
  ≤-Seqᵣ : (P : Prog) {Q : Prog} {q q' : Pos Q} → (q ≤ q') → Seqᵣ P q ≤ Seqᵣ P q'
