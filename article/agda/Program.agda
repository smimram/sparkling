module Program where

open import Data.Nat.Base

data Prog : Set where
  Act : Prog
  Seq : Prog → Prog → Prog
  If : Prog → Prog → Prog
  Par : Prog → Prog → Prog
  While : Prog → Prog

data Pos : Prog → Set where
  Bot : (P : Prog) → Pos P
  Top : (P : Prog) → Pos P
  Seqₗ : {P : Prog} → Pos P → (Q : Prog) → Pos (Seq P Q)
  Seqᵣ : (P : Prog) → {Q : Prog} → Pos Q → Pos (Seq P Q)
  Ifₗ : {P : Prog} → Pos P → (Q : Prog) → Pos (If P Q)
  Ifᵣ : (P : Prog) → {Q : Prog} → Pos Q → Pos (If P Q)
  Par : {P Q : Prog} → Pos P → Pos Q → Pos (Par P Q)
  While : {P : Prog} → ℕ → Pos P → Pos (While P)

data _↝_ : {P : Prog} (p : Pos P) (q : Pos P) → Set where
  ↝-Act : Bot Act ↝ Top Act
  ↝-Seq₀ : (P Q : Prog) → Bot (Seq P Q) ↝ Seqₗ (Bot P) Q
  ↝-Seqₗ : {P : Prog} {p p' : Pos P} → (p ↝ p') → (Q : Prog) → Seqₗ p Q ↝ Seqₗ p' Q
  ↝-Seqₘ : (P Q : Prog) → Seqₗ (Top P) Q ↝ Seqᵣ P (Bot Q)
  ↝-Seqᵣ : (P : Prog) {Q : Prog} {q q' : Pos Q} → (q ↝ q') → Seqᵣ P q ↝ Seqᵣ P q'
  ↝-Seq₁ : (P Q : Prog) → Seqᵣ P (Top Q) ↝ Top (Seq P Q)
  ↝-If₀ₗ : (P Q : Prog) → Bot (If P Q) ↝ Ifₗ (Bot P) Q
  ↝-Ifₗ : {P : Prog} {p p' : Pos P} → p ↝ p' → (Q : Prog) → Ifₗ p Q ↝ Ifₗ p' Q
  ↝-If₁ₗ : (P Q : Prog) → Ifₗ (Top P) Q ↝ Top (If P Q)
  ↝-If₀ᵣ : (P Q : Prog) → Bot (If P Q) ↝ Ifᵣ P (Bot Q)
  ↝-Ifᵣ : (P : Prog) {Q : Prog} {q q' : Pos Q} → q ↝ q' → Ifᵣ P q ↝ Ifᵣ P q'
  ↝-If₁ᵣ : (P Q : Prog) → Ifᵣ P (Top Q) ↝ Top (If P Q)
  ↝-Par₀ : (P Q : Prog) → Bot (Par P Q) ↝ Par (Bot P) (Bot Q)
  ↝-Parₗ : {P Q : Prog} {p p' : Pos P} → p ↝ p' → (q : Pos Q) → Par p q ↝ Par p' q
  ↝-Parᵣ : {P Q : Prog} (p : Pos P) {q q' : Pos Q} → q ↝ q' → Par p q ↝ Par p q'
  ↝-Par₁ : (P Q : Prog) → Par (Top P) (Top Q) ↝ Top (Par P Q)
  ↝-While₀ : (P : Prog) → Bot (While P) ↝ While zero (Bot P)
  ↝-While₀' : (P : Prog) → Bot (While P) ↝ Top (While P)
  ↝-While : {P : Prog} {p p' : Pos P} (n : ℕ) → (p ↝ p') → While n p ↝ While n p'
  ↝-While₁ : (P : Prog) → (n : ℕ) → While n (Top P) ↝ Top (While P)
