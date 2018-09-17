module LowerComplement where

open import Function using ( case_of_ )
open import Relation.Binary.PropositionalEquality
open import Data.Empty
open import Data.Sum
open import Data.Product

open import Logic
open import Program
open import Order

data _¬>_ : {P : Prog} (p q : Pos P) → Set where
  ¬>-Bot : {P : Prog} → (Bot P) ¬> (Bot P)
  ¬>-Top : {P : Prog} → (Top P) ¬> (Top P)
  ¬>-Seqₗ : {P : Prog} {p p' : Pos P} → (p ¬> p') → (Q : Prog) → Seqₗ p Q ¬> Seqₗ p' Q
  ¬>-Seqᵣ : (P : Prog) {Q : Prog} {q q' : Pos Q} → (q ¬> q') → Seqᵣ P q ¬> Seqᵣ P q'
  ¬>-Ifₗ : {P : Prog} {p p' : Pos P} → (p ¬> p') → (Q : Prog) → Ifₗ p Q ¬> Ifₗ p' Q
  ¬>-Ifₗ' : {P : Prog} (p : Pos P) (Q : Prog) → Ifᵣ P (Top Q) ¬> Ifₗ p Q
  ¬>-Ifᵣ : (P : Prog) {Q : Prog} (q q' : Pos Q) → (q ¬> q') → Ifᵣ P q ¬> Ifᵣ P q'
  ¬>-Parₗ : {P : Prog} {p p' : Pos P} → (p ¬> p') → {Q : Prog} (q : Pos Q) → Par p (Top Q) ¬> Par p' q
  ¬>-Parᵣ : {P : Prog} (p : Pos P) {Q : Prog} {q q' : Pos Q} → (q ¬> q') → Par (Top P) q ¬> Par p q'
  ¬>-While : {P : Prog} (n : ℕ) {p p' : Pos P} → (p ¬> p') → While (n , p) ¬> While (n , p')

¬>-refl : {P : Prog} (p : Pos P) → p ¬> p
¬>-refl (Bot P) = ¬>-Bot
¬>-refl (Top P) = ¬>-Top
¬>-refl (Seqₗ p Q) = ¬>-Seqₗ (¬>-refl p) Q
¬>-refl (Seqᵣ P q) = ¬>-Seqᵣ P (¬>-refl q)
¬>-refl (Ifₗ p Q) = {!!}
¬>-refl (Ifᵣ P p) = {!!}
¬>-refl (Par p p₁) = {!!}
¬>-refl (While x) = {!!}

-- ¬>-sound : {P : Prog} {x : Pos P} {p q : Pos P} → (p ¬> q) → (x ≤ p) → (q ≤ x) → x ≡ q
-- ¬>-sound ¬>-Bot l l' = ≤-asym l l'
-- ¬>-sound ¬>-Top l l' = ≤-asym l l'
-- ¬>-sound (¬>-Seqₗ {p' = p'} r Q) (≤-step (↝-Seq₀ P .Q) l) l' = ⊥-elim (¬≤-Seqₗ-Bot l')
-- ¬>-sound (¬>-Seqₗ r Q) (≤-step (↝-Seqₗ s .Q) l) l' = cong (λ p → Seqₗ p Q) (¬>-sound r (≤-step s (≤-Seqₗ' l)) (≤-Seqₗ' l'))
-- ¬>-sound (¬>-Seqₗ r Q) (≤-step (↝-Seqₘ P .Q) l) l' =  ⊥-elim (¬≤-Seqᵣ-Seqₗ l)
-- ¬>-sound (¬>-Seqₗ r Q) (≤-step (↝-Seqᵣ P s) l) l' = ⊥-elim (¬≤-Seqᵣ-Seqₗ l)
-- ¬>-sound (¬>-Seqₗ r Q) (≤-step (↝-Seq₁ P .Q) l) l' = ⊥-elim (¬≤-Top-Seqₗ l)
-- ¬>-sound (¬>-Seqₗ {p = p} r Q) (≤-refl .(Seqₗ _ Q)) l' = cong (λ p → Seqₗ p Q) (¬>-sound r (≤-refl p) (≤-Seqₗ' l'))
-- ¬>-sound (¬>-Seqᵣ P r) (≤-step (↝-Seq₀ .P _) l) l' = ⊥-elim (¬≤-Seqᵣ-Bot l')
-- ¬>-sound (¬>-Seqᵣ P r) (≤-step (↝-Seqₗ s _) l) l' = ⊥-elim (¬≤-Seqᵣ-Seqₗ l')
-- ¬>-sound (¬>-Seqᵣ P r) (≤-step (↝-Seqₘ .P _) l) l' = ⊥-elim (¬≤-Seqᵣ-Seqₗ l')
-- ¬>-sound (¬>-Seqᵣ P r) (≤-step (↝-Seqᵣ .P s) l) l' = cong (λ q → Seqᵣ P q) (¬>-sound r (≤-step s (≤-Seqᵣ' l)) (≤-Seqᵣ' l'))
-- ¬>-sound (¬>-Seqᵣ P r) (≤-step (↝-Seq₁ .P _) l) l' = ⊥-elim (¬≤-Top-Seqᵣ l)
-- ¬>-sound (¬>-Seqᵣ P {q = q} r) (≤-refl .(Seqᵣ P _)) l' = cong (λ q → Seqᵣ P q) (¬>-sound r (≤-refl q) (≤-Seqᵣ' l'))

-- ¬>-complete : {P : Prog} (p : Pos P) (x : Pos P) → (p ≤ x) or (∃[ q ] ((q ¬> p) and (x ≤ q)))
-- ¬>-complete (Bot P) x = inj₁ (≤-Bot x)
-- ¬>-complete (Top P) x = inj₂ ( Top P , ¬>-Top , ≤-Top x )
-- ¬>-complete (Seqₗ p Q) (Bot .(Seq _ Q)) = inj₂ (Seqₗ p Q , ¬>-Seqₗ (¬>-refl p) Q , ≤-Bot (Seqₗ p Q))
-- ¬>-complete (Seqₗ p Q) (Top .(Seq _ Q)) = inj₁ (≤-Top (Seqₗ p Q))
-- ¬>-complete (Seqₗ p Q) (Seqₗ x .Q) = case ¬>-complete p x of λ { (inj₁ l) → inj₁ (≤-Seqₗ l Q) ; (inj₂ (q , n , l)) → inj₂ (Seqₗ q Q , ¬>-Seqₗ n Q , ≤-Seqₗ l Q) }
-- ¬>-complete (Seqₗ p Q) (Seqᵣ P x) = inj₁ (≤-Seqₗ-Seqᵣ p x)
-- ¬>-complete (Seqᵣ P p) (Bot .(Seq P _)) = inj₂ (Seqᵣ P p , ¬>-refl (Seqᵣ P p) , ≤-Bot (Seqᵣ P p))
-- ¬>-complete (Seqᵣ P p) (Top .(Seq P _)) = inj₁ (≤-Top (Seqᵣ P p))
-- ¬>-complete (Seqᵣ P p) (Seqₗ x Q) = inj₂ (Seqᵣ P p , ¬>-Seqᵣ P (¬>-refl p) , ≤-Seqₗ-Seqᵣ x p)
-- ¬>-complete (Seqᵣ P q) (Seqᵣ .P x) = case ¬>-complete q x of λ { (inj₁ l) → inj₁ (≤-Seqᵣ P l) ; (inj₂ (q , n , l)) → inj₂ (Seqᵣ P q , ¬>-Seqᵣ P n , ≤-Seqᵣ P l) }

