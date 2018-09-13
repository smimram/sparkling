module Order where

open import Equality
open import Relation.Binary.PropositionalEquality
open import Data.Nat.Base renaming (_≤_ to _≤ℕ_) hiding (_≥_)
open import Program

data _≤_ : {P : Prog} (p : Pos P) (q : Pos P) → Set where
  ≤-step : {P : Prog} {p q r : Pos P} → (p ↝ q) → (q ≤ r) → p ≤ r
  ≤-refl : {P : Prog} (p : Pos P) → p ≤ p

≡-≤ : {P : Prog} {p q : Pos P} → (p ≡ q) → p ≤ q
≡-≤ {P} {p} {q} l = transport (λ q → p ≤ q) l (≤-refl p)

≤-trans : {P : Prog} {p q r : Pos P} → (p ≤ q) → (q ≤ r) → (p ≤ r)
≤-trans (≤-step r l) l' = ≤-step r (≤-trans l l')
≤-trans (≤-refl p) l' = l'

≤-step1 : {P : Prog} {p q : Pos P} → (p ↝ q) → (p ≤ q)
≤-step1 {_} {_} {q} r = ≤-step r (≤-refl q)

_≥_ : {P : Prog} (p : Pos P) (q : Pos P) → Set
p ≥ q = q ≤ p

≤-Seqₗ : {P : Prog} {p p' : Pos P} (l : p ≤ p') (Q : Prog) → Seqₗ p Q ≤ Seqₗ p' Q
≤-Seqₗ (≤-step s l) Q = ≤-step (↝-Seqₗ s Q) (≤-Seqₗ l Q)
≤-Seqₗ (≤-refl p) Q = ≤-refl (Seqₗ p Q)

≤-Seqᵣ : (P : Prog) {Q : Prog} {q q' : Pos Q} (l : q ≤ q') → Seqᵣ P q ≤ Seqᵣ P q'
≤-Seqᵣ P (≤-step r l) = ≤-step (↝-Seqᵣ P r) (≤-Seqᵣ P l)
≤-Seqᵣ P (≤-refl p) = ≤-refl (Seqᵣ P p)

≤-Ifₗ : {P : Prog} {p p' : Pos P} (l : p ≤ p') (Q : Prog) → Ifₗ p Q ≤ Ifₗ p' Q
≤-Ifₗ (≤-step s l) Q = ≤-step (↝-Ifₗ s Q) (≤-Ifₗ l Q)
≤-Ifₗ (≤-refl p) Q = ≤-refl (Ifₗ p Q)

≤-Ifᵣ : (P : Prog) {Q : Prog} {q q' : Pos Q} (l : q ≤ q') → Ifᵣ P q ≤ Ifᵣ P q'
≤-Ifᵣ P (≤-step s l) = ≤-step (↝-Ifᵣ P s) (≤-Ifᵣ P l)
≤-Ifᵣ P (≤-refl p) = ≤-refl (Ifᵣ P p)

≤-Parₗ : {P : Prog} {p p' : Pos P} (l : p ≤ p') {Q : Prog} (q : Pos Q) → Par p q ≤ Par p' q
≤-Parₗ (≤-step s l) q = ≤-step (↝-Parₗ s q) (≤-Parₗ l q)
≤-Parₗ (≤-refl p) q = ≤-refl (Par p q)

≤-Parᵣ : {P : Prog} (p : Pos P) {Q : Prog} {q q' : Pos Q} (l : q ≤ q') → Par p q ≤ Par p q'
≤-Parᵣ p (≤-step s l) = ≤-step (↝-Parᵣ p s) (≤-Parᵣ p l)
≤-Parᵣ p (≤-refl q) = ≤-refl (Par p q)

≤-While : {P : Prog} {n n' : ℕ} (_ : n ≤ℕ n') {p p' : Pos P} (l : p ≤ p') → While n p ≤ While n' p'
≤-While {n' = zero} z≤n l = {!!}
≤-While {n' = suc n'} z≤n l = {!!}
≤-While (s≤s ln) l = {!!}

-- ≤-Bot : {P : Prog} (p : Pos P) → (Bot P ≤ p)
-- ≤-Bot (Bot P) = ≤-refl (Bot P)
-- ≤-Bot (Top Act) = ≤-step ↝-Act (≤-refl (Top Act))
-- ≤-Bot (Top (Seq P Q)) =
  -- ≤-step (↝-Seq₀ P Q)
  -- (≤-trans (≤-Seqₗ (≤-Bot (Top P)) Q)
  -- (≤-step (↝-Seqₘ P Q)
  -- (≤-trans (≤-Seqᵣ P (≤-Bot (Top Q)))
  -- (≤-step1 (↝-Seq₁ P Q)))))
-- ≤-Bot (Seqₗ {P} p Q) = ≤-step (↝-Seq₀ P Q) (≤-Seqₗ (≤-Bot p) Q)
-- ≤-Bot (Seqᵣ P {Q} p) =
  -- ≤-step (↝-Seq₀ P Q)
  -- (≤-trans (≤-Seqₗ (≤-Bot (Top P)) Q)
  -- (≤-step (↝-Seqₘ P Q) (≤-Seqᵣ P (≤-Bot p))))

-- ≤-Top : {P : Prog} (p : Pos P) → (p ≤ Top P)
-- ≤-Top (Bot P) = ≤-Bot (Top P)
-- ≤-Top (Top P) = ≤-refl (Top P)
-- ≤-Top (Seqₗ {P} p Q) =
  -- ≤-trans (≤-Seqₗ (≤-Top p) Q)
  -- (≤-step (↝-Seqₘ P Q)
  -- (≤-trans (≤-Seqᵣ P (≤-Top (Bot Q)))
  -- (≤-step1 (↝-Seq₁ P Q))))
-- ≤-Top (Seqᵣ P {Q} p) =
  -- ≤-trans (≤-Seqᵣ P (≤-Top p))
  -- (≤-step1 (↝-Seq₁ P Q))

-- ≤-Seqₗ-Seqᵣ : {P Q : Prog} (p : Pos P) (q : Pos Q) → (Seqₗ p Q ≤ Seqᵣ P q)
-- ≤-Seqₗ-Seqᵣ {P} {Q} p q =
  -- ≤-trans (≤-Seqₗ (≤-Top p) Q)
  -- (≤-step (↝-Seqₘ P Q)
  -- (≤-Seqᵣ P (≤-Bot q)))

-- -- ---
-- -- --- Inversion lemmas
-- -- ---

-- ¬≤-Top-Bot : {P : Prog} → Top P ≤ Bot P → ⊥
-- ¬≤-Top-Bot (≤-step () l)

-- ¬≤-Top-Seqₗ : {P Q : Prog} {p : Pos P} → Top (Seq P Q) ≤ Seqₗ p Q → ⊥
-- ¬≤-Top-Seqₗ (≤-step () l)

-- ¬≤-Top-Seqᵣ : {P Q : Prog} {q : Pos Q} → Top (Seq P Q) ≤ Seqᵣ P q → ⊥
-- ¬≤-Top-Seqᵣ (≤-step () l)

-- ¬≤-Seqᵣ-Bot : {P Q : Prog} {q : Pos Q} → Seqᵣ P q ≤ Bot (Seq P Q) → ⊥
-- ¬≤-Seqᵣ-Bot (≤-step (↝-Seqᵣ P r) l) = ¬≤-Seqᵣ-Bot l
-- ¬≤-Seqᵣ-Bot (≤-step (↝-Seq₁ P Q) l) = ¬≤-Top-Bot l

-- ¬≤-Seqₗ-Bot : {P Q : Prog} {p : Pos P} → Seqₗ p Q ≤ Bot (Seq P Q) → ⊥
-- ¬≤-Seqₗ-Bot (≤-step (↝-Seqₗ s Q) l) = ¬≤-Seqₗ-Bot l
-- ¬≤-Seqₗ-Bot (≤-step (↝-Seqₘ P Q) l) = ¬≤-Seqᵣ-Bot l

-- ¬≤-Seqᵣ-Seqₗ : {P Q : Prog} {p : Pos P} {q : Pos Q} → Seqᵣ P q ≤ Seqₗ p Q → ⊥
-- ¬≤-Seqᵣ-Seqₗ (≤-step (↝-Seqᵣ P x) l) = ¬≤-Seqᵣ-Seqₗ l
-- ¬≤-Seqᵣ-Seqₗ (≤-step (↝-Seq₁ P Q) l) = ¬≤-Top-Seqₗ l

-- ≤-Seqₗ' : {P : Prog} {p p' : Pos P} {Q : Prog} → Seqₗ p Q ≤ Seqₗ p' Q → p ≤ p'
-- ≤-Seqₗ' (≤-step (↝-Seqₗ r Q) l) = ≤-step r (≤-Seqₗ' l)
-- ≤-Seqₗ' {_} {.(Top P)} {p'} (≤-step (↝-Seqₘ P Q) l) = ⊥-elim (¬≤-Seqᵣ-Seqₗ l)
-- ≤-Seqₗ' {_} {p} (≤-refl .(Seqₗ _ _)) = ≤-refl p

-- ≤-Seqᵣ' : {P : Prog} {Q : Prog} {q q' : Pos Q} → Seqᵣ P q ≤ Seqᵣ P q' → q ≤ q'
-- ≤-Seqᵣ' (≤-step (↝-Seqᵣ P r) l) = ≤-step r (≤-Seqᵣ' l)
-- ≤-Seqᵣ' (≤-step (↝-Seq₁ P Q) l) = ⊥-elim (¬≤-Top-Seqᵣ l)
-- ≤-Seqᵣ' {q = q} (≤-refl .(Seqᵣ _ _)) = ≤-refl q

-- ≤-Bot-≡ : {P : Prog} {p : Pos P} → (p ≤ Bot P) → (p ≡ Bot P)
-- ≤-Bot-≡ (≤-step ↝-Act l) = refl
-- ≤-Bot-≡ (≤-step (↝-Seq₀ P Q) l) = refl
-- ≤-Bot-≡ (≤-step (↝-Seqₗ x Q) l) = case ≤-Bot-≡ l of λ()
-- ≤-Bot-≡ (≤-step (↝-Seqₘ P Q) l) = case ≤-Bot-≡ l of λ()
-- ≤-Bot-≡ (≤-step (↝-Seqᵣ P x) l) = case ≤-Bot-≡ l of λ()
-- ≤-Bot-≡ (≤-step (↝-Seq₁ P Q) l) = case ≤-Bot-≡ l of λ()
-- ≤-Bot-≡ (≤-refl .(Bot _)) = refl

-- ≤-Top-≡ : {P : Prog} (p : Pos P) → (Top P ≤ p) → (p ≡ Top P)
-- ≤-Top-≡ p (≤-step () l)
-- ≤-Top-≡ .(Top _) (≤-refl .(Top _)) = refl

-- ≤-asym : {P : Prog} {p q : Pos P} → (p ≤ q) → (q ≤ p) → p ≡ q
-- ≤-asym (≤-step ↝-Act l) l' = ≡-sym (≤-Bot-≡ l')
-- ≤-asym (≤-step (↝-Seq₀ P Q) l) l' = ≡-sym (≤-Bot-≡ l')
-- ≤-asym (≤-step (↝-Seqₗ r Q) l) (≤-step (↝-Seq₀ P .Q) l') =  case ≤-Bot-≡ l of λ()
-- ≤-asym (≤-step (↝-Seqₗ r Q) l) (≤-step (↝-Seqₗ r' .Q) l') = cong (λ p → Seqₗ p Q) (≤-asym (≤-step r (≤-Seqₗ' l)) (≤-step r' (≤-Seqₗ' l')))
-- ≤-asym (≤-step (↝-Seqₗ r Q) l) (≤-step (↝-Seqₘ P .Q) l') = ⊥-elim (¬≤-Seqᵣ-Seqₗ l')
-- ≤-asym (≤-step (↝-Seqₗ r Q) l) (≤-step (↝-Seqᵣ P r') l') = ⊥-elim (¬≤-Seqᵣ-Seqₗ l')
-- ≤-asym (≤-step (↝-Seqₗ r Q) l) (≤-step (↝-Seq₁ P .Q) l') = ⊥-elim (¬≤-Top-Seqₗ l')
-- ≤-asym (≤-step (↝-Seqₗ r Q) l) (≤-refl .(Seqₗ _ Q)) = refl
-- ≤-asym (≤-step (↝-Seqₘ P Q) l) (≤-step (↝-Seq₀ .P .Q) l') = ⊥-elim (¬≤-Seqᵣ-Bot l)
-- ≤-asym (≤-step (↝-Seqₘ P Q) l) (≤-step (↝-Seqₗ r .Q) l') = ⊥-elim (¬≤-Seqᵣ-Seqₗ l)
-- ≤-asym (≤-step (↝-Seqₘ P Q) l) (≤-step (↝-Seqₘ .P .Q) l') = refl
-- ≤-asym (≤-step (↝-Seqₘ P Q) l) (≤-step (↝-Seqᵣ .P r) l') = ⊥-elim (¬≤-Seqᵣ-Seqₗ l')
-- ≤-asym (≤-step (↝-Seqₘ P Q) l) (≤-step (↝-Seq₁ .P .Q) l') = ⊥-elim (¬≤-Top-Seqₗ l')
-- ≤-asym (≤-step (↝-Seqₘ P Q) l) (≤-refl .(Seqₗ (Top P) Q)) = refl
-- ≤-asym (≤-step (↝-Seqᵣ P r) l) (≤-step (↝-Seq₀ .P Q) l') = ⊥-elim (¬≤-Seqᵣ-Bot l)
-- ≤-asym (≤-step (↝-Seqᵣ P r) l) (≤-step (↝-Seqₗ r' Q) l') = ⊥-elim (¬≤-Seqᵣ-Seqₗ l)
-- ≤-asym (≤-step (↝-Seqᵣ P r) l) (≤-step (↝-Seqₘ .P Q) l') = ⊥-elim (¬≤-Seqᵣ-Seqₗ l)
-- ≤-asym (≤-step (↝-Seqᵣ P r) l) (≤-step (↝-Seqᵣ .P r') l') = cong (λ q → Seqᵣ P q) (≤-asym (≤-step r (≤-Seqᵣ' l)) (≤-step r' (≤-Seqᵣ' l')))
-- ≤-asym (≤-step (↝-Seqᵣ P r) l) (≤-step (↝-Seq₁ .P Q) l') = ⊥-elim (¬≤-Top-Seqᵣ l')
-- ≤-asym (≤-step (↝-Seqᵣ P r) l) (≤-refl .(Seqᵣ P _)) = refl
-- ≤-asym (≤-step (↝-Seq₁ P Q) l) (≤-step (↝-Seq₀ .P .Q) l') = ⊥-elim (¬≤-Top-Bot l)
-- ≤-asym (≤-step (↝-Seq₁ P Q) l) (≤-step (↝-Seqₗ r .Q) l') = ⊥-elim (¬≤-Top-Seqₗ l)
-- ≤-asym (≤-step (↝-Seq₁ P Q) l) (≤-step (↝-Seqₘ .P .Q) l') = ⊥-elim (¬≤-Top-Seqₗ l)
-- ≤-asym (≤-step (↝-Seq₁ P Q) l) (≤-step (↝-Seqᵣ .P r) l') = ⊥-elim (¬≤-Top-Seqᵣ l)
-- ≤-asym (≤-step (↝-Seq₁ P Q) l) (≤-step (↝-Seq₁ .P .Q) l') = refl
-- ≤-asym (≤-step (↝-Seq₁ P Q) l) (≤-refl .(Seqᵣ P (Top Q))) = refl
-- ≤-asym (≤-refl p) l' = refl

-- ≤-dec : {P : Prog} → Decidable (_≤_ {P})
-- ≤-dec (Bot P) q = yes (≤-Bot q)
-- ≤-dec (Top P) (Bot .P) = no ¬≤-Top-Bot
-- ≤-dec (Top P) (Top .P) = yes (≤-refl (Top P))
-- ≤-dec (Top .(Seq _ Q)) (Seqₗ q Q) = no ¬≤-Top-Seqₗ
-- ≤-dec (Top .(Seq P _)) (Seqᵣ P q) = no ¬≤-Top-Seqᵣ
-- ≤-dec (Seqₗ p Q) (Bot .(Seq _ Q)) = no ¬≤-Seqₗ-Bot
-- ≤-dec (Seqₗ p Q) (Top .(Seq _ Q)) = yes (≤-Top (Seqₗ p Q))
-- ≤-dec (Seqₗ p Q) (Seqₗ q .Q) =  case ≤-dec p q of λ { (yes l) → yes (≤-Seqₗ l Q) ; (no ¬l) → no (λ l → ¬l (≤-Seqₗ' l)) }
-- ≤-dec (Seqₗ p Q) (Seqᵣ P q) = yes (≤-Seqₗ-Seqᵣ p q)
-- ≤-dec (Seqᵣ P p) (Bot .(Seq P _)) = no ¬≤-Seqᵣ-Bot
-- ≤-dec (Seqᵣ P p) (Top .(Seq P _)) = yes (≤-Top (Seqᵣ P p))
-- ≤-dec (Seqᵣ P p) (Seqₗ q Q) = no ¬≤-Seqᵣ-Seqₗ
-- ≤-dec (Seqᵣ P p) (Seqᵣ .P q) = case ≤-dec p q of λ { (yes l) → yes (≤-Seqᵣ P l) ; (no ¬l) → no λ l → ¬l (≤-Seqᵣ' l)}
