open import Relation.Binary.PropositionalEquality

transport : {A B : Set} → (A ≡ B) → A → B
transport refl x = x

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
  ↝-Seq₀ : (P Q : Prog) → Bot (Seq P Q) ↝ Seqₗ (Bot P) Q
  ↝-Seqₗ : {P : Prog} {p p' : Pos P} → (p ↝ p') → (Q : Prog) → Seqₗ p Q ↝ Seqₗ p' Q
  ↝-Seqₘ : (P Q : Prog) → Seqₗ (Top P) Q ↝ Seqᵣ P (Bot Q)
  ↝-Seqᵣ : (P : Prog) {Q : Prog} {q q' : Pos Q} → (q ↝ q') → Seqᵣ P q ↝ Seqᵣ P q'
  ↝-Seq₁ : (P Q : Prog) → Seqᵣ P (Top Q) ↝ Top (Seq P Q)

-- data _≤_ : {P : Prog} (p q : Pos P) → Set where
  -- ≤-refl : {P : Prog} (p : Pos P) → p ≤ p
  -- ≤-trans : {P : Prog} (p q r : Pos P) → (p ≤ q) → (q ≤ r) → (p ≤ r)
  -- ≤-bot : {P : Prog} (p : Pos P) → (Bot P) ≤ p
  -- ≤-top : {P : Prog} (p : Pos P) → p ≤ (Top P)
  -- ≤-Seqₗ : {P : Prog} {p p' : Pos P} → (p ≤ p') → (Q : Prog) → Seqₗ p Q ≤ Seqₗ p' Q
  -- ≤-Seqᵣ : (P : Prog) {Q : Prog} {q q' : Pos Q} → (q ≤ q') → Seqᵣ P q ≤ Seqᵣ P q'
  -- ≤-Seqₗᵣ : {P : Prog} (p : Pos P) {Q : Prog} {q : Pos Q} → Seqₗ p Q ≤ Seqᵣ P q

--
-- Order between positions
--

data _≤_ : {P : Prog} (p : Pos P) (q : Pos P) → Set where
  ≤-step : {P : Prog} {p q : Pos P} → (p ↝ q) → p ≤ q
  ≤-refl : {P : Prog} (p : Pos P) → p ≤ p
  ≤-trans : {P : Prog} {p q r : Pos P} → (p ≤ q) → (q ≤ r) → p ≤ r

≤-Seqₗ : {P : Prog} {p p' : Pos P} (l : p ≤ p') (Q : Prog) → Seqₗ p Q ≤ Seqₗ p' Q
≤-Seqₗ (≤-step l) Q = ≤-step (↝-Seqₗ l Q)
≤-Seqₗ (≤-refl p) Q = ≤-refl (Seqₗ p Q)
≤-Seqₗ (≤-trans l l') Q = ≤-trans (≤-Seqₗ l Q) (≤-Seqₗ l' Q)

≤-Seqᵣ : (P : Prog) {Q : Prog} {q q' : Pos Q} (l : q ≤ q') → Seqᵣ P q ≤ Seqᵣ P q'
≤-Seqᵣ P (≤-step l) = ≤-step (↝-Seqᵣ P l)
≤-Seqᵣ P (≤-refl p) = ≤-refl (Seqᵣ P p)
≤-Seqᵣ P (≤-trans {Q} l l') = ≤-trans (≤-Seqᵣ P {Q} l) (≤-Seqᵣ P {Q} l')

≤-Bot : {P : Prog} (p : Pos P) → (Bot P ≤ p)
≤-Bot (Bot P) = ≤-refl (Bot P)
≤-Bot (Top Act) = ≤-step ↝-Act
≤-Bot (Top (Seq P Q)) =
  ≤-trans
    (≤-trans (≤-step (↝-Seq₀ P Q)) (≤-trans (≤-Seqₗ (≤-Bot (Top P)) Q) (≤-step (↝-Seqₘ P Q))))
    (≤-trans (≤-Seqᵣ P (≤-Bot (Top Q))) (≤-step (↝-Seq₁ P Q)))
≤-Bot (Seqₗ {P} p Q) = ≤-trans (≤-step (↝-Seq₀ P Q)) (≤-Seqₗ (≤-Bot p) Q)
≤-Bot (Seqᵣ P {Q} p) =
  ≤-trans (≤-step (↝-Seq₀ P Q))
  (≤-trans (≤-Seqₗ (≤-Bot (Top P)) Q)
  (≤-trans (≤-step (↝-Seqₘ P Q))
  (≤-Seqᵣ P (≤-Bot p))))

≤-Top : {P : Prog} (p : Pos P) → (p ≤ Top P)
≤-Top (Bot P) = ≤-Bot (Top P)
≤-Top (Top P) = ≤-refl (Top P)
≤-Top (Seqₗ {P} p Q) =
  ≤-trans (≤-Seqₗ (≤-Top p) Q)
  (≤-trans (≤-step (↝-Seqₘ P Q))
  (≤-trans (≤-Seqᵣ P (≤-Top (Bot Q)))
  (≤-step (↝-Seq₁ P Q))))
≤-Top (Seqᵣ P {Q} p) =
  ≤-trans (≤-Seqᵣ P (≤-Top p))
  (≤-step (↝-Seq₁ P Q))

≤-Seqₗ-Seqᵣ : {P Q : Prog} (p : Pos P) (q : Pos Q) → (Seqₗ p Q ≤ Seqᵣ P q)
≤-Seqₗ-Seqᵣ {P} {Q} p q =
  ≤-trans (≤-Seqₗ (≤-Top p) Q)
  (≤-trans (≤-step (↝-Seqₘ P Q))
  (≤-Seqᵣ P (≤-Bot q)))

--
-- The lattice of positions
--

_∨_ : {P : Prog} (p q : Pos P) → Pos P
Bot P ∨ q = q
Top P ∨ q = Top P
Seqₗ p Q ∨ Bot .(Seq _ Q) = Seqₗ p Q
Seqₗ {P} p Q ∨ Top .(Seq P Q) = Top (Seq P Q)
Seqₗ p Q ∨ Seqₗ q .Q = Seqₗ (p ∨ q) Q
Seqₗ p Q ∨ Seqᵣ P q = Seqᵣ P q
Seqᵣ P p ∨ Bot .(Seq P _) = Seqᵣ P p
Seqᵣ P {Q} q ∨ Top .(Seq P Q) = Top (Seq P Q)
Seqᵣ P p ∨ Seqₗ q Q = Seqᵣ P p
Seqᵣ P p ∨ Seqᵣ .P q = Seqᵣ P (p ∨ q)

∨-Seqₗ : {P : Prog} (p p' : Pos P) (Q : Prog) → (Seqₗ p Q ∨ Seqₗ p' Q ≡ Seqₗ (p ∨ p') Q)
∨-Seqₗ (Bot P) p' Q = refl
∨-Seqₗ (Top P) p' Q = refl
∨-Seqₗ (Seqₗ p Q₁) p' Q = refl
∨-Seqₗ (Seqᵣ P p) p' Q = refl

∨-Seqᵣ : (P : Prog) {Q : Prog} (q q' : Pos Q) → (Seqᵣ P q ∨ Seqᵣ P q' ≡ Seqᵣ P (q ∨ q'))
∨-Seqᵣ P (Bot P₁) q' = refl
∨-Seqᵣ P (Top P₁) q' = refl
∨-Seqᵣ P (Seqₗ q Q) q' = refl
∨-Seqᵣ P (Seqᵣ P₁ q) q' = refl

sup-idem : {P : Prog} (p : Pos P) → (p ∨ p ≡ p)
sup-idem (Bot P) = refl
sup-idem (Top P) = refl
sup-idem (Seqₗ p Q) = trans (∨-Seqₗ p p Q) (cong (λ p → Seqₗ p Q) (sup-idem p))
sup-idem (Seqᵣ P q) = trans (∨-Seqᵣ P q q) (cong (λ q → Seqᵣ P q) (sup-idem q))

sup-comm : {P : Prog} (p q : Pos P) → ((p ∨ q) ≡ (q ∨ p))
sup-comm (Bot P) (Bot .P) = refl
sup-comm (Bot P) (Top .P) = refl
sup-comm (Bot .(Seq _ Q)) (Seqₗ q Q) = refl
sup-comm (Bot .(Seq P _)) (Seqᵣ P q) = refl
sup-comm (Top P) (Bot .P) = refl
sup-comm (Top P) (Top .P) = refl
sup-comm (Top .(Seq _ Q)) (Seqₗ q Q) = refl
sup-comm (Top .(Seq P _)) (Seqᵣ P q) = refl
sup-comm (Seqₗ p Q) (Bot .(Seq _ Q)) = refl
sup-comm (Seqₗ p Q) (Top .(Seq _ Q)) = refl
sup-comm (Seqₗ p Q) (Seqₗ q .Q) = trans (∨-Seqₗ p q Q) (trans (cong (λ p → Seqₗ p Q) (sup-comm p q)) (sym (∨-Seqₗ q p Q)))
sup-comm (Seqₗ p Q) (Seqᵣ P q) = refl
sup-comm (Seqᵣ P p) (Bot .(Seq P _)) = refl
sup-comm (Seqᵣ P p) (Top .(Seq P _)) = refl
sup-comm (Seqᵣ P p) (Seqₗ q Q) = refl
sup-comm (Seqᵣ P p) (Seqᵣ .P q) = trans (∨-Seqᵣ P p q) (trans (cong (λ q → Seqᵣ P q) (sup-comm p q)) (sym (∨-Seqᵣ P q p)))

sup-bigger-l : {P : Prog} (p q : Pos P) → (p ≤ (p ∨ q))
sup-bigger-l (Bot P) q = ≤-Bot q
sup-bigger-l (Top P) (Bot .P) = ≤-refl (Top P)
sup-bigger-l (Top P) (Top .P) = ≤-refl (Top P)
sup-bigger-l (Top .(Seq _ Q)) (Seqₗ {P} q Q) = ≤-refl (Top (Seq P Q))
sup-bigger-l (Top .(Seq P _)) (Seqᵣ P {Q} q) = ≤-refl (Top (Seq P Q))
sup-bigger-l (Seqₗ p Q) (Bot .(Seq _ Q)) = ≤-refl (Seqₗ p Q)
sup-bigger-l (Seqₗ p Q) (Top .(Seq _ Q)) = ≤-Top (Seqₗ p Q)
sup-bigger-l (Seqₗ p Q) (Seqₗ q .Q) = ≤-Seqₗ (sup-bigger-l p q) Q
sup-bigger-l (Seqₗ p Q) (Seqᵣ P q) = ≤-Seqₗ-Seqᵣ p q
sup-bigger-l (Seqᵣ P p) (Bot .(Seq P _)) = ≤-refl (Seqᵣ P p)
sup-bigger-l (Seqᵣ P p) (Top .(Seq P _)) = ≤-Top (Seqᵣ P p)
sup-bigger-l (Seqᵣ P p) (Seqₗ q Q) = ≤-Seqᵣ P (≤-refl p)
sup-bigger-l (Seqᵣ P p) (Seqᵣ .P q) = ≤-Seqᵣ P (sup-bigger-l p q)

sup-bigger-r : {P : Prog} (p q : Pos P) → (q ≤ (p ∨ q))
sup-bigger-r p q = transport (cong (λ p → q ≤ p) (sup-comm q p)) (sup-bigger-l q p)

sup-inc-l : {P : Prog} (p p' q : Pos P) → (p ≤ p') → ((p ∨ q) ≤ (p' ∨ q))
sup-inc-l .(Bot Act) .(Top Act) q (≤-step ↝-Act) = ≤-Top q
sup-inc-l .(Bot (Seq P Q)) .(Seqₗ (Bot P) Q) (Bot .(Seq P Q)) (≤-step (↝-Seq₀ P Q)) = ≤-step (↝-Seq₀ P Q)
sup-inc-l .(Bot (Seq P Q)) .(Seqₗ (Bot P) Q) (Top .(Seq P Q)) (≤-step (↝-Seq₀ P Q)) = ≤-refl (Top (Seq P Q))
sup-inc-l .(Bot (Seq P Q)) .(Seqₗ (Bot P) Q) (Seqₗ q .Q) (≤-step (↝-Seq₀ P Q)) = ≤-refl (Seqₗ q Q)
sup-inc-l .(Bot (Seq P Q)) .(Seqₗ (Bot P) Q) (Seqᵣ .P q) (≤-step (↝-Seq₀ P Q)) = ≤-refl (Seqᵣ P q)
sup-inc-l .(Seqₗ _ Q) .(Seqₗ _ Q) (Bot .(Seq _ Q)) (≤-step (↝-Seqₗ x Q)) = ≤-step (↝-Seqₗ x Q)
sup-inc-l .(Seqₗ _ Q) .(Seqₗ _ Q) (Top .(Seq _ Q)) (≤-step (↝-Seqₗ {P} x Q)) = ≤-refl (Top (Seq P Q))
sup-inc-l .(Seqₗ _ Q) .(Seqₗ _ Q) (Seqₗ q .Q) (≤-step (↝-Seqₗ {P} {p} {p'} l Q)) = ≤-Seqₗ (sup-inc-l p p' q (≤-step l)) Q
sup-inc-l .(Seqₗ _ Q) .(Seqₗ _ Q) (Seqᵣ P q) (≤-step (↝-Seqₗ x Q)) = ≤-refl (Seqᵣ P q)
sup-inc-l .(Seqₗ (Top P) Q) .(Seqᵣ P (Bot Q)) (Bot .(Seq P Q)) (≤-step (↝-Seqₘ P Q)) = ≤-step (↝-Seqₘ P Q)
sup-inc-l .(Seqₗ (Top P) Q) .(Seqᵣ P (Bot Q)) (Top .(Seq P Q)) (≤-step (↝-Seqₘ P Q)) = ≤-refl (Top (Seq P Q))
sup-inc-l .(Seqₗ (Top P) Q) .(Seqᵣ P (Bot Q)) (Seqₗ q .Q) (≤-step (↝-Seqₘ P Q)) = ≤-step (↝-Seqₘ P Q)
sup-inc-l .(Seqₗ (Top P) Q) .(Seqᵣ P (Bot Q)) (Seqᵣ .P q) (≤-step (↝-Seqₘ P Q)) = ≤-refl (Seqᵣ P q)
sup-inc-l .(Seqᵣ P _) .(Seqᵣ P _) (Bot .(Seq P _)) (≤-step (↝-Seqᵣ P x)) = ≤-step (↝-Seqᵣ P x)
sup-inc-l .(Seqᵣ P _) .(Seqᵣ P _) (Top .(Seq P _)) (≤-step (↝-Seqᵣ P {Q} {q} {q'} l)) = ≤-refl (Top (Seq P Q))
sup-inc-l .(Seqᵣ P _) .(Seqᵣ P _) (Seqₗ q Q) (≤-step (↝-Seqᵣ P x)) = ≤-step (↝-Seqᵣ P x)
sup-inc-l .(Seqᵣ P _) .(Seqᵣ P _) (Seqᵣ .P p) (≤-step (↝-Seqᵣ P {Q} {q} {q'} l)) = ≤-Seqᵣ P (sup-inc-l q q' p (≤-step l))
sup-inc-l .(Seqᵣ P (Top Q)) .(Top (Seq P Q)) q (≤-step (↝-Seq₁ P Q)) = ≤-Top (Seqᵣ P (Top Q) ∨ q)
sup-inc-l p .p q (≤-refl .p) = ≤-refl (p ∨ q)
sup-inc-l p p' q (≤-trans {_} {.p} {p''} l l') = ≤-trans (sup-inc-l p p'' q l) (sup-inc-l p'' p' q l')

sup-inc-r : {P : Prog} (p q q' : Pos P) → (q ≤ q') → ((p ∨ q) ≤ (p ∨ q'))
sup-inc-r p q q' l =
  transport (cong (λ r → r ≤ (p ∨ q')) (sup-comm q p))
  (transport (cong (λ r → (q ∨ p) ≤ r) (sup-comm q' p))
  (sup-inc-l q q' p l))

-- TODO: sup-lattice

--
-- Complements (TODO: better name, this is already taken) 
--

open import Data.List

-- maximal elements not greater

-- ¬≥ : {P : Prog} (p : Pos P) → List (Pos P)
-- ¬≥ (Bot P) = (Bot P) ∷ []
-- ¬≥ (Top P) = (Top P) ∷ []
-- ¬≥ (Seqₗ p Q) = map (λ p → Seqₗ p Q) (¬≥ p)
-- ¬≥ (Seqᵣ P q) = map (λ q → Seqᵣ P q) (¬≥ q)

data _¬≥_ : {P : Prog} (p : Pos P) → (q : Pos P) → Set where
  ¬≥-Bot : {P : Prog} → (Bot P) ¬≥ (Bot P)
  ¬≥-Top : {P : Prog} → (Top P) ¬≥ (Top P)
  ¬≥-Seqₗ : {P : Prog} {p p' : Pos P} → (p ¬≥ p') → (Q : Prog) → Seqₗ p Q ¬≥ Seqₗ p' Q
  ¬≥-Seqᵣ : (P : Prog) {Q : Prog} {q q' : Pos P} → (q ¬≥ q') → Seqᵣ P q ¬≥ Seqᵣ P q'

-- ¬≥-sound : {P : Prog} (p : Pos P) (q ≤ p)
-- ¬≥-sound = ?

¬≥-complete : {P : Prog} (p : Pos P) (x : Pos P)
