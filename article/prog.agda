open import Relation.Binary.PropositionalEquality

open import Function
open import Data.Empty
open import Data.Sum
open import Data.Product

_and_ : (A : Set) (B : Set) → Set
A and B = A × B

_or_ : (A : Set) (B : Set) → Set
A or B = A ⊎ B

≡-trans : {A : Set} {a b c : A} → (a ≡ b) → (b ≡ c) → (a ≡ c)
≡-trans refl refl = refl

≡-sym : {A : Set} {a b : A} → (a ≡ b) → (b ≡ a)
≡-sym refl = refl

coe : {A B : Set} → (A ≡ B) → A → B
coe refl x = x

transport : {A : Set} (B : A → Set) {x y : A} (p : x ≡ y) → B x → B y
transport B refl x = x

---
--- Programs
---

data Prog : Set where
  Act : Prog
  Seq : Prog → Prog → Prog

---
--- Positions
---

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
  ≤-step : {P : Prog} {p q r : Pos P} → (p ↝ q) → (q ≤ r) → p ≤ r
  ≤-refl : {P : Prog} (p : Pos P) → p ≤ p

≤-trans : {P : Prog} {p q r : Pos P} → (p ≤ q) → (q ≤ r) → (p ≤ r)
≤-trans (≤-step r l) l' = ≤-step r (≤-trans l l')
≤-trans (≤-refl p) l' = l'

≤-step1 : {P : Prog} {p q : Pos P} → (p ↝ q) → (p ≤ q)
≤-step1 {_} {_} {q} r = ≤-step r (≤-refl q)

_≥_ : {P : Prog} (p : Pos P) (q : Pos P) → Set
p ≥ q = q ≤ p

≤-Seqₗ : {P : Prog} {p p' : Pos P} (l : p ≤ p') (Q : Prog) → Seqₗ p Q ≤ Seqₗ p' Q
≤-Seqₗ (≤-step r l) Q = ≤-step (↝-Seqₗ r Q) (≤-Seqₗ l Q)
≤-Seqₗ (≤-refl p) Q = ≤-refl (Seqₗ p Q)

≤-Seqᵣ : (P : Prog) {Q : Prog} {q q' : Pos Q} (l : q ≤ q') → Seqᵣ P q ≤ Seqᵣ P q'
≤-Seqᵣ P (≤-step r l) = ≤-step (↝-Seqᵣ P r) (≤-Seqᵣ P l)
≤-Seqᵣ P (≤-refl p) = ≤-refl (Seqᵣ P p)

≤-Bot : {P : Prog} (p : Pos P) → (Bot P ≤ p)
≤-Bot (Bot P) = ≤-refl (Bot P)
≤-Bot (Top Act) = ≤-step ↝-Act (≤-refl (Top Act))
≤-Bot (Top (Seq P Q)) =
  ≤-step (↝-Seq₀ P Q)
  (≤-trans (≤-Seqₗ (≤-Bot (Top P)) Q)
  (≤-step (↝-Seqₘ P Q)
  (≤-trans (≤-Seqᵣ P (≤-Bot (Top Q)))
  (≤-step1 (↝-Seq₁ P Q)))))
≤-Bot (Seqₗ {P} p Q) = ≤-step (↝-Seq₀ P Q) (≤-Seqₗ (≤-Bot p) Q)
≤-Bot (Seqᵣ P {Q} p) =
  ≤-step (↝-Seq₀ P Q)
  (≤-trans (≤-Seqₗ (≤-Bot (Top P)) Q)
  (≤-step (↝-Seqₘ P Q) (≤-Seqᵣ P (≤-Bot p))))

≤-Top : {P : Prog} (p : Pos P) → (p ≤ Top P)
≤-Top (Bot P) = ≤-Bot (Top P)
≤-Top (Top P) = ≤-refl (Top P)
≤-Top (Seqₗ {P} p Q) =
  ≤-trans (≤-Seqₗ (≤-Top p) Q)
  (≤-step (↝-Seqₘ P Q)
  (≤-trans (≤-Seqᵣ P (≤-Top (Bot Q)))
  (≤-step1 (↝-Seq₁ P Q))))
≤-Top (Seqᵣ P {Q} p) =
  ≤-trans (≤-Seqᵣ P (≤-Top p))
  (≤-step1 (↝-Seq₁ P Q))

≤-Seqₗ-Seqᵣ : {P Q : Prog} (p : Pos P) (q : Pos Q) → (Seqₗ p Q ≤ Seqᵣ P q)
≤-Seqₗ-Seqᵣ {P} {Q} p q =
  ≤-trans (≤-Seqₗ (≤-Top p) Q)
  (≤-step (↝-Seqₘ P Q)
  (≤-Seqᵣ P (≤-Bot q)))

-- ---
-- --- Inversion lemmas
-- ---

¬≤-Top-Bot : {P : Prog} → Top P ≤ Bot P → ⊥
¬≤-Top-Bot (≤-step () l)

¬≤-Top-Seqₗ : {P Q : Prog} {p : Pos P} → Top (Seq P Q) ≤ Seqₗ p Q → ⊥
¬≤-Top-Seqₗ (≤-step () l)

¬≤-Top-Seqᵣ : {P Q : Prog} {q : Pos Q} → Top (Seq P Q) ≤ Seqᵣ P q → ⊥
¬≤-Top-Seqᵣ (≤-step () l)

¬≤-Seqᵣ-Bot : {P Q : Prog} {q : Pos Q} → Seqᵣ P q ≤ Bot (Seq P Q) → ⊥
¬≤-Seqᵣ-Bot (≤-step (↝-Seqᵣ P r) l) = ¬≤-Seqᵣ-Bot l
¬≤-Seqᵣ-Bot (≤-step (↝-Seq₁ P Q) l) = ¬≤-Top-Bot l

¬≤-Seqₗ-Bot : {P Q : Prog} {p : Pos P} → Seqₗ p Q ≤ Bot (Seq P Q) → ⊥
¬≤-Seqₗ-Bot (≤-step (↝-Seqₗ s Q) l) = ¬≤-Seqₗ-Bot l
¬≤-Seqₗ-Bot (≤-step (↝-Seqₘ P Q) l) = ¬≤-Seqᵣ-Bot l

¬≤-Seqᵣ-Seqₗ : {P Q : Prog} {p : Pos P} {q : Pos Q} → Seqᵣ P q ≤ Seqₗ p Q → ⊥
¬≤-Seqᵣ-Seqₗ (≤-step (↝-Seqᵣ P x) l) = ¬≤-Seqᵣ-Seqₗ l
¬≤-Seqᵣ-Seqₗ (≤-step (↝-Seq₁ P Q) l) = ¬≤-Top-Seqₗ l

≤-Seqₗ' : {P : Prog} {p p' : Pos P} {Q : Prog} → Seqₗ p Q ≤ Seqₗ p' Q → p ≤ p'
≤-Seqₗ' (≤-step (↝-Seqₗ r Q) l) = ≤-step r (≤-Seqₗ' l)
≤-Seqₗ' {_} {.(Top P)} {p'} (≤-step (↝-Seqₘ P Q) l) = ⊥-elim (¬≤-Seqᵣ-Seqₗ l)
≤-Seqₗ' {_} {p} (≤-refl .(Seqₗ _ _)) = ≤-refl p

≤-Seqᵣ' : {P : Prog} {Q : Prog} {q q' : Pos Q} → Seqᵣ P q ≤ Seqᵣ P q' → q ≤ q'
≤-Seqᵣ' (≤-step (↝-Seqᵣ P r) l) = ≤-step r (≤-Seqᵣ' l)
≤-Seqᵣ' (≤-step (↝-Seq₁ P Q) l) = ⊥-elim (¬≤-Top-Seqᵣ l)
≤-Seqᵣ' {q = q} (≤-refl .(Seqᵣ _ _)) = ≤-refl q

≤-Bot-≡ : {P : Prog} {p : Pos P} → (p ≤ Bot P) → (p ≡ Bot P)
≤-Bot-≡ (≤-step ↝-Act l) = refl
≤-Bot-≡ (≤-step (↝-Seq₀ P Q) l) = refl
≤-Bot-≡ (≤-step (↝-Seqₗ x Q) l) = case ≤-Bot-≡ l of λ()
≤-Bot-≡ (≤-step (↝-Seqₘ P Q) l) = case ≤-Bot-≡ l of λ()
≤-Bot-≡ (≤-step (↝-Seqᵣ P x) l) = case ≤-Bot-≡ l of λ()
≤-Bot-≡ (≤-step (↝-Seq₁ P Q) l) = case ≤-Bot-≡ l of λ()
≤-Bot-≡ (≤-refl .(Bot _)) = refl

≤-Top-≡ : {P : Prog} (p : Pos P) → (Top P ≤ p) → (p ≡ Top P)
≤-Top-≡ p (≤-step () l)
≤-Top-≡ .(Top _) (≤-refl .(Top _)) = refl

≤-asym : {P : Prog} {p q : Pos P} → (p ≤ q) → (q ≤ p) → p ≡ q
≤-asym (≤-step ↝-Act l) l' = ≡-sym (≤-Bot-≡ l')
≤-asym (≤-step (↝-Seq₀ P Q) l) l' = ≡-sym (≤-Bot-≡ l')
≤-asym (≤-step (↝-Seqₗ r Q) l) (≤-step (↝-Seq₀ P .Q) l') =  case ≤-Bot-≡ l of λ()
≤-asym (≤-step (↝-Seqₗ r Q) l) (≤-step (↝-Seqₗ r' .Q) l') = cong (λ p → Seqₗ p Q) (≤-asym (≤-step r (≤-Seqₗ' l)) (≤-step r' (≤-Seqₗ' l')))
≤-asym (≤-step (↝-Seqₗ r Q) l) (≤-step (↝-Seqₘ P .Q) l') = ⊥-elim (¬≤-Seqᵣ-Seqₗ l')
≤-asym (≤-step (↝-Seqₗ r Q) l) (≤-step (↝-Seqᵣ P r') l') = ⊥-elim (¬≤-Seqᵣ-Seqₗ l')
≤-asym (≤-step (↝-Seqₗ r Q) l) (≤-step (↝-Seq₁ P .Q) l') = ⊥-elim (¬≤-Top-Seqₗ l')
≤-asym (≤-step (↝-Seqₗ r Q) l) (≤-refl .(Seqₗ _ Q)) = refl
≤-asym (≤-step (↝-Seqₘ P Q) l) (≤-step (↝-Seq₀ .P .Q) l') = ⊥-elim (¬≤-Seqᵣ-Bot l)
≤-asym (≤-step (↝-Seqₘ P Q) l) (≤-step (↝-Seqₗ r .Q) l') = ⊥-elim (¬≤-Seqᵣ-Seqₗ l)
≤-asym (≤-step (↝-Seqₘ P Q) l) (≤-step (↝-Seqₘ .P .Q) l') = refl
≤-asym (≤-step (↝-Seqₘ P Q) l) (≤-step (↝-Seqᵣ .P r) l') = ⊥-elim (¬≤-Seqᵣ-Seqₗ l')
≤-asym (≤-step (↝-Seqₘ P Q) l) (≤-step (↝-Seq₁ .P .Q) l') = ⊥-elim (¬≤-Top-Seqₗ l')
≤-asym (≤-step (↝-Seqₘ P Q) l) (≤-refl .(Seqₗ (Top P) Q)) = refl
≤-asym (≤-step (↝-Seqᵣ P r) l) (≤-step (↝-Seq₀ .P Q) l') = ⊥-elim (¬≤-Seqᵣ-Bot l)
≤-asym (≤-step (↝-Seqᵣ P r) l) (≤-step (↝-Seqₗ r' Q) l') = ⊥-elim (¬≤-Seqᵣ-Seqₗ l)
≤-asym (≤-step (↝-Seqᵣ P r) l) (≤-step (↝-Seqₘ .P Q) l') = ⊥-elim (¬≤-Seqᵣ-Seqₗ l)
≤-asym (≤-step (↝-Seqᵣ P r) l) (≤-step (↝-Seqᵣ .P r') l') = cong (λ q → Seqᵣ P q) (≤-asym (≤-step r (≤-Seqᵣ' l)) (≤-step r' (≤-Seqᵣ' l')))
≤-asym (≤-step (↝-Seqᵣ P r) l) (≤-step (↝-Seq₁ .P Q) l') = ⊥-elim (¬≤-Top-Seqᵣ l')
≤-asym (≤-step (↝-Seqᵣ P r) l) (≤-refl .(Seqᵣ P _)) = refl
≤-asym (≤-step (↝-Seq₁ P Q) l) (≤-step (↝-Seq₀ .P .Q) l') = ⊥-elim (¬≤-Top-Bot l)
≤-asym (≤-step (↝-Seq₁ P Q) l) (≤-step (↝-Seqₗ r .Q) l') = ⊥-elim (¬≤-Top-Seqₗ l)
≤-asym (≤-step (↝-Seq₁ P Q) l) (≤-step (↝-Seqₘ .P .Q) l') = ⊥-elim (¬≤-Top-Seqₗ l)
≤-asym (≤-step (↝-Seq₁ P Q) l) (≤-step (↝-Seqᵣ .P r) l') = ⊥-elim (¬≤-Top-Seqᵣ l)
≤-asym (≤-step (↝-Seq₁ P Q) l) (≤-step (↝-Seq₁ .P .Q) l') = refl
≤-asym (≤-step (↝-Seq₁ P Q) l) (≤-refl .(Seqᵣ P (Top Q))) = refl
≤-asym (≤-refl p) l' = refl

-- --
-- -- The lattice of positions
-- --

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

∨-Bot-l : {P : Prog} (p : Pos P) → (Bot P ∨ p ≡ p)
∨-Bot-l (Bot P) = refl
∨-Bot-l (Top P) = refl
∨-Bot-l (Seqₗ p Q) = refl
∨-Bot-l (Seqᵣ P p) = refl

∨-assoc : {P : Prog} (p q r : Pos P) → ((p ∨ q) ∨ r ≡ p ∨ (q ∨ r))
∨-assoc (Bot P) q r = refl
∨-assoc (Top P) q r = refl
∨-assoc (Seqₗ p Q) (Bot .(Seq _ Q)) r = refl
∨-assoc (Seqₗ p Q) (Top .(Seq _ Q)) r = refl
∨-assoc (Seqₗ p Q) (Seqₗ q .Q) (Bot .(Seq _ Q)) = refl
∨-assoc (Seqₗ p Q) (Seqₗ q .Q) (Top .(Seq _ Q)) = refl
∨-assoc (Seqₗ p Q) (Seqₗ q .Q) (Seqₗ r .Q) = cong (λ p → Seqₗ p Q) (∨-assoc p q r)
∨-assoc (Seqₗ p Q) (Seqₗ q .Q) (Seqᵣ P r) = refl
∨-assoc (Seqₗ p Q) (Seqᵣ P q) (Bot .(Seq P Q)) = refl
∨-assoc (Seqₗ p Q) (Seqᵣ P q) (Top .(Seq P Q)) = refl
∨-assoc (Seqₗ p Q) (Seqᵣ P q) (Seqₗ r .Q) = refl
∨-assoc (Seqₗ p Q) (Seqᵣ P q) (Seqᵣ .P r) = refl
∨-assoc (Seqᵣ P p) (Bot .(Seq P _)) r = refl
∨-assoc (Seqᵣ P p) (Top .(Seq P _)) r = refl
∨-assoc (Seqᵣ P p) (Seqₗ q Q) (Bot .(Seq P Q)) = refl
∨-assoc (Seqᵣ P p) (Seqₗ q Q) (Top .(Seq P Q)) = refl
∨-assoc (Seqᵣ P p) (Seqₗ q Q) (Seqₗ r .Q) = refl
∨-assoc (Seqᵣ P p) (Seqₗ q Q) (Seqᵣ .P r) = refl
∨-assoc (Seqᵣ P p) (Seqᵣ .P q) (Bot .(Seq P _)) = refl
∨-assoc (Seqᵣ P p) (Seqᵣ .P q) (Top .(Seq P _)) = refl
∨-assoc (Seqᵣ P p) (Seqᵣ .P q) (Seqₗ r Q) = refl
∨-assoc (Seqᵣ P p) (Seqᵣ .P q) (Seqᵣ .P r) = cong (λ q → Seqᵣ P q) (∨-assoc p q r)

∨-idem : {P : Prog} (p : Pos P) → (p ∨ p ≡ p)
∨-idem (Bot P) = refl
∨-idem (Top P) = refl
∨-idem (Seqₗ p Q) = trans (∨-Seqₗ p p Q) (cong (λ p → Seqₗ p Q) (∨-idem p))
∨-idem (Seqᵣ P q) = trans (∨-Seqᵣ P q q) (cong (λ q → Seqᵣ P q) (∨-idem q))

∨-comm : {P : Prog} (p q : Pos P) → ((p ∨ q) ≡ (q ∨ p))
∨-comm (Bot P) (Bot .P) = refl
∨-comm (Bot P) (Top .P) = refl
∨-comm (Bot .(Seq _ Q)) (Seqₗ q Q) = refl
∨-comm (Bot .(Seq P _)) (Seqᵣ P q) = refl
∨-comm (Top P) (Bot .P) = refl
∨-comm (Top P) (Top .P) = refl
∨-comm (Top .(Seq _ Q)) (Seqₗ q Q) = refl
∨-comm (Top .(Seq P _)) (Seqᵣ P q) = refl
∨-comm (Seqₗ p Q) (Bot .(Seq _ Q)) = refl
∨-comm (Seqₗ p Q) (Top .(Seq _ Q)) = refl
∨-comm (Seqₗ p Q) (Seqₗ q .Q) = trans (∨-Seqₗ p q Q) (trans (cong (λ p → Seqₗ p Q) (∨-comm p q)) (sym (∨-Seqₗ q p Q)))
∨-comm (Seqₗ p Q) (Seqᵣ P q) = refl
∨-comm (Seqᵣ P p) (Bot .(Seq P _)) = refl
∨-comm (Seqᵣ P p) (Top .(Seq P _)) = refl
∨-comm (Seqᵣ P p) (Seqₗ q Q) = refl
∨-comm (Seqᵣ P p) (Seqᵣ .P q) = trans (∨-Seqᵣ P p q) (trans (cong (λ q → Seqᵣ P q) (∨-comm p q)) (sym (∨-Seqᵣ P q p)))

∨-bigger-l : {P : Prog} (p q : Pos P) → (p ≤ (p ∨ q))
∨-bigger-l (Bot P) q = ≤-Bot q
∨-bigger-l (Top P) (Bot .P) = ≤-refl (Top P)
∨-bigger-l (Top P) (Top .P) = ≤-refl (Top P)
∨-bigger-l (Top .(Seq _ Q)) (Seqₗ {P} q Q) = ≤-refl (Top (Seq P Q))
∨-bigger-l (Top .(Seq P _)) (Seqᵣ P {Q} q) = ≤-refl (Top (Seq P Q))
∨-bigger-l (Seqₗ p Q) (Bot .(Seq _ Q)) = ≤-refl (Seqₗ p Q)
∨-bigger-l (Seqₗ p Q) (Top .(Seq _ Q)) = ≤-Top (Seqₗ p Q)
∨-bigger-l (Seqₗ p Q) (Seqₗ q .Q) = ≤-Seqₗ (∨-bigger-l p q) Q
∨-bigger-l (Seqₗ p Q) (Seqᵣ P q) = ≤-Seqₗ-Seqᵣ p q
∨-bigger-l (Seqᵣ P p) (Bot .(Seq P _)) = ≤-refl (Seqᵣ P p)
∨-bigger-l (Seqᵣ P p) (Top .(Seq P _)) = ≤-Top (Seqᵣ P p)
∨-bigger-l (Seqᵣ P p) (Seqₗ q Q) = ≤-Seqᵣ P (≤-refl p)
∨-bigger-l (Seqᵣ P p) (Seqᵣ .P q) = ≤-Seqᵣ P (∨-bigger-l p q)

∨-bigger-r : {P : Prog} (p q : Pos P) → (q ≤ (p ∨ q))
∨-bigger-r p q = coe (cong (λ p → q ≤ p) (∨-comm q p)) (∨-bigger-l q p)

∨-↝-l : {P : Prog} {p p' : Pos P} → (p ↝ p') → (q : Pos P) → ((p ∨ q) ≤ (p' ∨ q))
∨-↝-l ↝-Act (Bot .Act) = ≤-step1 ↝-Act
∨-↝-l ↝-Act (Top .Act) = ≤-refl (Top Act)
∨-↝-l (↝-Seq₀ P Q) (Bot .(Seq P Q)) = ≤-step1 (↝-Seq₀ P Q)
∨-↝-l (↝-Seq₀ P Q) (Top .(Seq P Q)) = ≤-refl (Top (Seq P Q))
∨-↝-l (↝-Seq₀ P Q) (Seqₗ q .Q) = ≤-refl (Seqₗ q Q)
∨-↝-l (↝-Seq₀ P Q) (Seqᵣ .P q) = ≤-refl (Seqᵣ P q)
∨-↝-l (↝-Seqₗ {p' = p'} r Q) (Bot .(Seq _ Q)) = ≤-step1 (↝-Seqₗ r Q)
∨-↝-l (↝-Seqₗ {P} r Q) (Top .(Seq _ Q)) = ≤-refl (Top (Seq P Q))
∨-↝-l (↝-Seqₗ r Q) (Seqₗ q .Q) = ≤-Seqₗ (∨-↝-l r q) Q
∨-↝-l (↝-Seqₗ r Q) (Seqᵣ P q) = ≤-Seqᵣ P (≤-refl q)
∨-↝-l (↝-Seqₘ P Q) (Bot .(Seq P Q)) = ≤-step1 (↝-Seqₘ P Q)
∨-↝-l (↝-Seqₘ P Q) (Top .(Seq P Q)) = ≤-refl (Top (Seq P Q))
∨-↝-l (↝-Seqₘ P Q) (Seqₗ q .Q) = ≤-step1 (↝-Seqₘ P Q)
∨-↝-l (↝-Seqₘ P Q) (Seqᵣ .P q) = ≤-refl (Seqᵣ P q)
∨-↝-l (↝-Seqᵣ P {q' = q'} r) (Bot .(Seq P _)) = ≤-step1 (↝-Seqᵣ P r)
∨-↝-l (↝-Seqᵣ P {Q} r) (Top .(Seq P _)) = ≤-refl (Top (Seq P Q))
∨-↝-l (↝-Seqᵣ P {q' = q'} r) (Seqₗ q Q) = ≤-step1 (↝-Seqᵣ P r)
∨-↝-l (↝-Seqᵣ P r) (Seqᵣ .P q) = ≤-Seqᵣ P (∨-↝-l r q)
∨-↝-l (↝-Seq₁ P Q) (Bot .(Seq P Q)) = ≤-step1 (↝-Seq₁ P Q)
∨-↝-l (↝-Seq₁ P Q) (Top .(Seq P Q)) = ≤-refl (Top (Seq P Q))
∨-↝-l (↝-Seq₁ P Q) (Seqₗ q .Q) = ≤-step1 (↝-Seq₁ P Q)
∨-↝-l (↝-Seq₁ P Q) (Seqᵣ .P q) = ≤-step1 (↝-Seq₁ P Q)

∨-inc-l : {P : Prog} {p p' : Pos P} → (p ≤ p') → (q : Pos P) → ((p ∨ q) ≤ (p' ∨ q))
∨-inc-l (≤-step r l) q = ≤-trans (∨-↝-l r q) (∨-inc-l l q)
∨-inc-l (≤-refl p) q = ≤-refl (p ∨ q)

∨-inc-r : {P : Prog} (p q q' : Pos P) → (q ≤ q') → ((p ∨ q) ≤ (p ∨ q'))
∨-inc-r p q q' l =
  coe (cong (λ r → r ≤ (p ∨ q')) (∨-comm q p))
  (coe (cong (λ r → (q ∨ p) ≤ r) (∨-comm q' p))
  (∨-inc-l l p))

-- -- TODO: sup-lattice

-- --
-- -- Complements (TODO: better name, this is already taken) 
-- --

-- -- maximal elements not greater

-- open import Data.List
-- ¬≥ : {P : Prog} (p : Pos P) → List (Pos P)
-- ¬≥ (Bot P) = (Bot P) ∷ []
-- ¬≥ (Top P) = (Top P) ∷ []
-- ¬≥ (Seqₗ p Q) = map (λ p → Seqₗ p Q) (¬≥ p)
-- ¬≥ (Seqᵣ P q) = map (λ q → Seqᵣ P q) (¬≥ q)

data _¬>_ : {P : Prog} (p : Pos P) → (q : Pos P) → Set where
  ¬>-Bot : {P : Prog} → (Bot P) ¬> (Bot P)
  ¬>-Top : {P : Prog} → (Top P) ¬> (Top P)
  ¬>-Seqₗ : {P : Prog} {p p' : Pos P} → (p ¬> p') → (Q : Prog) → Seqₗ p Q ¬> Seqₗ p' Q
  ¬>-Seqᵣ : (P : Prog) {Q : Prog} {q q' : Pos P} → (q ¬> q') → Seqᵣ P q ¬> Seqᵣ P q'

¬>-sound : {P : Prog} {x : Pos P} {p q : Pos P} → (p ¬> q) → (x ≤ p) → (q ≤ x) → x ≡ q
¬>-sound ¬>-Bot l l' = ≤-asym l l'
¬>-sound ¬>-Top l l' = ≤-asym l l'
¬>-sound (¬>-Seqₗ {p' = p'} r Q) (≤-step (↝-Seq₀ P .Q) l) l' = {!⊥-elim (¬≤-Seqₗ-Bot l')!}
¬>-sound (¬>-Seqₗ r Q) (≤-step (↝-Seqₗ s .Q) l) l' = {!!}
¬>-sound (¬>-Seqₗ r Q) (≤-step (↝-Seqₘ P .Q) l) l' = {!!}
¬>-sound (¬>-Seqₗ r Q) (≤-step (↝-Seqᵣ P s) l) l' = {!!}
¬>-sound (¬>-Seqₗ r Q) (≤-step (↝-Seq₁ P .Q) l) l' = {!!}
¬>-sound (¬>-Seqₗ r Q) (≤-refl .(Seqₗ _ Q)) l' = ≤-asym {!!} l'
¬>-sound (¬>-Seqᵣ P r) l l' = {!!}

-- ¬>-sound {P} {x} {.(Bot P)} {.(Bot P)} ¬>-Bot l l' = ≤-Bot-≡ x l
-- ¬>-sound {P} {x} {.(Top P)} {.(Top P)} ¬>-Top l l' = ≤-Top-≡ x l'
-- ¬>-sound {.(Seq P Q)} {.(Bot (Seq P Q))} {.(Seqₗ (Bot P) Q)} {.(Seqₗ p' Q)} (¬>-Seqₗ {.P} {.(Bot P)} {p'} n Q) (≤-step (↝-Seq₀ P .Q)) (≤-step ())
-- ¬>-sound {.(Seq P Q)} {.(Bot (Seq P Q))} {.(Seqₗ (Bot P) Q)} {.(Seqₗ p' Q)} (¬>-Seqₗ {.P} {.(Bot P)} {p'} n Q) (≤-step (↝-Seq₀ P .Q)) (≤-trans {.(Seq P Q)} {.(Seqₗ p' Q)} {p''} {.(Bot (Seq P Q))} l' l'') = ¬>-sound (¬>-Seqₗ n Q) (≤-step (↝-Seq₀ P Q)) (transport (λ p'' → (Seqₗ p' Q ≤ p'')) (≤-Bot-≡ p'' l'') l')
-- ¬>-sound {.(Seq P Q)} {.(Seqₗ _ Q)} {.(Seqₗ p Q)} {.(Seqₗ p' Q)} (¬>-Seqₗ {P} {p} {p'} n Q) (≤-step (↝-Seqₗ r .Q)) l' = cong (λ p → Seqₗ p Q) {!!}
-- ¬>-sound {.(Seq P Q)} {.(Seqₗ p Q)} {.(Seqₗ p Q)} {.(Seqₗ p' Q)} (¬>-Seqₗ {P} {p} {p'} n Q) (≤-refl .(Seqₗ p Q)) l' = {!l'!}
-- ¬>-sound {.(Seq P Q)} {x} {.(Seqₗ p Q)} {.(Seqₗ p' Q)} (¬>-Seqₗ {P} {p} {p'} n Q) (≤-trans l l₁) l' = {!!}
-- ¬>-sound {.(Seq P P)} {x} {.(Seqᵣ P _)} {.(Seqᵣ P _)} (¬>-Seqᵣ P l1) l l' = {!!}

¬>-complete : {P : Prog} (p : Pos P) (x : Pos P) → (p ≤ x) or (∃[ p ] ((Pos P) and (x ≤ p)))
¬>-complete = {!!}
