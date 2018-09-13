open import Relation.Binary.PropositionalEquality

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
  ≤-step : {P : Prog} {p q : Pos P} → (p ↝ q) → p ≤ q
  ≤-refl : {P : Prog} (p : Pos P) → p ≤ p
  ≤-trans : {P : Prog} {p q r : Pos P} → (p ≤ q) → (q ≤ r) → p ≤ r

_≥_ : {P : Prog} (p : Pos P) (q : Pos P) → Set
p ≥ q = q ≤ p

≤-Seqₗ : {P : Prog} {p p' : Pos P} (l : p ≤ p') (Q : Prog) → Seqₗ p Q ≤ Seqₗ p' Q
≤-Seqₗ (≤-step l) Q = ≤-step (↝-Seqₗ l Q)
≤-Seqₗ (≤-refl p) Q = ≤-refl (Seqₗ p Q)
≤-Seqₗ (≤-trans l l') Q = ≤-trans (≤-Seqₗ l Q) (≤-Seqₗ l' Q)

-- ≤-Seqₗ' : 

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

---
--- Inversion lemmas
---

{-# TERMINATING #-}
≤-Bot-≡ : {P : Prog} {p : Pos P} → (p ≤ Bot P) → (p ≡ Bot P)
≤-Bot-≡ (≤-step ())
≤-Bot-≡ (≤-refl .(Bot _)) = refl
≤-Bot-≡ {P} {p} (≤-trans {_} {.p} {q} {.(Bot P)} l l') = ≤-Bot-≡ (transport (λ q → p ≤ q) (≤-Bot-≡ l') l)

{-# TERMINATING #-}
≤-Top-≡ : {P : Prog} {p : Pos P} → (Top P ≤ p) → (p ≡ Top P)
≤-Top-≡ (≤-step ())
≤-Top-≡ (≤-refl .(Top _)) = refl
≤-Top-≡ {P} {q} (≤-trans {_} {.(Top P)} {p} {.q} l l') = ≤-Top-≡ (transport (λ p → p ≤ q) (≤-Top-≡ l) l')

≤-asym : {P : Prog} {p q : Pos P} → (p ≤ q) → (q ≤ p) → p ≡ q
≤-asym {.Act} {.(Bot Act)} {q} (≤-step ↝-Act) l' = ≡-sym (≤-Bot-≡ l')
≤-asym {.(Seq P Q)} {.(Bot (Seq P Q))} {q} (≤-step (↝-Seq₀ P Q)) l' = ≡-sym (≤-Bot-≡ l')
≤-asym {.(Seq _ Q)} {.(Seqₗ _ Q)} {.(Seqₗ _ Q)} (≤-step (↝-Seqₗ x Q)) l' = {!l'!}
≤-asym {.(Seq P Q)} {.(Seqₗ (Top P) Q)} {.(Seqᵣ P (Bot Q))} (≤-step (↝-Seqₘ P Q)) l' = {!!}
≤-asym {.(Seq P _)} {.(Seqᵣ P _)} {.(Seqᵣ P _)} (≤-step (↝-Seqᵣ P x)) l' = {!!}
≤-asym {.(Seq P Q)} {.(Seqᵣ P (Top Q))} {.(Top (Seq P Q))} (≤-step (↝-Seq₁ P Q)) l' = {!!}
≤-asym {P} {.p} {.p} (≤-refl p) l' = {!!}
≤-asym {P} {p} {q} (≤-trans l l₁) l' = {!!}

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

∨-inc-l : {P : Prog} (p p' q : Pos P) → (p ≤ p') → ((p ∨ q) ≤ (p' ∨ q))
∨-inc-l .(Bot Act) .(Top Act) q (≤-step ↝-Act) = ≤-Top q
∨-inc-l .(Bot (Seq P Q)) .(Seqₗ (Bot P) Q) (Bot .(Seq P Q)) (≤-step (↝-Seq₀ P Q)) = ≤-step (↝-Seq₀ P Q)
∨-inc-l .(Bot (Seq P Q)) .(Seqₗ (Bot P) Q) (Top .(Seq P Q)) (≤-step (↝-Seq₀ P Q)) = ≤-refl (Top (Seq P Q))
∨-inc-l .(Bot (Seq P Q)) .(Seqₗ (Bot P) Q) (Seqₗ q .Q) (≤-step (↝-Seq₀ P Q)) = ≤-refl (Seqₗ q Q)
∨-inc-l .(Bot (Seq P Q)) .(Seqₗ (Bot P) Q) (Seqᵣ .P q) (≤-step (↝-Seq₀ P Q)) = ≤-refl (Seqᵣ P q)
∨-inc-l .(Seqₗ _ Q) .(Seqₗ _ Q) (Bot .(Seq _ Q)) (≤-step (↝-Seqₗ x Q)) = ≤-step (↝-Seqₗ x Q)
∨-inc-l .(Seqₗ _ Q) .(Seqₗ _ Q) (Top .(Seq _ Q)) (≤-step (↝-Seqₗ {P} x Q)) = ≤-refl (Top (Seq P Q))
∨-inc-l .(Seqₗ _ Q) .(Seqₗ _ Q) (Seqₗ q .Q) (≤-step (↝-Seqₗ {P} {p} {p'} l Q)) = ≤-Seqₗ (∨-inc-l p p' q (≤-step l)) Q
∨-inc-l .(Seqₗ _ Q) .(Seqₗ _ Q) (Seqᵣ P q) (≤-step (↝-Seqₗ x Q)) = ≤-refl (Seqᵣ P q)
∨-inc-l .(Seqₗ (Top P) Q) .(Seqᵣ P (Bot Q)) (Bot .(Seq P Q)) (≤-step (↝-Seqₘ P Q)) = ≤-step (↝-Seqₘ P Q)
∨-inc-l .(Seqₗ (Top P) Q) .(Seqᵣ P (Bot Q)) (Top .(Seq P Q)) (≤-step (↝-Seqₘ P Q)) = ≤-refl (Top (Seq P Q))
∨-inc-l .(Seqₗ (Top P) Q) .(Seqᵣ P (Bot Q)) (Seqₗ q .Q) (≤-step (↝-Seqₘ P Q)) = ≤-step (↝-Seqₘ P Q)
∨-inc-l .(Seqₗ (Top P) Q) .(Seqᵣ P (Bot Q)) (Seqᵣ .P q) (≤-step (↝-Seqₘ P Q)) = ≤-refl (Seqᵣ P q)
∨-inc-l .(Seqᵣ P _) .(Seqᵣ P _) (Bot .(Seq P _)) (≤-step (↝-Seqᵣ P x)) = ≤-step (↝-Seqᵣ P x)
∨-inc-l .(Seqᵣ P _) .(Seqᵣ P _) (Top .(Seq P _)) (≤-step (↝-Seqᵣ P {Q} {q} {q'} l)) = ≤-refl (Top (Seq P Q))
∨-inc-l .(Seqᵣ P _) .(Seqᵣ P _) (Seqₗ q Q) (≤-step (↝-Seqᵣ P x)) = ≤-step (↝-Seqᵣ P x)
∨-inc-l .(Seqᵣ P _) .(Seqᵣ P _) (Seqᵣ .P p) (≤-step (↝-Seqᵣ P {Q} {q} {q'} l)) = ≤-Seqᵣ P (∨-inc-l q q' p (≤-step l))
∨-inc-l .(Seqᵣ P (Top Q)) .(Top (Seq P Q)) q (≤-step (↝-Seq₁ P Q)) = ≤-Top (Seqᵣ P (Top Q) ∨ q)
∨-inc-l p .p q (≤-refl .p) = ≤-refl (p ∨ q)
∨-inc-l p p' q (≤-trans {_} {.p} {p''} l l') = ≤-trans (∨-inc-l p p'' q l) (∨-inc-l p'' p' q l')

∨-inc-r : {P : Prog} (p q q' : Pos P) → (q ≤ q') → ((p ∨ q) ≤ (p ∨ q'))
∨-inc-r p q q' l =
  coe (cong (λ r → r ≤ (p ∨ q')) (∨-comm q p))
  (coe (cong (λ r → (q ∨ p) ≤ r) (∨-comm q' p))
  (∨-inc-l q q' p l))

-- TODO: sup-lattice

--
-- Complements (TODO: better name, this is already taken) 
--

-- maximal elements not greater

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

{-# TERMINATING #-}
¬>-sound : {P : Prog} {x : Pos P} {p q : Pos P} → (p ¬> q) → (x ≤ p) → (q ≤ x) → x ≡ q
¬>-sound {P} {x} {.(Bot P)} {.(Bot P)} ¬>-Bot l l' = ≤-Bot-≡ l
¬>-sound {P} {x} {.(Top P)} {.(Top P)} ¬>-Top l l' = ≤-Top-≡ l'
¬>-sound {.(Seq P Q)} {.(Bot (Seq P Q))} {.(Seqₗ (Bot P) Q)} {.(Seqₗ p' Q)} (¬>-Seqₗ {.P} {.(Bot P)} {p'} n Q) (≤-step (↝-Seq₀ P .Q)) (≤-step ())
¬>-sound {.(Seq P Q)} {.(Bot (Seq P Q))} {.(Seqₗ (Bot P) Q)} {.(Seqₗ p' Q)} (¬>-Seqₗ {.P} {.(Bot P)} {p'} n Q) (≤-step (↝-Seq₀ P .Q)) (≤-trans {.(Seq P Q)} {.(Seqₗ p' Q)} {p''} {.(Bot (Seq P Q))} l' l'') = ¬>-sound (¬>-Seqₗ n Q) (≤-step (↝-Seq₀ P Q)) (transport (λ p'' → (Seqₗ p' Q ≤ p'')) (≤-Bot-≡ l'') l')
¬>-sound {.(Seq P Q)} {.(Seqₗ _ Q)} {.(Seqₗ p Q)} {.(Seqₗ p' Q)} (¬>-Seqₗ {P} {p} {p'} n Q) (≤-step (↝-Seqₗ r .Q)) l' = cong (λ p → Seqₗ p Q) {!!}
¬>-sound {.(Seq P Q)} {.(Seqₗ p Q)} {.(Seqₗ p Q)} {.(Seqₗ p' Q)} (¬>-Seqₗ {P} {p} {p'} n Q) (≤-refl .(Seqₗ p Q)) l' = {!l'!}
¬>-sound {.(Seq P Q)} {x} {.(Seqₗ p Q)} {.(Seqₗ p' Q)} (¬>-Seqₗ {P} {p} {p'} n Q) (≤-trans l l₁) l' = {!!}
¬>-sound {.(Seq P P)} {x} {.(Seqᵣ P _)} {.(Seqᵣ P _)} (¬>-Seqᵣ P l1) l l' = {!!}

¬>-complete : {P : Prog} (p : Pos P) (x : Pos P) → (p ≤ x) or (∃[ p ] ((Pos P) and (x ≤ p)))
¬>-complete = {!!}
