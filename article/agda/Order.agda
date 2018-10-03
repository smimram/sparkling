{-# OPTIONS --allow-unsolved-metas #-}

module Order where

open import Equality
open import Function using ( case_of_ )
open import Relation.Binary using ( Decidable )
open import Relation.Nullary using ( yes ; no )
open import Relation.Binary.PropositionalEquality
open import Data.Empty
open import Data.Product
open import Data.Sum
open import Data.Nat.Base renaming (_≤_ to _≤ℕ_ ; _<_ to _<ℕ_ ; _≟_ to _≟ℕ_) hiding (_≥_)
open import Data.Nat.Properties renaming (≤-refl to ≤ℕ-refl ; ≤-trans to ≤ℕ-trans ; ≤-antisym to ≤ℕ-antisym) hiding (≤-step)
open import Program

data _≤_ : {P : Prog} (p : Pos P) (q : Pos P) → Set where
  ≤-step : {P : Prog} {p q r : Pos P} (s : p ↝ q) (l : q ≤ r) → p ≤ r
  ≤-refl : {P : Prog} (p : Pos P) → p ≤ p

data _≤W_ : {P : Prog} → (ℕ × Pos P) → (ℕ × Pos P) → Set where
  ≤W-zz : {P : Prog} {p p' : Pos P} (l : p ≤ p') → (zero , p) ≤W (zero , p')
  ≤W-zs : {P : Prog} (n' : ℕ) (p p' : Pos P) → (zero , p) ≤W (suc n' , p')
  ≤W-ss : {P : Prog} {n n' : ℕ} {p p' : Pos P} → (n , p) ≤W (n' , p') → (suc n , p) ≤W (suc n' , p')

_<_ : {P : Prog} (p : Pos P) (q : Pos P) → Set
p < q = ∃[ p' ] ((p ↝ p') × (p' ≤ q))

_≥_ : {P : Prog} (p : Pos P) (q : Pos P) → Set
p ≥ q = q ≤ p

≤W-nn : {P : Prog} → (n : ℕ) → {p p' : Pos P} → p ≤ p' → (n , p) ≤W (n , p')
≤W-nn zero l = ≤W-zz l
≤W-nn (suc n) l = ≤W-ss (≤W-nn n l)

≤W-elim : {P : Prog} {n n' : ℕ} {p p' : Pos P} → ((n , p) ≤W (n' , p')) → ((n ≡ n') × p ≤ p') ⊎ (n <ℕ n')
≤W-elim (≤W-zz l) = inj₁ (refl , l)
≤W-elim (≤W-zs n' p p') = inj₂ (s≤s z≤n)
≤W-elim (≤W-ss l) with ≤W-elim l
≤W-elim (≤W-ss _) | inj₁ (e , l) = inj₁ (cong suc e , l)
≤W-elim (≤W-ss _) | inj₂ l = inj₂ (s≤s l)

≤W-refl : {P : Prog} (np : ℕ × Pos P) → np ≤W np
≤W-refl (zero , p) = ≤W-zz (≤-refl p)
≤W-refl (suc n , p) = ≤W-ss (≤W-refl (n , p))

≤-≤W : {P : Prog} → (n : ℕ) → {p p' : Pos P} → (p ≤ p') → (n , p) ≤W (n , p')
≤-≤W zero l = ≤W-zz l
≤-≤W (suc n) l = ≤W-ss (≤-≤W n l)

<ℕ-≤W : {P : Prog} {n n' : ℕ} → (n <ℕ n') → (p q : Pos P) → (n , p) ≤W (n' , q)
<ℕ-≤W {n = zero} {zero} () p q
<ℕ-≤W {n = zero} {suc n'} l p q = ≤W-zs n' p q
<ℕ-≤W {n = suc n} {.(suc (suc _))} (s≤s (s≤s l)) p q = ≤W-ss (<ℕ-≤W (s≤s l) p q)

≤W-≤ℕ : {P : Prog} {n n' : ℕ} → {p q : Pos P} → (n , p) ≤W (n' , q) → n ≤ℕ n'
≤W-≤ℕ (≤W-zz l) = z≤n
≤W-≤ℕ (≤W-zs n' p p') = z≤n
≤W-≤ℕ (≤W-ss l) = s≤s (≤W-≤ℕ l)

≤W-≤ : {P : Prog} {n : ℕ} {p p' : Pos P} → (n , p) ≤W (n , p') → p ≤ p'
≤W-≤ (≤W-zz l) = l
≤W-≤ (≤W-ss l) = ≤W-≤ l

≡-≤W : {P : Prog} {np np' : ℕ × Pos P} → np ≡ np' → np ≤W np'
≡-≤W {_} {np} refl = ≤W-refl np

≡-≤W' : {P : Prog} {n n' : ℕ} {p p' : Pos P} → n ≡ n' → p ≡ p' → (n , p) ≤W (n' , p')
≡-≤W' {n = n} {p = p} refl refl = ≤W-refl (n , p)

≡-≤ : {P : Prog} {p q : Pos P} → (p ≡ q) → p ≤ q
≡-≤ {P} {p} {q} l = transport (λ q → p ≤ q) l (≤-refl p)

≤-trans : {P : Prog} {p q r : Pos P} → (p ≤ q) → (q ≤ r) → (p ≤ r)
≤-trans (≤-step r l) l' = ≤-step r (≤-trans l l')
≤-trans (≤-refl p) l' = l'

≤W-trans : {P : Prog} {np np' np'' : ℕ × Pos P} → np ≤W np' → np' ≤W np'' → np ≤W np''
≤W-trans {np = .0 , p} {.0 , p'} {.0 , p''} (≤W-zz l) (≤W-zz l') = ≤W-zz (≤-trans l l')
≤W-trans {np = .0 , p} {.0 , p'} {.(suc n') , p''} (≤W-zz l) (≤W-zs n' .p' .p'') = ≤W-zs n' p p''
≤W-trans {np = .0 , p} {.(suc n') , p'} {.(suc _) , p''} (≤W-zs n' .p .p') (≤W-ss {n' = n₁} l') = ≤W-zs n₁ p p''
≤W-trans {np = .(suc _) , p} {.(suc _) , p'} {.(suc _) , p''} (≤W-ss l) (≤W-ss l') = ≤W-ss (≤W-trans l l')

≤W-intro : {P : Prog} {n n' : ℕ} {p p' : Pos P} → ((n ≡ n') × p ≤ p') ⊎ (n <ℕ n') → ((n , p) ≤W (n' , p'))
≤W-intro {n' = n'} (inj₁ (e , l)) = ≤W-trans (≡-≤W' e refl) (≤-≤W n' l)
≤W-intro {p = p} {p'} (inj₂ l) = <ℕ-≤W l p p'

≤-step1 : {P : Prog} {p q : Pos P} → (p ↝ q) → (p ≤ q)
≤-step1 {_} {_} {q} r = ≤-step r (≤-refl q)

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

≤-Whileₚ : {P : Prog} {n : ℕ} {p p' : Pos P} (l : p ≤ p') → While (n , p) ≤ While (n , p')
≤-Whileₚ {n = n} (≤-step s l) = ≤-step (↝-While n s) (≤-Whileₚ l)
≤-Whileₚ {n = n} (≤-refl p) = ≤-refl (While (n , p))

≤-Bot : {P : Prog} (p : Pos P) → (Bot P ≤ p)
≤-Top : {P : Prog} (p : Pos P) → (p ≤ Top P)
≤-Bot (Bot P) = ≤-refl (Bot P)
≤-Bot (Top Act) = ≤-step1 ↝-Act
≤-Bot (Top (Seq P Q)) =
  ≤-step (↝-Seq₀ P Q)
  (≤-trans (≤-Seqₗ (≤-Bot (Top P)) Q)
  (≤-step (↝-Seqₘ P Q)
  (≤-trans (≤-Seqᵣ P (≤-Bot (Top Q)))
  (≤-step1 (↝-Seq₁ P Q)))))
≤-Bot (Top (If P Q)) =
  ≤-step (↝-If₀ₗ P Q)
  (≤-trans (≤-Ifₗ (≤-Bot (Top P)) Q)
  (≤-step1 (↝-If₁ₗ P Q)))
≤-Bot (Top (While P)) = ≤-step1 (↝-While₀' P)
≤-Bot (Seqₗ {P} p Q) = ≤-step (↝-Seq₀ P Q) (≤-Seqₗ (≤-Bot p) Q)
≤-Bot (Seqᵣ P {Q} q) =
  ≤-step (↝-Seq₀ P Q)
  (≤-trans (≤-Seqₗ (≤-Bot (Top P)) Q)
  (≤-step (↝-Seqₘ P Q)
  (≤-Seqᵣ P (≤-Bot q))))
≤-Bot (Ifₗ {P} p Q) = ≤-step (↝-If₀ₗ P Q) (≤-Ifₗ (≤-Bot p) Q)
≤-Bot (Ifᵣ P {Q} q) = ≤-step (↝-If₀ᵣ P Q) (≤-Ifᵣ P (≤-Bot q))
≤-Bot (While {P} (zero , p)) = ≤-step (↝-While₀ P) (≤-Whileₚ (≤-Bot p))
≤-Bot (While {P} (suc n , p)) =
  ≤-trans
  (≤-Bot (While (n , p)))
  (≤-trans (≤-Whileₚ (≤-Top p))
  (≤-step (↝-While₁ P n)
  (≤-Whileₚ (≤-Bot p))))

≤-Top (Bot P) = ≤-Bot (Top P)
≤-Top (Top P) = ≤-refl (Top P)
≤-Top (Seqₗ {P} p Q) =
  ≤-trans (≤-Seqₗ (≤-Top p) Q)
  (≤-step (↝-Seqₘ P Q)
  (≤-trans (≤-Seqᵣ P (≤-Top (Bot Q)))
  (≤-step1 (↝-Seq₁ P Q))))
≤-Top (Seqᵣ P {Q} q) = ≤-trans (≤-Seqᵣ P (≤-Top q)) (≤-step1 (↝-Seq₁ P Q))
≤-Top (Ifₗ {P} p Q) = ≤-trans (≤-Ifₗ (≤-Top p) Q) (≤-step1 (↝-If₁ₗ P Q))
≤-Top (Ifᵣ P {Q} q) = ≤-trans (≤-Ifᵣ P (≤-Top q)) (≤-step1 (↝-If₁ᵣ P Q))
≤-Top (While {P} (n , p)) = ≤-trans (≤-Whileₚ (≤-Top p)) (≤-step1 (↝-While₁' P n))

ℕ-rec-from : (P : ℕ → Set) (n : ℕ) (P₀ : P n) (Pᵢ : (n : ℕ) → P n → P (suc n)) → (m : ℕ) → (n ≤ℕ m) → P m
ℕ-rec-from P zero P₀ Pᵢ zero x = P₀
ℕ-rec-from P zero P₀ Pᵢ (suc m) x = ℕ-rec-from (λ z → P (suc z)) zero (Pᵢ zero P₀) (λ n → Pᵢ (suc n)) m z≤n
ℕ-rec-from P (suc n) P₀ Pᵢ zero ()
ℕ-rec-from P (suc n) P₀ Pᵢ (suc m) (s≤s l) = ℕ-rec-from (λ z → P (suc z)) n P₀ (λ n₁ → Pᵢ (suc n₁)) m l

≤-Whileₙ : {P : Prog} {n n' : ℕ} → (n ≤ℕ n') → (p : Pos P) → While (n , p) ≤ While (n' , p)
≤-Whileₙ {P} {n} {n'} l p =
  ℕ-rec-from (λ n' → While (n , p) ≤ While (n' , p)) n (≤-refl (While (n , p)))
  ( λ m l → ≤-trans l (≤-trans (≤-Whileₚ (≤-Top p)) (≤-step (↝-While₁ P m) (≤-Whileₚ (≤-Bot p)))) )
  n' l

≤-Whileₙ' : {P : Prog} {n n' : ℕ} → (suc n ≤ℕ n') → (p p' : Pos P) → While (n , p) ≤ While (n' , p')
≤-Whileₙ' {P} {n} {n'} l p p' =
  ℕ-rec-from (λ n' → While (n , p) ≤ While (n' , p')) (suc n)
  (≤-trans (≤-Whileₚ (≤-Top p)) (≤-step (↝-While₁ P n) (≤-Whileₚ (≤-Bot p'))))
  (λ m l → ≤-trans l (≤-trans (≤-Whileₚ (≤-Top p')) (≤-step (↝-While₁ P m) (≤-Whileₚ (≤-Bot p')))))
  n' l

≤-While : {P : Prog} {n n' : ℕ} {p p' : Pos P} → ((n , p) ≤W (n' , p')) → While (n , p) ≤ While (n' , p')
≤-While l with ≤W-elim l
≤-While {_} {n} {n'} {p} {p'} _ | inj₁ (e , l) = transport (λ n' → While (n , p) ≤ While (n' , p')) e (≤-Whileₚ l)
≤-While {p = p} {p' = p'} _ | inj₂ l = ≤-Whileₙ' l p p'

≤-Seqₗ-Seqᵣ : {P Q : Prog} (p : Pos P) (q : Pos Q) → (Seqₗ p Q ≤ Seqᵣ P q)
≤-Seqₗ-Seqᵣ {P} {Q} p q =
  ≤-trans (≤-Seqₗ (≤-Top p) Q)
  (≤-step (↝-Seqₘ P Q)
  (≤-Seqᵣ P (≤-Bot q)))

---
--- Inversion lemmas
---

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

¬≤-Ifₗ-Bot : {P Q : Prog} {p : Pos P} → Ifₗ p Q ≤ Bot (If P Q) → ⊥
¬≤-Ifₗ-Bot (≤-step (↝-Ifₗ r Q) l) = ¬≤-Ifₗ-Bot l
¬≤-Ifₗ-Bot (≤-step (↝-If₁ₗ P Q) l) = ¬≤-Top-Bot l

¬≤-Top-Ifₗ : {P Q : Prog} {p : Pos P} → Top (If P Q) ≤ Ifₗ p Q → ⊥
¬≤-Top-Ifₗ (≤-step () l)

¬≤-Top-Ifᵣ : {P Q : Prog} {q : Pos Q} → Top (If P Q) ≤ Ifᵣ P q → ⊥
¬≤-Top-Ifᵣ (≤-step () l)

¬≤-Ifₗ-Ifᵣ : {P Q : Prog} {p : Pos P} {q : Pos Q} → Ifₗ p Q ≤ Ifᵣ P q → ⊥
¬≤-Ifₗ-Ifᵣ (≤-step (↝-Ifₗ x Q) l) = ¬≤-Ifₗ-Ifᵣ l
¬≤-Ifₗ-Ifᵣ (≤-step (↝-If₁ₗ P Q) l) = ¬≤-Top-Ifᵣ l

¬≤-Ifᵣ-Ifₗ : {P Q : Prog} {p : Pos P} {q : Pos Q} → Ifᵣ P q ≤ Ifₗ p Q → ⊥
¬≤-Ifᵣ-Ifₗ (≤-step (↝-Ifᵣ P s) l) = ¬≤-Ifᵣ-Ifₗ l
¬≤-Ifᵣ-Ifₗ (≤-step (↝-If₁ᵣ P Q) l) = ¬≤-Top-Ifₗ l

¬≤-Ifᵣ-Bot : {P Q : Prog} {q : Pos Q} → Ifᵣ P q ≤ Bot (If P Q) → ⊥
¬≤-Ifᵣ-Bot (≤-step (↝-Ifᵣ P s) l) = ¬≤-Ifᵣ-Bot l
¬≤-Ifᵣ-Bot (≤-step (↝-If₁ᵣ P Q) l) = ¬≤-Top-Bot l

¬≤-While-Bot : {P : Prog} {n : ℕ} {p : Pos P} → While (n , p) ≤ Bot (While P) → ⊥
¬≤-While-Bot (≤-step (↝-While n s) l) = ¬≤-While-Bot l
¬≤-While-Bot (≤-step (↝-While₁ P n) l) = ¬≤-While-Bot l
¬≤-While-Bot (≤-step (↝-While₁' P n) l) = ¬≤-Top-Bot l

¬≤-Top-While : {P : Prog} {n : ℕ} {p : Pos P} → Top (While P) ≤ While (n , p) → ⊥
¬≤-Top-While (≤-step () l)

≤-While-suc : {P : Prog} {n n' : ℕ} → {p p' : Pos P} → While (n , p) ≤ While (n' , p') → While (suc n , p) ≤ While (suc n' , p')
≤-While-suc (≤-step (↝-While n s) l) = ≤-step (↝-While (suc n) s) (≤-While-suc l)
≤-While-suc (≤-step (↝-While₁ P n) l) = ≤-step (↝-While₁ P (suc n)) (≤-While-suc l)
≤-While-suc (≤-step (↝-While₁' P n) l) = ⊥-elim (¬≤-Top-While l)
≤-While-suc {P} {n} {.n} {p} {.p} (≤-refl .(While (n , p))) = ≤-refl (While (suc n , p))

≤-While-elim : {P : Prog} {n n' : ℕ} {p p' : Pos P} → (While (n , p) ≤ While (n' , p')) → (n , p) ≤W (n' , p')
≤-While-elim (≤-step (↝-While n s) l) = ≤W-trans (≤-≤W n (≤-step1 s)) (≤-While-elim l)
≤-While-elim (≤-step (↝-While₁ P n) l) = ≤W-trans (<ℕ-≤W (s≤s ≤ℕ-refl) (Top P) (Bot P)) (≤-While-elim l)
≤-While-elim (≤-step (↝-While₁' P n) l) = ⊥-elim (¬≤-Top-While l)
≤-While-elim {n = n} {p = p} (≤-refl .(While (_ , _))) = ≤W-refl (n , p)

≤-While-elimₙ : {P : Prog} {n n' : ℕ} {p p' : Pos P} → (While (n , p) ≤ While (n' , p')) → n ≤ℕ n'
≤-While-elimₙ l = ≤W-≤ℕ (≤-While-elim l)

≤-While-elimₚ : {P : Prog} {n : ℕ} {p p' : Pos P} → (While (n , p) ≤ While (n , p')) → p ≤ p'
≤-While-elimₚ l = {!!}

≤-Seqₗ' : {P : Prog} {p p' : Pos P} {Q : Prog} → Seqₗ p Q ≤ Seqₗ p' Q → p ≤ p'
≤-Seqₗ' (≤-step (↝-Seqₗ r Q) l) = ≤-step r (≤-Seqₗ' l)
≤-Seqₗ' {_} {.(Top P)} {p'} (≤-step (↝-Seqₘ P Q) l) = ⊥-elim (¬≤-Seqᵣ-Seqₗ l)
≤-Seqₗ' {_} {p} (≤-refl .(Seqₗ _ _)) = ≤-refl p

≤-Seqᵣ' : {P : Prog} {Q : Prog} {q q' : Pos Q} → Seqᵣ P q ≤ Seqᵣ P q' → q ≤ q'
≤-Seqᵣ' (≤-step (↝-Seqᵣ P r) l) = ≤-step r (≤-Seqᵣ' l)
≤-Seqᵣ' (≤-step (↝-Seq₁ P Q) l) = ⊥-elim (¬≤-Top-Seqᵣ l)
≤-Seqᵣ' {q = q} (≤-refl .(Seqᵣ _ _)) = ≤-refl q

≤-Ifₗ' : {P : Prog} {p p' : Pos P} {Q : Prog} → Ifₗ p Q ≤ Ifₗ p' Q → p ≤ p'
≤-Ifₗ' (≤-step (↝-Ifₗ r Q) l) = ≤-step r (≤-Ifₗ' l)
≤-Ifₗ' (≤-step (↝-If₁ₗ P Q) l) = ⊥-elim (¬≤-Top-Ifₗ l)
≤-Ifₗ' {p = p} (≤-refl .(Ifₗ _ _)) = ≤-refl p

≤-Ifᵣ' : {P : Prog} {Q : Prog} {q q' : Pos Q} → Ifᵣ P q ≤ Ifᵣ P q' → q ≤ q'
≤-Ifᵣ' (≤-step (↝-Ifᵣ P s) l) = ≤-step s (≤-Ifᵣ' l)
≤-Ifᵣ' (≤-step (↝-If₁ᵣ P Q) l) = ⊥-elim (¬≤-Top-Ifᵣ l)
≤-Ifᵣ' {q = q} (≤-refl .(Ifᵣ _ _)) = ≤-refl q

≤-Bot-≡ : {P : Prog} {p : Pos P} → (p ≤ Bot P) → (p ≡ Bot P)
≤-Bot-≡ (≤-step ↝-Act l) = refl
≤-Bot-≡ (≤-step (↝-Seq₀ P Q) l) = refl
≤-Bot-≡ (≤-step (↝-Seqₗ x Q) l) = case ≤-Bot-≡ l of λ()
≤-Bot-≡ (≤-step (↝-Seqₘ P Q) l) = case ≤-Bot-≡ l of λ()
≤-Bot-≡ (≤-step (↝-Seqᵣ P x) l) = case ≤-Bot-≡ l of λ()
≤-Bot-≡ (≤-step (↝-Seq₁ P Q) l) = case ≤-Bot-≡ l of λ()
≤-Bot-≡ (≤-step (↝-If₀ₗ P Q) l) = case ≤-Bot-≡ l of λ()
≤-Bot-≡ (≤-step (↝-Ifₗ x Q) l) = case ≤-Bot-≡ l of λ()
≤-Bot-≡ (≤-step (↝-If₁ₗ P Q) l) = case ≤-Bot-≡ l of λ()
≤-Bot-≡ (≤-step (↝-If₀ᵣ P Q) l) = case ≤-Bot-≡ l of λ()
≤-Bot-≡ (≤-step (↝-Ifᵣ P x) l) = case ≤-Bot-≡ l of λ()
≤-Bot-≡ (≤-step (↝-If₁ᵣ P Q) l) = case ≤-Bot-≡ l of λ()
≤-Bot-≡ (≤-step (↝-While₀ P) l) = case ≤-Bot-≡ l of λ()
≤-Bot-≡ (≤-step (↝-While₀' P) l) = case ≤-Bot-≡ l of λ()
≤-Bot-≡ (≤-step (↝-While n x) l) = case ≤-Bot-≡ l of λ()
≤-Bot-≡ (≤-step (↝-While₁ P n) l) = case ≤-Bot-≡ l of λ()
≤-Bot-≡ (≤-step (↝-While₁' P n) l) = case ≤-Bot-≡ l of λ()
≤-Bot-≡ (≤-refl .(Bot _)) = refl

≤-Top-≡ : {P : Prog} (p : Pos P) → (Top P ≤ p) → (p ≡ Top P)
≤-Top-≡ p (≤-step () l)
≤-Top-≡ .(Top _) (≤-refl .(Top _)) = refl

≤-antisym : {P : Prog} {p q : Pos P} → (p ≤ q) → (q ≤ p) → p ≡ q
≤-antisym (≤-step ↝-Act l) (≤-step ↝-Act l') = refl
≤-antisym (≤-step ↝-Act l) (≤-refl .(Bot Act)) = refl
≤-antisym (≤-step (↝-Seq₀ P Q) l) (≤-step (↝-Seq₀ .P .Q) l') = refl
≤-antisym (≤-step (↝-Seq₀ P Q) l) (≤-step (↝-Seqₗ x .Q) l') = ⊥-elim (¬≤-Seqₗ-Bot l')
≤-antisym (≤-step (↝-Seq₀ P Q) l) (≤-step (↝-Seqₘ .P .Q) l') = ⊥-elim (¬≤-Seqᵣ-Bot l')
≤-antisym (≤-step (↝-Seq₀ P Q) l) (≤-step (↝-Seqᵣ .P x) l') =  ⊥-elim (¬≤-Seqᵣ-Bot l')
≤-antisym (≤-step (↝-Seq₀ P Q) l) (≤-step (↝-Seq₁ .P .Q) l') = ⊥-elim (¬≤-Top-Bot l')
≤-antisym (≤-step (↝-Seq₀ P Q) l) (≤-refl .(Bot (Seq P Q))) = refl
≤-antisym (≤-step (↝-Seqₗ p Q) l) (≤-step (↝-Seq₀ P .Q) l') = ⊥-elim (¬≤-Seqₗ-Bot l)
≤-antisym (≤-step (↝-Seqₗ p Q) l) (≤-step (↝-Seqₗ p' .Q) l') = cong (λ p → Seqₗ p Q) (≤-antisym (≤-step p (≤-Seqₗ' l)) (≤-step p' (≤-Seqₗ' l')))
≤-antisym (≤-step (↝-Seqₗ p Q) l) (≤-step (↝-Seqₘ P .Q) l') = {!!}
≤-antisym (≤-step (↝-Seqₗ p Q) l) (≤-step (↝-Seqᵣ P q) l') = {!!}
≤-antisym (≤-step (↝-Seqₗ p Q) l) (≤-step (↝-Seq₁ P .Q) l') = {!!}
≤-antisym (≤-step (↝-Seqₗ p Q) l) (≤-refl .(Seqₗ _ Q)) = refl
≤-antisym (≤-step (↝-Seqₘ P Q) l) l' = {!!}
≤-antisym (≤-step (↝-Seqᵣ P x) l) l' = {!!}
≤-antisym (≤-step (↝-Seq₁ P Q) l) l' = {!!}
≤-antisym (≤-step (↝-If₀ₗ P Q) l) l' = {!!}
≤-antisym (≤-step (↝-Ifₗ x Q) l) l' = {!!}
≤-antisym (≤-step (↝-If₁ₗ P Q) l) l' = {!!}
≤-antisym (≤-step (↝-If₀ᵣ P Q) l) l' = {!!}
≤-antisym (≤-step (↝-Ifᵣ P x) l) l' = {!!}
≤-antisym (≤-step (↝-If₁ᵣ P Q) l) l' = {!!}
≤-antisym (≤-step (↝-While₀ P) l) l' = {!!}
≤-antisym (≤-step (↝-While₀' P) l) l' = {!!}
≤-antisym (≤-step (↝-While n x) l) l' = {!!}
≤-antisym (≤-step (↝-While₁ P n) l) l' = {!!}
≤-antisym (≤-step (↝-While₁' P n) l) l' = {!!}
≤-antisym (≤-refl p) l' = refl

≤-dec : {P : Prog} → Decidable (_≤_ {P})
≤-dec (Bot P) q = yes (≤-Bot q)
≤-dec (Top P) (Bot .P) = no ¬≤-Top-Bot
≤-dec (Top P) (Top .P) = yes (≤-refl (Top P))
≤-dec (Top .(Seq _ Q)) (Seqₗ q Q) = no ¬≤-Top-Seqₗ
≤-dec (Top .(Seq P _)) (Seqᵣ P q) = no ¬≤-Top-Seqᵣ
≤-dec (Top .(If _ Q)) (Ifₗ q Q) = {!!}
≤-dec (Top .(If P _)) (Ifᵣ P q) = {!!}
≤-dec (Top .(While _)) (While (n , p)) = {!!}
≤-dec (Seqₗ p Q) q = {!!}
≤-dec (Seqᵣ P p) q = {!!}
≤-dec (Ifₗ p Q) q = {!!}
≤-dec (Ifᵣ P p) q = {!!}
≤-dec (While (n , p)) q = {!!}
