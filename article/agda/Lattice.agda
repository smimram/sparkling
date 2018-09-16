module Lattice where

open import Function using ( case_of_ )
open import Relation.Binary.PropositionalEquality
open import Data.Product
open import Data.Nat.Base renaming (_≤_ to _≤ℕ_) renaming (compare to ℕ-compare)
open import Data.Nat.Properties using ( )
open import Program
open import Order

≤ℕ-suc : {n n' : ℕ} → (n ≤ℕ n') → (suc n ≤ℕ suc n')
≤ℕ-suc {zero} {n'} l = s≤s l
≤ℕ-suc {suc n} {zero} l = s≤s l
≤ℕ-suc {suc n} {suc n'} l = s≤s l

_∨_ : {P : Prog} (p q : Pos P) → Pos P
_∨Wₙ_ : {P : Prog} → (np : ℕ × Pos P) → (np' : ℕ × Pos P) → ℕ
_∨Wₚ_ : {P : Prog} → (np : ℕ × Pos P) → (np' : ℕ × Pos P) → Pos P
infix 40 _∨_
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
Ifₗ p Q ∨ Bot .(If _ Q) = Ifₗ p Q
Ifₗ {P} p Q ∨ Top .(If _ Q) = Top (If P Q)
Ifₗ p Q ∨ Ifₗ p' .Q = Ifₗ (p ∨ p') Q
Ifₗ {P} p Q ∨ Ifᵣ .P q = Top (If P Q)
Ifᵣ P {Q} q ∨ Bot .(If P Q) = Ifᵣ P q
Ifᵣ P {Q} q ∨ Top .(If P _) = Top (If P Q)
Ifᵣ P q ∨ Ifₗ p Q₁ = Top (If P Q₁)
Ifᵣ P q ∨ Ifᵣ .P q' = Ifᵣ P (q ∨ q')
Par p q ∨ Bot .(Par _ _) = Par p q
Par {P} p {Q} q ∨ Top .(Par _ _) = Top (Par P Q)
Par p q ∨ Par p' q' = Par (p ∨ p') (q ∨ q')
While n p ∨ Bot .(While _) = While n p
While {P} n p ∨ Top .(While _) = Top (While P)
While n p ∨ While n' p' = While ((n , p) ∨Wₙ (n' , p')) ((n , p) ∨Wₚ (n' , p'))
(zero , p) ∨Wₙ (zero , p') = zero
(zero , p) ∨Wₙ (suc n' , p') = suc n'
(suc n , p) ∨Wₙ (zero , p') = suc n
(suc n , p) ∨Wₙ (suc n' , p') = suc ((n , p) ∨Wₙ (n' , p'))
(zero , p) ∨Wₚ (zero , p') = p ∨ p'
(zero , p) ∨Wₚ (suc n' , p') = p'
(suc n , p) ∨Wₚ (zero , p') = p
(suc n , p) ∨Wₚ (suc n' , p') = (n , p) ∨Wₚ (n' , p')

∨-Seqₗ : {P : Prog} (p p' : Pos P) (Q : Prog) → (Seqₗ p Q ∨ Seqₗ p' Q ≡ Seqₗ (p ∨ p') Q)
∨-Seqₗ (Bot P) p' Q = refl
∨-Seqₗ (Top P) p' Q = refl
∨-Seqₗ (Seqₗ p Q₁) p' Q = refl
∨-Seqₗ (Seqᵣ P p) p' Q = refl
∨-Seqₗ (Ifₗ p Q₁) q Q = refl
∨-Seqₗ (Ifᵣ P p) q Q = refl
∨-Seqₗ (Par p p₁) q Q = refl
∨-Seqₗ (While n p) q Q = refl

∨-Seqᵣ : (P : Prog) {Q : Prog} (q q' : Pos Q) → (Seqᵣ P q ∨ Seqᵣ P q' ≡ Seqᵣ P (q ∨ q'))
∨-Seqᵣ P (Bot P₁) q' = refl
∨-Seqᵣ P (Top P₁) q' = refl
∨-Seqᵣ P (Seqₗ q Q) q' = refl
∨-Seqᵣ P (Seqᵣ P₁ q) q' = refl
∨-Seqᵣ P (Ifₗ p Q) q = refl
∨-Seqᵣ P (Ifᵣ P₁ p) q = refl
∨-Seqᵣ P (Par p p₁) q = refl
∨-Seqᵣ P (While n p) q = refl

∨-Bot-l : {P : Prog} (p : Pos P) → (Bot P ∨ p ≡ p)
∨-Bot-l (Bot P) = refl
∨-Bot-l (Top P) = refl
∨-Bot-l (Seqₗ p Q) = refl
∨-Bot-l (Seqᵣ P p) = refl
∨-Bot-l (Ifₗ p Q) = refl
∨-Bot-l (Ifᵣ P p) = refl
∨-Bot-l (Par p p₁) = refl
∨-Bot-l (While n p) = refl

∨Wₙ-assoc : {P : Prog} (n n' n'' : ℕ) (p p' p'' : Pos P) → ((((n , p) ∨Wₙ (n' , p')) , ((n , p) ∨Wₚ (n' , p'))) ∨Wₙ (n'' , p'')) ≡ ((n , p) ∨Wₙ (((n' , p') ∨Wₙ (n'' , p'')) , ((n' , p') ∨Wₚ (n'' , p''))))
∨Wₙ-assoc zero zero zero p p' p'' = refl
∨Wₙ-assoc zero zero (suc n'') p p' p'' = refl
∨Wₙ-assoc zero (suc n') zero p p' p'' = refl
∨Wₙ-assoc zero (suc n') (suc n'') p p' p'' = refl
∨Wₙ-assoc (suc n) zero zero p p' p'' = refl
∨Wₙ-assoc (suc n) zero (suc n'') p p' p'' = refl
∨Wₙ-assoc (suc n) (suc n') zero p p' p'' = refl
∨Wₙ-assoc (suc n) (suc n') (suc n'') p p' p'' = cong suc (∨Wₙ-assoc n n' n'' p p' p'')

∨-assoc : {P : Prog} (p q r : Pos P) → ((p ∨ q) ∨ r ≡ p ∨ (q ∨ r))
∨Wₚ-assoc : {P : Prog} (n n' n'' : ℕ) (p p' p'' : Pos P) → ((((n , p) ∨Wₙ (n' , p')) , ((n , p) ∨Wₚ (n' , p'))) ∨Wₚ (n'' , p'')) ≡ ((n , p) ∨Wₚ (((n' , p') ∨Wₙ (n'' , p'')) , ((n' , p') ∨Wₚ (n'' , p''))))
∨Wₚ-assoc zero zero zero p p' p'' = ∨-assoc p p' p''
∨Wₚ-assoc zero zero (suc n'') p p' p'' = refl
∨Wₚ-assoc zero (suc n') zero p p' p'' = refl
∨Wₚ-assoc zero (suc n') (suc n'') p p' p'' = refl
∨Wₚ-assoc (suc n) zero zero p p' p'' = refl
∨Wₚ-assoc (suc n) zero (suc n'') p p' p'' = refl
∨Wₚ-assoc (suc n) (suc n') zero p p' p'' = refl
∨Wₚ-assoc (suc n) (suc n') (suc n'') p p' p'' = ∨Wₚ-assoc n n' n'' p p' p''
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
∨-assoc (Ifₗ p Q) (Bot .(If _ Q)) r = refl
∨-assoc (Ifₗ p Q) (Top .(If _ Q)) r = refl
∨-assoc (Ifₗ p Q) (Ifₗ q .Q) (Bot .(If _ Q)) = refl
∨-assoc (Ifₗ p Q) (Ifₗ q .Q) (Top .(If _ Q)) = refl
∨-assoc (Ifₗ p Q) (Ifₗ q .Q) (Ifₗ r .Q) = cong (λ p → Ifₗ p Q) (∨-assoc p q r)
∨-assoc (Ifₗ p Q) (Ifₗ q .Q) (Ifᵣ P r) = refl
∨-assoc (Ifₗ p Q) (Ifᵣ P q) (Bot .(If P Q)) = refl
∨-assoc (Ifₗ p Q) (Ifᵣ P q) (Top .(If P Q)) = refl
∨-assoc (Ifₗ p Q) (Ifᵣ P q) (Ifₗ r .Q) = refl
∨-assoc (Ifₗ p Q) (Ifᵣ P q) (Ifᵣ .P r) = refl
∨-assoc (Ifᵣ P p) (Bot .(If P _)) r = refl
∨-assoc (Ifᵣ P p) (Top .(If P _)) r = refl
∨-assoc (Ifᵣ P p) (Ifₗ q Q) (Bot .(If P Q)) = refl
∨-assoc (Ifᵣ P p) (Ifₗ q Q) (Top .(If P Q)) = refl
∨-assoc (Ifᵣ P p) (Ifₗ q Q) (Ifₗ r .Q) = refl
∨-assoc (Ifᵣ P p) (Ifₗ q Q) (Ifᵣ .P r) = refl
∨-assoc (Ifᵣ P p) (Ifᵣ .P q) (Bot .(If P _)) = refl
∨-assoc (Ifᵣ P p) (Ifᵣ .P q) (Top .(If P _)) = refl
∨-assoc (Ifᵣ P p) (Ifᵣ .P q) (Ifₗ r Q) = refl
∨-assoc (Ifᵣ P p) (Ifᵣ .P q) (Ifᵣ .P r) = cong (λ q → Ifᵣ P q) (∨-assoc p q r)
∨-assoc (Par p p₁) (Bot .(Par _ _)) r = refl
∨-assoc (Par p p₁) (Top .(Par _ _)) r = refl
∨-assoc (Par p p₁) (Par q q₁) (Bot .(Par _ _)) = refl
∨-assoc (Par p p₁) (Par q q₁) (Top .(Par _ _)) = refl
∨-assoc (Par p p₁) (Par q q₁) (Par r r₁) = cong₂ (λ p q → Par p q) (∨-assoc p q r) (∨-assoc p₁ q₁ r₁)
∨-assoc (While n p) (Bot .(While _)) r = refl
∨-assoc (While n p) (Top .(While _)) r = refl
∨-assoc (While n p) (While n₁ q) (Bot .(While _)) = refl
∨-assoc (While n p) (While n₁ q) (Top .(While _)) = refl
∨-assoc (While n p) (While n' p') (While n'' p'') = cong₂ While (∨Wₙ-assoc n n' n'' p p' p'') (∨Wₚ-assoc n n' n'' p p' p'')

∨Wₙ-idem : {P : Prog} (n : ℕ) (p : Pos P) → ((n , p) ∨Wₙ (n , p)) ≡ n
∨Wₙ-idem zero p = refl
∨Wₙ-idem (suc n) p = cong suc (∨Wₙ-idem n p)

∨-idem : {P : Prog} (p : Pos P) → (p ∨ p ≡ p)
∨Wₚ-idem : {P : Prog} (n : ℕ) (p : Pos P) → ((n , p) ∨Wₚ (n , p)) ≡ p
∨Wₚ-idem zero p = ∨-idem p
∨Wₚ-idem (suc n) p = ∨Wₚ-idem n p
∨-idem (Bot P) = refl
∨-idem (Top P) = refl
∨-idem (Seqₗ p Q) = cong (λ p → Seqₗ p Q) (∨-idem p)
∨-idem (Seqᵣ P q) = cong (λ q → Seqᵣ P q) (∨-idem q)
∨-idem (Ifₗ p Q) = cong (λ p → Ifₗ p Q) (∨-idem p)
∨-idem (Ifᵣ P q) = cong (Ifᵣ P) (∨-idem q)
∨-idem (Par p q) = cong₂ (λ p q → Par p q) (∨-idem p) (∨-idem q)
∨-idem (While n p) = cong₂ While (∨Wₙ-idem n p) (∨Wₚ-idem n p)

∨Wₙ-comm : {P : Prog} (n n' : ℕ) (p p' : Pos P) → ((n , p) ∨Wₙ (n' , p')) ≡ ((n' , p') ∨Wₙ (n , p))
∨Wₙ-comm zero zero p p' = refl
∨Wₙ-comm zero (suc n') p p' = refl
∨Wₙ-comm (suc n) zero p p' = refl
∨Wₙ-comm (suc n) (suc n') p p' = cong suc (∨Wₙ-comm n n' p p')

∨-comm : {P : Prog} (p q : Pos P) → ((p ∨ q) ≡ (q ∨ p))
∨Wₚ-comm : {P : Prog} (n n' : ℕ) (p p' : Pos P) → ((n , p) ∨Wₚ (n' , p')) ≡ ((n' , p') ∨Wₚ (n , p))
∨Wₚ-comm zero zero p p' = ∨-comm p p'
∨Wₚ-comm zero (suc n') p p' = refl
∨Wₚ-comm (suc n) zero p p' = refl
∨Wₚ-comm (suc n) (suc n') p p' = ∨Wₚ-comm n n' p p'
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
∨-comm (Bot .(If _ Q)) (Ifₗ q Q) = refl
∨-comm (Bot .(If P _)) (Ifᵣ P q) = refl
∨-comm (Bot .(Par _ _)) (Par q q₁) = refl
∨-comm (Bot .(While _)) (While n q) = refl
∨-comm (Top .(If _ Q)) (Ifₗ q Q) = refl
∨-comm (Top .(If P _)) (Ifᵣ P q) = refl
∨-comm (Top .(Par _ _)) (Par q q₁) = refl
∨-comm (Top .(While _)) (While n q) = refl
∨-comm (Ifₗ p Q) (Bot .(If _ Q)) = refl
∨-comm (Ifₗ p Q) (Top .(If _ Q)) = refl
∨-comm (Ifₗ p Q) (Ifₗ q .Q) = cong (λ p → Ifₗ p Q) (∨-comm p q)
∨-comm (Ifₗ p Q) (Ifᵣ P q) = refl
∨-comm (Ifᵣ P p) (Bot .(If P _)) = refl
∨-comm (Ifᵣ P p) (Top .(If P _)) = refl
∨-comm (Ifᵣ P p) (Ifₗ q Q) = refl
∨-comm (Ifᵣ P p) (Ifᵣ .P q) = cong (λ q → Ifᵣ P q) (∨-comm p q)
∨-comm (Par p p₁) (Bot .(Par _ _)) = refl
∨-comm (Par p p₁) (Top .(Par _ _)) = refl
∨-comm (Par p q) (Par p' q') = cong₂ (λ p q → Par p q) (∨-comm p p') (∨-comm q q')
∨-comm (While n p) (Bot .(While _)) = refl
∨-comm (While n p) (Top .(While _)) = refl
∨-comm (While n p) (While n' p') = cong₂ While (∨Wₙ-comm n n' p p') (∨Wₚ-comm n n' p p')

∨Wₙ-l-≤ : {P : Prog} (n n' : ℕ) (p p' : Pos P) → n ≤ℕ ((n , p) ∨Wₙ (n' , p'))
∨Wₙ-l-≤ zero n' p p' = z≤n
∨Wₙ-l-≤ (suc n) zero p p' = Data.Nat.Properties.≤-refl
∨Wₙ-l-≤ (suc n) (suc n') p p' = ≤ℕ-suc (∨Wₙ-l-≤ n n' p p')

∨-l-≤ : {P : Prog} (p q : Pos P) → (p ≤ (p ∨ q))
∨-l-≤ (Bot P) q = ≤-Bot q
∨-l-≤ (Top P) (Bot .P) = ≤-refl (Top P)
∨-l-≤ (Top P) (Top .P) = ≤-refl (Top P)
∨-l-≤ (Top .(Seq _ Q)) (Seqₗ {P} q Q) = ≤-refl (Top (Seq P Q))
∨-l-≤ (Top .(Seq P _)) (Seqᵣ P {Q} q) = ≤-refl (Top (Seq P Q))
∨-l-≤ (Seqₗ p Q) (Bot .(Seq _ Q)) = ≤-refl (Seqₗ p Q)
∨-l-≤ (Seqₗ p Q) (Top .(Seq _ Q)) = ≤-Top (Seqₗ p Q)
∨-l-≤ (Seqₗ p Q) (Seqₗ q .Q) = ≤-Seqₗ (∨-l-≤ p q) Q
∨-l-≤ (Seqₗ p Q) (Seqᵣ P q) = ≤-Seqₗ-Seqᵣ p q
∨-l-≤ (Seqᵣ P p) (Bot .(Seq P _)) = ≤-refl (Seqᵣ P p)
∨-l-≤ (Seqᵣ P p) (Top .(Seq P _)) = ≤-Top (Seqᵣ P p)
∨-l-≤ (Seqᵣ P p) (Seqₗ q Q) = ≤-Seqᵣ P (≤-refl p)
∨-l-≤ (Seqᵣ P p) (Seqᵣ .P q) = ≤-Seqᵣ P (∨-l-≤ p q)
∨-l-≤ (Top .(If _ Q)) (Ifₗ {P} p Q) = ≤-refl (Top (If P Q))
∨-l-≤ (Top .(If P _)) (Ifᵣ P {Q} q) = ≤-refl (Top (If P Q))
∨-l-≤ (Top .(Par _ _)) (Par {P} p {Q} q) = ≤-refl (Top (Par P Q))
∨-l-≤ (Top .(While _)) (While {P} n p) = ≤-refl (Top (While P))
∨-l-≤ (Ifₗ {P} p Q) (Bot .(If P Q)) = ≤-refl (Ifₗ p Q)
∨-l-≤ (Ifₗ {P} p Q) (Top .(If P Q)) = ≤-Top (Ifₗ p Q)
∨-l-≤ (Ifₗ {P} p Q) (Ifₗ q .Q) = ≤-Ifₗ (∨-l-≤ p q) Q
∨-l-≤ (Ifₗ {.P} p Q) (Ifᵣ P q) = ≤-Top (Ifₗ p Q)
∨-l-≤ (Ifᵣ P {Q} q) (Bot .(If P Q)) = ≤-refl (Ifᵣ P q)
∨-l-≤ (Ifᵣ P {Q} q) (Top .(If P Q)) = ≤-Top (Ifᵣ P q)
∨-l-≤ (Ifᵣ P {.Q} q) (Ifₗ r Q) = ≤-Top (Ifᵣ P q)
∨-l-≤ (Ifᵣ P {Q} q) (Ifᵣ .P q') = ≤-Ifᵣ P (∨-l-≤ q q')
∨-l-≤ (Par p q) (Bot .(Par _ _)) = ≤-refl (Par p q)
∨-l-≤ (Par p q) (Top .(Par _ _)) = ≤-Top (Par p q)
∨-l-≤ (Par p q) (Par p' q') = ≤-Par (∨-l-≤ p p') (∨-l-≤ q q')
∨-l-≤ (While n p) (Bot .(While _)) = ≤-refl (While n p)
∨-l-≤ (While n p) (Top .(While _)) = ≤-Top (While n p)
∨-l-≤ (While zero p) (While zero p') = ≤-Whileₚ (∨-l-≤ p p')
∨-l-≤ (While zero p) (While (suc n') p') = ≤-Whileₙ' (s≤s z≤n) p p'
∨-l-≤ (While (suc n) p) (While zero p') = ≤-refl (While (suc n) p)
∨-l-≤ (While (suc n) p) (While (suc n') p') = {!!}

-- ∨-r-≤ : {P : Prog} (p q : Pos P) → (q ≤ (p ∨ q))
-- ∨-r-≤ p q = coe (cong (λ p → q ≤ p) (∨-comm q p)) (∨-l-≤ q p)

-- ∨-↝-l : {P : Prog} {p p' : Pos P} → (p ↝ p') → (q : Pos P) → ((p ∨ q) ≤ (p' ∨ q))
-- ∨-↝-l ↝-Act (Bot .Act) = ≤-step1 ↝-Act
-- ∨-↝-l ↝-Act (Top .Act) = ≤-refl (Top Act)
-- ∨-↝-l (↝-Seq₀ P Q) (Bot .(Seq P Q)) = ≤-step1 (↝-Seq₀ P Q)
-- ∨-↝-l (↝-Seq₀ P Q) (Top .(Seq P Q)) = ≤-refl (Top (Seq P Q))
-- ∨-↝-l (↝-Seq₀ P Q) (Seqₗ q .Q) = ≤-refl (Seqₗ q Q)
-- ∨-↝-l (↝-Seq₀ P Q) (Seqᵣ .P q) = ≤-refl (Seqᵣ P q)
-- ∨-↝-l (↝-Seqₗ {p' = p'} r Q) (Bot .(Seq _ Q)) = ≤-step1 (↝-Seqₗ r Q)
-- ∨-↝-l (↝-Seqₗ {P} r Q) (Top .(Seq _ Q)) = ≤-refl (Top (Seq P Q))
-- ∨-↝-l (↝-Seqₗ r Q) (Seqₗ q .Q) = ≤-Seqₗ (∨-↝-l r q) Q
-- ∨-↝-l (↝-Seqₗ r Q) (Seqᵣ P q) = ≤-Seqᵣ P (≤-refl q)
-- ∨-↝-l (↝-Seqₘ P Q) (Bot .(Seq P Q)) = ≤-step1 (↝-Seqₘ P Q)
-- ∨-↝-l (↝-Seqₘ P Q) (Top .(Seq P Q)) = ≤-refl (Top (Seq P Q))
-- ∨-↝-l (↝-Seqₘ P Q) (Seqₗ q .Q) = ≤-step1 (↝-Seqₘ P Q)
-- ∨-↝-l (↝-Seqₘ P Q) (Seqᵣ .P q) = ≤-refl (Seqᵣ P q)
-- ∨-↝-l (↝-Seqᵣ P {q' = q'} r) (Bot .(Seq P _)) = ≤-step1 (↝-Seqᵣ P r)
-- ∨-↝-l (↝-Seqᵣ P {Q} r) (Top .(Seq P _)) = ≤-refl (Top (Seq P Q))
-- ∨-↝-l (↝-Seqᵣ P {q' = q'} r) (Seqₗ q Q) = ≤-step1 (↝-Seqᵣ P r)
-- ∨-↝-l (↝-Seqᵣ P r) (Seqᵣ .P q) = ≤-Seqᵣ P (∨-↝-l r q)
-- ∨-↝-l (↝-Seq₁ P Q) (Bot .(Seq P Q)) = ≤-step1 (↝-Seq₁ P Q)
-- ∨-↝-l (↝-Seq₁ P Q) (Top .(Seq P Q)) = ≤-refl (Top (Seq P Q))
-- ∨-↝-l (↝-Seq₁ P Q) (Seqₗ q .Q) = ≤-step1 (↝-Seq₁ P Q)
-- ∨-↝-l (↝-Seq₁ P Q) (Seqᵣ .P q) = ≤-step1 (↝-Seq₁ P Q)

-- ∨-≤-l : {P : Prog} {p p' : Pos P} → (p ≤ p') → (q : Pos P) → (p ∨ q ≤ p' ∨ q)
-- ∨-≤-l (≤-step r l) q = ≤-trans (∨-↝-l r q) (∨-≤-l l q)
-- ∨-≤-l (≤-refl p) q = ≤-refl (p ∨ q)

-- ∨-≤-r : {P : Prog} (p : Pos P) {q q' : Pos P} → (q ≤ q') → (p ∨ q ≤ p ∨ q')
-- ∨-≤-r p {q} {q'} l =
  -- coe (cong (λ r → r ≤ (p ∨ q')) (∨-comm q p))
  -- (coe (cong (λ r → (q ∨ p) ≤ r) (∨-comm q' p))
  -- (∨-≤-l l p))

-- ∨-≤ : {P : Prog} {p p' q q' : Pos P} → (p ≤ p') → (q ≤ q') → (p ∨ q ≤ p' ∨ q')
-- ∨-≤ {p' = p'} {q = q} l r = ≤-trans (∨-≤-l l q) (∨-≤-r p' r)

-- ∨-sup : {P : Prog} (p p' q : Pos P) → ((p ≤ p ∨ p') and (p' ≤ p ∨ p')) and ((r : Pos P) → (p ≤ r) → (p' ≤ r) → (p ∨ p' ≤ r))
-- proj₁ (proj₁ (∨-sup p p' q)) = ∨-l-≤ p p'
-- proj₂ (proj₁ (∨-sup p p' q)) = ∨-r-≤ p p'
-- proj₂ (∨-sup p p' q) r l l' = ≤-trans (∨-≤ l l') (≡-≤ (∨-idem r))
