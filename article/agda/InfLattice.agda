module InfLattice where

open import Function using ( case_of_ )
open import Relation.Binary.PropositionalEquality
open import Data.Sum using ( _⊎_ ; inj₁ ; inj₂ )
open import Data.Product
open import Data.Nat.Base renaming (_≤_ to _≤ℕ_) renaming (compare to ℕ-compare)
open import Data.Nat.Properties renaming ( ≤-refl to ≤ℕ-refl ) renaming ( ≤-trans to ≤ℕ-trans )
open import Base
open import Program
open import Order

_∧Wₙ_ : ℕ → ℕ → ℕ
zero ∧Wₙ n = zero
suc n ∧Wₙ zero = zero
suc n ∧Wₙ suc n' = suc (n ∧Wₙ n')

_∧_ : {P : Prog} (p q : Pos P) → Pos P
_∧Wₚ_ : {P : Prog} → (ℕ × Pos P) → (ℕ × Pos P) → Pos P
_∧W_ : {P : Prog} → (ℕ × Pos P) → (ℕ × Pos P) → ℕ × Pos P
infix 40 _∧_
Bot P ∧ q = Bot P
Top P ∧ q = q
Seqₗ {P} p Q ∧ Bot .(Seq _ Q) = Bot (Seq P Q)
Seqₗ p Q ∧ Top .(Seq _ Q) = Seqₗ p Q
Seqₗ p Q ∧ Seqₗ q .Q = Seqₗ (p ∧ q) Q
Seqₗ p Q ∧ Seqᵣ P q = Bot (Seq P Q)
Seqᵣ P {Q} q ∧ Bot .(Seq P _) = Bot (Seq P Q)
Seqᵣ P q ∧ Top .(Seq P _) = Seqᵣ P q
Seqᵣ P q ∧ Seqₗ p Q = Bot (Seq P Q)
Seqᵣ P q ∧ Seqᵣ .P q' = Seqᵣ P (q ∧ q')
Ifₗ {P} p Q ∧ Bot .(If _ Q) = Bot (If P Q)
Ifₗ p Q ∧ Top .(If _ Q) = Ifₗ p Q
Ifₗ p Q ∧ Ifₗ p' .Q = Ifₗ (p ∧ p') Q
Ifₗ p Q ∧ Ifᵣ P q = Bot (If P Q)
Ifᵣ P {Q} q ∧ Bot .(If P _) = Bot (If P Q)
Ifᵣ P q ∧ Top .(If P _) = Ifᵣ P q
Ifᵣ P q ∧ Ifₗ p Q = Bot (If P Q)
Ifᵣ P q ∧ Ifᵣ .P q' = Ifᵣ P (q ∧ q')
While {P} np ∧ Bot .(While _) = Bot (While P)
While np ∧ Top .(While _) = While np
While np ∧ While np' = While (np ∧W np')
(zero , p) ∧Wₚ (zero , p') = p ∧ p'
(zero , p) ∧Wₚ (suc n' , p') = p
(suc n , p) ∧Wₚ (zero , p') = p'
(suc n , p) ∧Wₚ (suc n' , p') = (n , p) ∧Wₚ (n' , p')
(n , p) ∧W (n' , p') = n ∧Wₙ n' , (n , p) ∧Wₚ (n' , p')
