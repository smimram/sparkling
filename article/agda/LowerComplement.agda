module LowerComplement where

open import Function using ( case_of_ )
open import Relation.Binary.PropositionalEquality
open import Data.Empty
open import Data.Sum
open import Data.Product
open import Data.Nat.Base renaming (_≤_ to _≤ℕ_)
open import Data.Nat.Properties renaming (≤-trans to ≤ℕ-trans ; ≤-antisym to ≤ℕ-antisym) hiding (≤-step ; ≤-refl)

open import Base
open import Equality
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
  ¬>-Ifᵣ : (P : Prog) {Q : Prog} {q q' : Pos Q} → (q ¬> q') → Ifᵣ P q ¬> Ifᵣ P q'
  ¬>-Ifᵣ' : (P : Prog) {Q : Prog} (q : Pos Q) → Ifₗ (Top P) Q ¬> Ifᵣ P q
  ¬>-While : {P : Prog} (n : ℕ) {p p' : Pos P} → (p ¬> p') → While (n , p) ¬> While (n , p')

¬>-refl : {P : Prog} (p : Pos P) → p ¬> p
¬>-refl (Bot P) = ¬>-Bot
¬>-refl (Top P) = ¬>-Top
¬>-refl (Seqₗ p Q) = ¬>-Seqₗ (¬>-refl p) Q
¬>-refl (Seqᵣ P q) = ¬>-Seqᵣ P (¬>-refl q)
¬>-refl (Ifₗ p Q) = ¬>-Ifₗ (¬>-refl p) Q
¬>-refl (Ifᵣ P q) = ¬>-Ifᵣ P (¬>-refl q)
¬>-refl (While (n , p)) = ¬>-While n (¬>-refl p)

¬>-sound : {P : Prog} {x : Pos P} {p q : Pos P} → (p ¬> q) → (x ≤ p) → (q ≤ x) → x ≡ q
¬>-sound ¬>-Bot l l' = ≤-antisym l l'
¬>-sound ¬>-Top l l' = ≤-antisym l l'
¬>-sound (¬>-Seqₗ {p' = p'} r Q) (≤-step (↝-Seq₀ P .Q) l) l' = ⊥-elim (¬≤-Seqₗ-Bot l')
¬>-sound (¬>-Seqₗ r Q) (≤-step (↝-Seqₗ s .Q) l) l' = cong (λ p → Seqₗ p Q) (¬>-sound r (≤-step s (≤-Seqₗ' l)) (≤-Seqₗ' l'))
¬>-sound (¬>-Seqₗ r Q) (≤-step (↝-Seqₘ P .Q) l) l' =  ⊥-elim (¬≤-Seqᵣ-Seqₗ l)
¬>-sound (¬>-Seqₗ r Q) (≤-step (↝-Seqᵣ P s) l) l' = ⊥-elim (¬≤-Seqᵣ-Seqₗ l)
¬>-sound (¬>-Seqₗ r Q) (≤-step (↝-Seq₁ P .Q) l) l' = ⊥-elim (¬≤-Top-Seqₗ l)
¬>-sound (¬>-Seqₗ {p = p} r Q) (≤-refl .(Seqₗ _ Q)) l' = cong (λ p → Seqₗ p Q) (¬>-sound r (≤-refl p) (≤-Seqₗ' l'))
¬>-sound (¬>-Seqᵣ P r) (≤-step (↝-Seq₀ .P _) l) l' = ⊥-elim (¬≤-Seqᵣ-Bot l')
¬>-sound (¬>-Seqᵣ P r) (≤-step (↝-Seqₗ s _) l) l' = ⊥-elim (¬≤-Seqᵣ-Seqₗ l')
¬>-sound (¬>-Seqᵣ P r) (≤-step (↝-Seqₘ .P _) l) l' = ⊥-elim (¬≤-Seqᵣ-Seqₗ l')
¬>-sound (¬>-Seqᵣ P r) (≤-step (↝-Seqᵣ .P s) l) l' = cong (λ q → Seqᵣ P q) (¬>-sound r (≤-step s (≤-Seqᵣ' l)) (≤-Seqᵣ' l'))
¬>-sound (¬>-Seqᵣ P r) (≤-step (↝-Seq₁ .P _) l) l' = ⊥-elim (¬≤-Top-Seqᵣ l)
¬>-sound (¬>-Seqᵣ P {q = q} r) (≤-refl .(Seqᵣ P _)) l' = cong (λ q → Seqᵣ P q) (¬>-sound r (≤-refl q) (≤-Seqᵣ' l'))
¬>-sound (¬>-Ifₗ r Q) (≤-step (↝-If₀ₗ P .Q) l) l' = ⊥-elim (¬≤-Ifₗ-Bot l')
¬>-sound (¬>-Ifₗ r Q) (≤-step (↝-Ifₗ s .Q) l) l' = cong (λ p → Ifₗ p Q) (¬>-sound r (≤-step s (≤-Ifₗ' l)) (≤-Ifₗ' l'))
¬>-sound (¬>-Ifₗ r Q) (≤-step (↝-If₁ₗ P .Q) l) l' = ⊥-elim (¬≤-Top-Ifₗ l)
¬>-sound (¬>-Ifₗ r Q) (≤-step (↝-If₀ᵣ P .Q) l) l' = ⊥-elim (¬≤-Ifₗ-Bot l')
¬>-sound (¬>-Ifₗ r Q) (≤-step (↝-Ifᵣ P s) l) l' = ⊥-elim (¬≤-Ifₗ-Ifᵣ l')
¬>-sound (¬>-Ifₗ r Q) (≤-step (↝-If₁ᵣ P .Q) l) l' = ⊥-elim (¬≤-Ifₗ-Ifᵣ l')
¬>-sound (¬>-Ifₗ {p = p} r Q) (≤-refl .(Ifₗ _ Q)) l' = cong (λ p → Ifₗ p Q) (¬>-sound r (≤-refl p) (≤-Ifₗ' l'))
¬>-sound (¬>-Ifₗ' p Q) (≤-step (↝-If₀ₗ P .Q) l) l' = ⊥-elim (¬≤-Ifₗ-Bot l')
¬>-sound (¬>-Ifₗ' p Q) (≤-step (↝-Ifₗ x₁ .Q) l) l' = ⊥-elim (¬≤-Ifₗ-Ifᵣ l)
¬>-sound (¬>-Ifₗ' p Q) (≤-step (↝-If₁ₗ P .Q) l) l' = ⊥-elim (¬≤-Top-Ifᵣ l)
¬>-sound (¬>-Ifₗ' p Q) (≤-step (↝-If₀ᵣ P .Q) l) l' = ⊥-elim (¬≤-Ifₗ-Bot l')
¬>-sound (¬>-Ifₗ' p Q) (≤-step (↝-Ifᵣ P x₁) l) l' = ⊥-elim (¬≤-Ifₗ-Ifᵣ l')
¬>-sound (¬>-Ifₗ' p Q) (≤-step (↝-If₁ᵣ P .Q) l) l' = ⊥-elim (¬≤-Ifₗ-Ifᵣ l')
¬>-sound (¬>-Ifₗ' p Q) (≤-refl .(Ifᵣ _ (Top Q))) l' = ⊥-elim (¬≤-Ifₗ-Ifᵣ l')
¬>-sound (¬>-Ifᵣ P r) (≤-step (↝-If₀ₗ .P Q) l) l' = ⊥-elim (¬≤-Ifₗ-Ifᵣ l)
¬>-sound (¬>-Ifᵣ P r) (≤-step (↝-Ifₗ s Q) l) l' = ⊥-elim (¬≤-Ifₗ-Ifᵣ l)
¬>-sound (¬>-Ifᵣ P r) (≤-step (↝-If₁ₗ .P Q) l) l' = ⊥-elim (¬≤-Top-Ifᵣ l)
¬>-sound (¬>-Ifᵣ P r) (≤-step (↝-If₀ᵣ .P Q) l) l' = ⊥-elim (¬≤-Ifᵣ-Bot l')
¬>-sound (¬>-Ifᵣ P r) (≤-step (↝-Ifᵣ .P s) l) l' = cong (λ q → Ifᵣ P q) (¬>-sound r (≤-step s (≤-Ifᵣ' l)) (≤-Ifᵣ' l'))
¬>-sound (¬>-Ifᵣ P r) (≤-step (↝-If₁ᵣ .P Q) l) l' = ⊥-elim (¬≤-Top-Ifᵣ l)
¬>-sound (¬>-Ifᵣ P {q = q} r) (≤-refl .(Ifᵣ P _)) l' = cong (λ q → Ifᵣ P q) (¬>-sound r (≤-refl q) (≤-Ifᵣ' l'))
¬>-sound (¬>-Ifᵣ' P q) (≤-step (↝-If₀ₗ .P Q) l) l' = ⊥-elim (¬≤-Ifᵣ-Bot l')
¬>-sound (¬>-Ifᵣ' P q) (≤-step (↝-Ifₗ s Q) l) l' = ⊥-elim (¬≤-Ifᵣ-Ifₗ l')
¬>-sound (¬>-Ifᵣ' P q) (≤-step (↝-If₁ₗ .P Q) l) l' = ⊥-elim (¬≤-Ifᵣ-Ifₗ l')
¬>-sound (¬>-Ifᵣ' P q) (≤-step (↝-If₀ᵣ .P Q) l) l' = ⊥-elim (¬≤-Ifᵣ-Bot l')
¬>-sound (¬>-Ifᵣ' P q) (≤-step (↝-Ifᵣ .P s) l) l' = ⊥-elim (¬≤-Ifᵣ-Ifₗ l)
¬>-sound (¬>-Ifᵣ' P q) (≤-step (↝-If₁ᵣ .P Q) l) l' = ⊥-elim (¬≤-Top-Ifₗ l)
¬>-sound (¬>-Ifᵣ' P q) (≤-refl .(Ifₗ (Top P) _)) l' = ⊥-elim (¬≤-Ifᵣ-Ifₗ l')
¬>-sound (¬>-While n r) (≤-step (↝-While₀ P) l) l' = ⊥-elim (¬≤-While-Bot l')
¬>-sound (¬>-While n r) (≤-step (↝-While₀' P) l) l' = ⊥-elim (¬≤-While-Bot l')
¬>-sound (¬>-While n {p} {p'} r) (≤-step (↝-While {_} {q} {q'} n' s) l) l' =
  let nn' = ≤ℕ-antisym (≤-While-elimₙ l) (≤-While-elimₙ l') in
  cong₂ (λ n p → While (n , p)) nn' (¬>-sound r (≤-step s (≤-While-elimₚ (transport (λ n' -> While (n' , q') ≤ While (n , p)) nn' l))) (≤-While-elimₚ (transport (λ n' → While (n , p') ≤ While (n' , q)) nn' l')))
¬>-sound (¬>-While n r) (≤-step (↝-While₁ P n') l) l' =
  let nn' = ≤ℕ-antisym (≤-While-elimₙ l') (≤ℕ-trans (n≤1+n n') (≤-While-elimₙ l)) in
  let nn' = transport (λ n → suc n' ≤ℕ n) nn' (≤-While-elimₙ l) in
  ⊥-elim (suc-acyclic nn')
¬>-sound (¬>-While n r) (≤-step (↝-While₁' P n') l) l' = ⊥-elim (¬≤-Top-While l)
¬>-sound (¬>-While n {p} r) (≤-refl .(While (n , _))) l' = cong (λ p → While (n , p)) (¬>-sound r (≤-refl p) (≤-While-elimₚ l'))

¬>-complete : {P : Prog} (p : Pos P) (x : Pos P) → (p ≤ x) or (∃[ q ] ((q ¬> p) and (x ≤ q)))
¬>-complete (Bot P) x = inj₁ (≤-Bot x)
¬>-complete (Top P) x = inj₂ ( Top P , ¬>-Top , ≤-Top x )
¬>-complete (Seqₗ {P} p Q) (Bot .(Seq _ Q)) = inj₂ (Seqₗ p Q , ¬>-Seqₗ (¬>-refl p) Q , ≤-Bot (Seqₗ p Q))
¬>-complete (Seqₗ p Q) (Top .(Seq _ Q)) = inj₁ (≤-Top (Seqₗ p Q))
¬>-complete (Seqₗ p Q) (Seqₗ x .Q) = case ¬>-complete p x of λ { (inj₁ l) → inj₁ (≤-Seqₗ l Q) ; (inj₂ (q , n , l)) → inj₂ (Seqₗ q Q , ¬>-Seqₗ n Q , ≤-Seqₗ l Q) }
¬>-complete (Seqₗ p Q) (Seqᵣ P x) = inj₁ (≤-Seqₗ-Seqᵣ p x)
¬>-complete (Seqᵣ P p) (Bot .(Seq P _)) = inj₂ (Seqᵣ P p , ¬>-refl (Seqᵣ P p) , ≤-Bot (Seqᵣ P p))
¬>-complete (Seqᵣ P p) (Top .(Seq P _)) = inj₁ (≤-Top (Seqᵣ P p))
¬>-complete (Seqᵣ P p) (Seqₗ x Q) = inj₂ (Seqᵣ P p , ¬>-Seqᵣ P (¬>-refl p) , ≤-Seqₗ-Seqᵣ x p)
¬>-complete (Seqᵣ P q) (Seqᵣ .P x) = case ¬>-complete q x of λ { (inj₁ l) → inj₁ (≤-Seqᵣ P l) ; (inj₂ (q , n , l)) → inj₂ (Seqᵣ P q , ¬>-Seqᵣ P n , ≤-Seqᵣ P l) }
¬>-complete (Ifₗ p Q) (Bot .(If _ Q)) = inj₂ (Ifₗ p Q , ¬>-refl (Ifₗ p Q) , ≤-Bot (Ifₗ p Q))
¬>-complete (Ifₗ p Q) (Top .(If _ Q)) = inj₁ (≤-Top (Ifₗ p Q))
¬>-complete (Ifₗ p Q) (Ifₗ p' .Q) = case ¬>-complete p p' of λ { (inj₁ l) → inj₁ (≤-Ifₗ l Q) ; (inj₂ (q , n , l)) → inj₂ (Ifₗ q Q , ¬>-Ifₗ n Q , ≤-Ifₗ l Q) }
¬>-complete (Ifₗ p Q) (Ifᵣ P q') = inj₂ (Ifᵣ P (Top Q) , ¬>-Ifₗ' p Q , ≤-Ifᵣ P (≤-Top q'))
¬>-complete (Ifᵣ P p) (Bot .(If P _)) = inj₂ (Ifᵣ P p , ¬>-refl (Ifᵣ P p) , ≤-Bot (Ifᵣ P p))
¬>-complete (Ifᵣ P p) (Top .(If P _)) = inj₁ (≤-Top (Ifᵣ P p))
¬>-complete (Ifᵣ P p) (Ifₗ p' Q) = inj₂ (Ifₗ (Top P) Q , ¬>-Ifᵣ' P p , ≤-Ifₗ (≤-Top p') Q)
¬>-complete (Ifᵣ P q) (Ifᵣ .P q') = case ¬>-complete q q' of λ { (inj₁ l) → inj₁ (≤-Ifᵣ P l) ; (inj₂ (r , n , l)) → inj₂ (Ifᵣ P r , ¬>-Ifᵣ P n , ≤-Ifᵣ P l) }
¬>-complete (While np) (Bot .(While _)) = inj₂ (While np , ¬>-refl (While np) , ≤-Bot (While np))
¬>-complete (While np) (Top .(While _)) = inj₁ (≤-Top (While np))
¬>-complete (While (zero , p)) (While (zero , p')) = case ¬>-complete p p' of λ { (inj₁ l) → inj₁ (≤-Whileₚ l) ; (inj₂ (q , n , l)) → inj₂ (While (zero , q) , ¬>-While zero n , ≤-Whileₚ l) }
¬>-complete (While (zero , p)) (While (suc n' , p')) = inj₁ (≤-Whileₙ' (s≤s z≤n) p p')
¬>-complete (While (suc n , p)) (While (zero , p')) = inj₂ (While (suc n , p) , ¬>-refl (While (suc n , p)) , ≤-Whileₙ' (s≤s z≤n) p' p)
¬>-complete (While (suc n , p)) (While (suc n' , p')) = case ¬>-complete (While (n , p)) (While (n' , p')) of λ { (inj₁ l) → inj₁ (≤-While-suc l) ; (inj₂ (q , n , l)) → inj₂ ({!!} , {!!} , {!!}) }
