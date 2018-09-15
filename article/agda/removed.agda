open import Data.Nat.Base renaming (_≤_ to _≤ℕ_) renaming (_⊔_ to _⊔ℕ_) renaming (Ordering to ℕ-Ordering) renaming (compare to ℕ-compare)

-- data ℕ-Ordering (m : ℕ) (n : ℕ) : Set → Set where
  -- lt : ℕ-Ordering m n (m ≤ℕ suc n)
  -- eq : ℕ-Ordering m n (m ≡ n)
  -- gt : ℕ-Ordering m n (n ≤ℕ suc m)

-- ℕ-compare : (m : ℕ) (n : ℕ) → ℕ-Ordering m n
-- ℕ-compare = ?

ℕ-compare-prop : {m n : ℕ} → ℕ-Ordering m n → Set
ℕ-compare-prop {m} {n} (less _ _) = m ≤ℕ suc n
ℕ-compare-prop {m} {n} (equal _) = m ≡ n
ℕ-compare-prop {m} {n} (greater _ _) = n ≤ℕ suc m

≤ℕ-trans : {m n p : ℕ} → (m ≤ℕ n) → (n ≤ℕ p) → (m ≤ℕ p)
≤ℕ-trans {.0} {n} {p} z≤n l' = z≤n
≤ℕ-trans {.(suc _)} {.(suc _)} {.(suc _)} (s≤s l) (s≤s l') = s≤s (≤ℕ-trans l l')

≤ℕ-refl : (n : ℕ) → (n ≤ℕ n)
≤ℕ-refl zero = z≤n
≤ℕ-refl (suc n) = s≤s (≤ℕ-refl n)

s≤ : (n : ℕ) → n ≤ℕ suc n
s≤ zero = z≤n
s≤ (suc n) = s≤s (s≤ n)

≤s : {m n : ℕ} → (m ≤ℕ n) → (m ≤ℕ suc n)
≤s {zero} {n} l = z≤n
≤s {suc m} {n} l = s≤s (≤ℕ-trans (s≤ m) l)

+-r-≤ : (m n : ℕ) → n ≤ℕ m + n
+-r-≤ zero n = ≤ℕ-refl n
+-r-≤ (suc m) n = ≤s (+-r-≤ m n)

+-sym : (m n : ℕ) → m + n ≡ n + m
+-sym zero zero = refl
+-sym zero (suc n) = cong (λ n → suc n) (+-sym zero n)
+-sym (suc m) zero = cong (λ n → suc n) (+-sym m zero)
+-sym (suc m) (suc n) = cong (λ n → suc n) {!!}

ℕ-compare-sound : {m n : ℕ} → ℕ-compare-prop (ℕ-compare m n)
ℕ-compare-sound {zero} {zero} = refl
ℕ-compare-sound {zero} {suc n} = z≤n
ℕ-compare-sound {suc m} {zero} = z≤n
ℕ-compare-sound {suc m} {suc n} with ℕ-compare m n
ℕ-compare-sound {suc .m} {suc n} | less m k = s≤s (≤s (≤s {!!}))
ℕ-compare-sound {suc .m} {suc .m} | equal m = refl
ℕ-compare-sound {suc .(suc m + k)} {suc .m} | greater m k = s≤s {!!}
