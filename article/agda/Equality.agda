module Equality where

open import Relation.Binary.PropositionalEquality

≡-trans : {A : Set} {a b c : A} → (a ≡ b) → (b ≡ c) → (a ≡ c)
≡-trans refl refl = refl

≡-sym : {A : Set} {a b : A} → (a ≡ b) → (b ≡ a)
≡-sym refl = refl

coe : {A B : Set} → (A ≡ B) → A → B
coe refl x = x

transport : {A : Set} (B : A → Set) {x y : A} (p : x ≡ y) → B x → B y
transport B refl x = x

