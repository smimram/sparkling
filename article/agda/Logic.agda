module Logic where

_and_ : (A : Set) (B : Set) → Set
infixr 2 _and_
A and B = A × B

_or_ : (A : Set) (B : Set) → Set
infixr 1 _or_
A or B = A ⊎ B
