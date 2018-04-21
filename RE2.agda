module RE2 where

open import Data.String
open import Data.List hiding (_++_)
open import Data.Bool hiding (_≟_)
open import Data.Nat hiding (_≟_)
open import Data.Product
open import Data.Unit hiding (_≟_)
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

-- The language of regular expressions

data RE : Set where
  ∅   : RE
  ε   : RE
  Sym : String → RE
  ∪   : RE → RE → RE
  •   : RE → RE → RE
  *   : RE → RE
  +   : RE → RE

data Stream : Set → Set where
   []   : {A : Set} → Stream A
   Cons : {A : Set} → (a : A) → (s : Stream A) → (Stream A)
   $    : {A : Set} → (⊤ → Stream A) → (Stream A)


mzero : ∀ {A} → Stream A
mzero {A} = []

mplus : ∀ {A : Set} → Stream A →  Stream A → Stream A
mplus [] $₁ = $₁
mplus (Cons a d) $₁ = (Cons a (mplus $₁ d))
mplus ($ s) $₁ = (mplus $₁ (s tt))

mconj : ∀ {A : Set} → Stream A → (A → Stream A) → (Stream A)
mconj [] f = mzero
mconj (Cons a d) f = (mplus (f a) (mconj d f))
mconj ($ s) f = (mconj (s tt) f)

--------------------------
-- The interpreter -------
--------------------------

{-# TERMINATING #-}
valof : RE → (Stream String)
valof ∅ = mzero
valof ε = (Cons "" [])
valof (Sym x) = (Cons x [])
valof (∪ a b) = (mplus (valof a) (valof b))
valof (• a b) = (mconj (valof a)
                       (λ a → (mconj (valof b) (λ x → (Cons (a ++ x) [])))))
valof (* e) = (mconj (valof e)
                     (λ A → (Cons "" (mconj ($ (λ t → (valof (* e))))
                                            (λ x → (Cons (A ++ x) []))))))
valof (+ e) = valof (• e (* e))

--------------------------------
-- Functions to handle ---------
-- taking the first n members --
-- of a language  --------------
--------------------------------

set/cons : String → (Stream String) → (Bool × (Stream String))
set/cons x [] = true , (Cons x [])
set/cons x (Cons x₁ ls)
  with (x ≟ x₁)
... | yes pp = (false , (Cons x₁ ls))
... | no _ with (set/cons x ls)
...        | (a , res) = a , (Cons x₁ res)
set/cons x ($ v) = true , (Cons x [])

take/set : ℕ → (Stream String) → (Stream String) → (Stream String)
take/set zero ls ans = ans
take/set (suc n) [] ans = ans
take/set (suc n) (Cons a d) ans 
  with (set/cons a ans)
... | (true , res)  = (take/set n d res)
... | (false , res) = (take/set (suc n) d res)
take/set (suc n) ($ x) ans = (take/set (suc n) (x tt) ans)


get-chars : ℕ → RE → (Stream String)
get-chars n e = (take/set n (valof e) [])

----------------------
-- Examples

e₁ e₂ e₃ : RE
e₁ = (• (∪ (Sym "a") (Sym "b")) (Sym "c"))
e₂ = (• (* (Sym "a")) (Sym "c"))
e₃ = (* (• (* (Sym "a")) (∪ (Sym "b") (Sym "c"))))

a₁ a₂ a₃ : (Stream String)
a₁ = get-chars 20 e₁
a₂ = get-chars 10 e₂
a₃ = get-chars 10 e₃

----------------------------
-- Proofs about the system

-- Some helper functions/types

data isList : {A : Set} → (Stream A) → Set where
    empty : ∀ {A s} → isList {A} s
    cons  : ∀ {A l} → {x : A} → isList {A} l → isList (Cons x l)

-- Proof 1: The system always gives a finite list of answers with no stream weirdness
-- (this shows that when valof is used through our interface, it always terminates)
takeStep : ∀ {ans} → (l : Stream String) → (n : ℕ)  → (isList (take/set n l ans) → (isList (take/set (suc n) l ans)))
takeStep l zero p = empty
takeStep [] (suc n) p = p
takeStep (Cons a l) (suc n) p = empty
takeStep ($ x) (suc n) p = takeStep (x tt) (suc n) p

finiteAnswers : (n : ℕ) → (e : RE) → isList (get-chars n e)
finiteAnswers zero e = empty 
finiteAnswers (suc n) e =  takeStep {[]} (valof e) n (finiteAnswers n e)


-- Proof 2 : The elimination of + is correct

+=* : (n : ℕ) → (e : RE) → (get-chars n (+ e)) ≡ (get-chars n (• e (* e)))
+=* n e = refl


