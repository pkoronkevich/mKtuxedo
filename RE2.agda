module RE2 where

open import Data.String
open import Data.Char hiding (_≟_)
open import Agda.Builtin.Char
open import Data.List hiding (_++_; concat)
open import Data.Bool hiding (_≟_)
open import Data.Nat hiding (_≟_)
open import Data.Product
open import Data.Sum
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
... | yes pp = false , (Cons x₁ ls)
... | no _ with (set/cons x ls)
...          | true , res = true , (Cons x₁ res)
...          | false , res = false , (Cons x₁ res)

set/cons x ($ v) = true , (Cons x [])

take/set : ℕ → (Stream String) → (Stream String) → (Stream String)
take/set zero ls ans = ans
take/set (suc n) [] ans = ans
take/set (suc n) (Cons a d) ans 
  with (set/cons a ans)
... | true , res  = (take/set n d res)
... | false , res = (take/set (suc n) d res)
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
a₃ = get-chars 5 e₃

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


--------------------
--------------------
-- Prinf of arbitrary RE's with dependent types!

{--

Types of inputs
%s → String
%n → Num
%c → Char
%(α) → RE

--}

Word : Set
Word = String

data Printfn : Set where
  return   : RE → Printfn
  takeStr  : (String → Printfn) → Printfn
  takeChar : (Char → Printfn) → Printfn
  takeNum  : (ℕ → Printfn) → Printfn
  concat   : Printfn → Printfn → Printfn
  disj     : Printfn → Printfn → Printfn
  star     : Printfn → Printfn
  plus     : Printfn → Printfn


-- toString helpers
doC : Char → RE
doC c = (Sym (fromList (c ∷ [])))


N→C : ℕ → Char
N→C 0 = '0'
N→C (suc n) = (primNatToChar (suc (primCharToNat (N→C n))))

doN : ℕ → RE
doN n = doC (N→C n)



splitLP : (List Char) → (List Char) → (((List Char) × (List Char)) ⊎ ℕ)
splitLP [] ls = (inj₂ 0)
splitLP (')' ∷ xs) [] = inj₁ ([] , xs)
splitLP (')' ∷ xs) (p ∷ ps) with (splitLP xs ps)
...                | (inj₁ (e₁ , e₂)) = (inj₁ (e₁ , e₂))
...                | (inj₂ _) = (inj₂ 0)
splitLP ('(' ∷ xs) ps with (splitLP xs ('(' ∷ ps))
...               | (inj₁ (e₁ , e₂)) = inj₁ (e₁ , e₂)
...               | (inj₂ _) = inj₂ 0
splitLP (x ∷ xs) ps with (splitLP xs ps)
...               | (inj₁ (e₁ , e₂)) = (inj₁ ((x ∷ e₁) , e₂))
...               | (inj₂ _) = (inj₂ 0)

makeRE : (List Char) → Printfn

{-# TERMINATING #-}
split : (List Char) → ((Printfn × Printfn) ⊎ ℕ)
split [] = (inj₂ 0)
split (a ∷ []) = (inj₂ 0)
split ('%' ∷ 'c' ∷ xs) = (inj₁ ((takeChar (λ c → (return (doC c)))) , (makeRE xs)))
split ('%' ∷ 's' ∷ xs) = (inj₁ ((takeStr (λ st → (return (Sym st)))) , (makeRE xs)))
split ('%' ∷ 'n' ∷ xs) = (inj₁ ((takeNum (λ n → (return (doN n)))) , (makeRE xs)))
split ('(' ∷ xs)
  with (splitLP xs [])
... | (inj₁ (e₁ , e₂)) = (inj₁ (makeRE e₁ , (makeRE e₂)))
... | inj₂ _ = inj₂ 0
split (' ' ∷ xs) = (inj₁ ((return ε) , (makeRE xs))) 
split (x ∷ ls) with (split ls)
...             | (inj₁ (e₁ , e₂)) = (inj₁ ((concat (return (doC x)) e₁) , e₂))
...             | (inj₂ _) = (inj₂ 0)

makeRE [] = return ε
makeRE ('%' ∷ []) = return ∅
makeRE ('∪' ∷ ' ' ∷ xs) with (split xs)
...                | (inj₁ (e₁ , e₂)) = disj e₁ e₂
...                | (inj₂ _) = return ∅  
makeRE ('∪' ∷ xs) with (split xs)
...                | (inj₁ (e₁ , e₂)) = disj e₁ e₂
...                | (inj₂ _) = return ∅  
makeRE ('•' ∷ ' ' ∷ xs) with (split xs)
...                | (inj₁ (e₁ , e₂)) = concat e₁ e₂
...                | (inj₂ _) = return ∅  
makeRE ('•' ∷ xs) with (split xs)
...                | (inj₁ (e₁ , e₂)) = concat e₁ e₂
...                | (inj₂ _) = return ∅  
makeRE ('*' ∷ xs) = (star (makeRE xs))
makeRE ('+' ∷ xs) = (plus (makeRE xs))
makeRE ('%' ∷ 's' ∷ []) = (takeStr (λ str → (return (Sym str))))
makeRE ('%' ∷ 'c' ∷ []) = (takeChar (λ c → (return (doC c))))
makeRE ('%' ∷ 'n' ∷ []) = (takeNum (λ n → (return (doN n))))
makeRE ('%' ∷ c ∷ []) = return ∅
makeRE (a ∷ xs) = concat (return (doC a)) (makeRE xs)

{-# TERMINATING #-}
parse' : (List Char) → Printfn
parse' [] = return ε
parse' ('%' ∷ []) = return ∅
parse' (x ∷ []) = return (doC x)
parse' ('%' ∷ '(' ∷ xs) 
   with (splitLP xs [])
...  | (inj₁ (e , res)) = (concat (makeRE e) (parse' res))
...  | (inj₂ _) = (return ∅)

parse' ('%' ∷ c ∷ xs)
 with (parse' xs) | c 
-- taking a string
... | (return r) | 's' = (takeStr (λ str → (return (• (Sym str) r))))
... | (takeStr f) | 's' = (takeStr (λ str₁ → (takeStr (λ str₂ → (concat (return (Sym str₁)) (f str₂)))))) 
... | (takeChar f) | 's' = (takeStr (λ str₁ → (takeChar (λ str₂ → (concat (return (Sym str₁)) (f str₂)))))) 
... | (takeNum f) | 's' = (takeStr (λ str₁ → (takeNum (λ str₂ → (concat (return (Sym str₁)) (f str₂)))))) 
... | (concat e₁ e₂) | 's' = (takeStr (λ str₁ → (concat (return (Sym str₁)) (concat e₁ e₂)))) 
... | (disj e₁ e₂) | 's' = (takeStr (λ str₁ → (concat (return (Sym str₁)) (disj e₁ e₂)))) 
... | (star e) | 's' = (takeStr (λ str₁ → (concat (return (Sym str₁)) (star e)))) 
... | (plus e) | 's' = (takeStr (λ str₁ → (concat (return (Sym str₁)) (plus e)))) 
-- taking a char
... | (return r) | 'c' = (takeChar (λ c → (return (• (doC c) r))))
... | (takeStr f) | 'c' = (takeChar (λ c → (takeStr (λ str₂ → (concat (return (doC c)) (f str₂)))))) 
... | (takeChar f) | 'c' = (takeChar (λ c → (takeChar (λ str₂ → (concat (return (doC c)) (f str₂)))))) 
... | (takeNum f) | 'c' = (takeChar (λ c → (takeNum (λ str₂ → (concat (return (doC c)) (f str₂)))))) 
... | (concat e₁ e₂) | 'c' = (takeChar (λ c → (concat (return (doC c)) (concat e₁ e₂)))) 
... | (disj e₁ e₂) | 'c' = (takeChar (λ c → (concat (return (doC c)) (disj e₁ e₂)))) 
... | (star e) | 'c' = (takeChar (λ c → (concat (return (doC c)) (star e)))) 
... | (plus e) | 'c' = (takeChar (λ c → (concat (return (doC c)) (plus e)))) 
-- taking a number
... | (return r) | 'n' = (takeNum (λ c → (return (• (doN c) r))))
... | (takeStr f) | 'n' = (takeNum (λ c → (takeStr (λ str₂ → (concat (return (doN c)) (f str₂)))))) 
... | (takeChar f) | 'n' = (takeNum (λ c → (takeChar (λ str₂ → (concat (return (doN c)) (f str₂)))))) 
... | (takeNum f) | 'n' = (takeNum (λ c → (takeNum (λ str₂ → (concat (return (doN c)) (f str₂)))))) 
... | (concat e₁ e₂) | 'n' = (takeNum (λ c → (concat (return (doN c)) (concat e₁ e₂)))) 
... | (disj e₁ e₂) | 'n' = (takeNum (λ c → (concat (return (doN c)) (disj e₁ e₂)))) 
... | (star e) | 'n' = (takeNum (λ c → (concat (return (doN c)) (star e)))) 
... | (plus e) | 'n' = (takeNum (λ c → (concat (return (doN c)) (plus e)))) 
-- ill-formed error case
... | (return r) | bad = (return ∅) 
... | (takeStr f) | bad = (return ∅)
... | (takeChar f) | bad = (return ∅)
... | (takeNum f) | bad = (return ∅)
... | (concat e₁ e₂) | bad = (return ∅) 
... | (disj e₁ e₂) | bad = (return ∅) 
... | (star e) | bad = (return ∅)
... | (plus e) | bad = (return ∅)
parse' (a ∷ b ∷ xs) = (concat (return (doC a)) (parse' (b ∷ xs)))


data Input : Set where
   N : ℕ → Input
   S : String → Input
   C : Char → Input

ass1 : ℕ → ℕ
ass1 n = suc n

countArgs : Printfn →  ℕ
countArgs (return x) = 0
countArgs (takeStr x) = (ass1 (countArgs (x "s")))
countArgs (takeChar x) = (ass1 (countArgs (x 'c')))
countArgs (takeNum x) = (ass1 (countArgs (x 0)))
countArgs (concat n n₁) = (countArgs n) Data.Nat.+ (countArgs n₁)
countArgs (disj n n₁) = (countArgs n) Data.Nat.+ (countArgs n₁)
countArgs (star n) = (countArgs n)
countArgs (plus n) = (countArgs n)


use-printfn : Printfn → (List Input) → RE
use-printfn (return x) [] = x
use-printfn (return x) (x₁ ∷ l) = ∅
use-printfn (takeStr x) [] = ∅
use-printfn (takeStr x) (N x₁ ∷ l) = ∅
use-printfn (takeStr x) (S x₁ ∷ l) = use-printfn (x x₁) l
use-printfn (takeStr x) (C x₁ ∷ l) = ∅
use-printfn (takeChar x) [] = ∅
use-printfn (takeChar x) (N x₁ ∷ l) = ∅
use-printfn (takeChar x) (S x₁ ∷ l) = ∅
use-printfn (takeChar x) (C x₁ ∷ l) = use-printfn (x x₁) l
use-printfn (takeNum x) [] = ∅
use-printfn (takeNum x) (N x₁ ∷ l) = use-printfn (x x₁) l
use-printfn (takeNum x) (S x₁ ∷ l) = ∅
use-printfn (takeNum x) (C x₁ ∷ l) = ∅
use-printfn (concat p p₁) ls =
  let argsₚ = (countArgs p)
      res   = (splitAt argsₚ ls) in
      (• (use-printfn p (proj₁ res)) (use-printfn p₁ (proj₂ res))) 
use-printfn (disj p p₁) ls =
  let argsₚ = (countArgs p)
      res   = (splitAt argsₚ ls) in
      (∪ (use-printfn p (proj₁ res)) (use-printfn p₁ (proj₂ res)))
use-printfn (star p) ls = (* (use-printfn p ls))
use-printfn (plus p) ls = (+ (use-printfn p ls))

print : ℕ → String → (List Input) → (Stream String)  
print n w ins =
  let p = (parse' (toList w))
      r = use-printfn p ins in
    get-chars n r



sₒ s₁ s₂ s₃ : Word
sₒ = "Hello %(*%s) are you having a %(∪%s%s) day on November %(∪%n%n)th?"
s₁ = "Dear Resident of %(∪%n (∪%n %n)) %(∪%s %s) street, here's some chars: %(+ (∪ %c %c))."
s₂ = "My favorite colors are %(* (∪ %s %s))"
s₃ = "%(•%s (∪%s (∪%s %n)))"

ansₒ : (Stream String)
ansₒ = print 10 sₒ ((S "Paul") ∷ (S "good") ∷ (S "bad") ∷ (N 3) ∷ (N 8) ∷ [])

ans₁ : (Stream String)
ans₁ = print 10 s₁ ((N 1) ∷ (N 2) ∷ (N 3) ∷ (S "Madison") ∷ (S "MLK") ∷  (C 'g') ∷ (C 'f') ∷ [])

ans₂ : (Stream String)
ans₂ = print 10 s₂ ((S "red") ∷ (S "green") ∷ [])

ans₃ : (Stream String)
ans₃ = print 10 s₃ ((S "1") ∷ (S "2") ∷ (S "hi") ∷ (N 3) ∷ [])
