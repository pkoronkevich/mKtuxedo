module test where

open import Data.Empty
open import Data.Unit hiding (_≟_)
open import Data.Nat renaming (_≟_ to _ℕ=_ ) 
open import Data.String hiding ( _==_ ; show)
open import Data.Vec hiding (_∈_)
open import Data.List hiding ([_]) 
open import Data.Sum
open import Data.Nat.Show
open import Agda.Builtin.Coinduction

open import Data.Product
open import Relation.Nullary
open import Relation.Binary
open import Relation.Nullary.Decidable
open import Relation.Binary.PropositionalEquality hiding ([_])
open ≡-Reasoning


M : Set → Set
M a = List a


mzero : {a : Set} → M a
mzero = []

mplus : {a : Set} → M a → M a → M a
mplus [] b = b
mplus (x ∷ a) b = x ∷ (mplus b a)

bind : {a : Set} → M a → (a → M a) → M a
-- bind mzero k
bind [] k = mzero
-- bind mplus k
bind (x ∷ ma) k = (k x) Data.List.++ (bind ma k)

-- an equivalence relation for M, which ignores order

foo : (A : Set) → M A
foo A = []

data _∈_ : {A : Set} → (x : A) → (xs : List A) → Set where
  here : ∀ {A} → {a : A} → {as : List A} → a ∈ (a ∷ as)
  skip : ∀ {A} → {a b : A} → {as : List A} → a ∈ as → a ∈ (b ∷ as)

data _⊂_ : {A : Set} → (a b : M A) → Set where  
     nil⊂ : ∀ {A} → {b : M A} → (foo A) ⊂ b
     add⊂ : ∀ {A} → {a : A} → {as b : M A} → a ∈ b → as ⊂ b → (a ∷ as) ⊂ b
     
data _M≡_ : {A : Set} → M A → M A → Set where
   reflM : {A : Set} {a : M A} →  (a M≡ a)
   symmM : {A : Set} {a b : M A} → (a M≡ b) → (b M≡ a)
   transM : {A : Set} {a b c : M A} → (a M≡ b) → (b M≡ c) → (a M≡ c)
   subsetsM   : {A : Set} {a b : M A} → (a ⊂ b) → (b ⊂ a) → (a M≡ b)

congM : {A : Set} → {a b : M A} → (f : M A → M A) → a M≡ b → (f a) M≡ (f b)
congM f reflM = reflM
congM f (symmM a=b) = symmM (congM f a=b)
congM f (transM a=b a=b₁) = transM (congM f a=b) (congM f a=b₁)
congM f (subsetsM x x₁) = {!!} 

mzeroRight : {A : Set} → {a : M A} → mplus a mzero M≡ a
mzeroRight {A} {[]} = reflM
mzeroRight {A} {x ∷ a} = reflM

mzeroLeft : {A : Set} → {a : M A} → mplus mzero a M≡ a
mzeroLeft {A} {a} = reflM

-- mPlusCommLem : ∀ {A : Set} → 

mPlusComm : {A : Set} → (a b : M A)  → mplus a b M≡ mplus b a
mPlusComm [] b = transM mzeroLeft (symmM mzeroRight)
mPlusComm (x ∷ a) b = 
    let IH = mPlusComm a b
    in {!!}
mPlusAssoc : {A : Set} → {a b c : M A} → mplus a (mplus b c) M≡ mplus (mplus a b) c
mPlusAssoc {A} {[]} {b} {c} = reflM
mPlusAssoc {A} {x ∷ a} {b} {c} = {!!}

{--
begin
mplus (x ∷ a) (mplus b c)
≡⟨ reflM ⟩
x ∷ mplus (mplus b c) a
≡⟨ {!!} ⟩
x ∷ mplus c (mplus b a)
≡⟨ reflM ⟩
mplus (x ∷ (mplus b a)) c
≡⟨ reflM ⟩
mplus (mplus (x ∷ a) b) c ∎ --}
