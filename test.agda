module test where

open import Data.Empty
open import Data.Unit hiding (_≟_)
open import Data.Nat renaming (_≟_ to _ℕ=_ ) 
open import Data.String hiding ( _==_ ; show)
open import Data.Vec hiding (_∈_)
open import Data.List hiding ([_])
open import Data.List.Properties
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

return : {A : Set} → (a : A) → M A
return a = a ∷ mzero

monadIdR : {A : Set} → (a : A) → (f : A → M A) → bind (return a) f ≡ f a
monadIdR a f = ++-identityʳ (f a)

monadIdL : {A : Set} → (ma : M A) → bind ma return ≡ ma
monadIdL [] = refl
monadIdL (x ∷ ma) = cong (_∷_ x) (monadIdL ma) 

monadAssocLemma : {A : Set} → (ma ma₂ : M A) → (f g : A → M A) →
  bind (ma₂ Data.List.++ bind ma f) g ≡ bind ma₂ g Data.List.++ (bind (bind ma f) g)
monadAssocLemma ma [] f g = refl
monadAssocLemma ma (x ∷ ma₂) f g =
  begin
  bind ((x ∷ ma₂) Data.List.++ bind ma f) g
  ≡⟨ refl ⟩
  (g x) Data.List.++ bind (ma₂ Data.List.++ bind ma f) g
  ≡⟨ cong (Data.List._++_ (g x)) (monadAssocLemma ma ma₂ f g) ⟩
  (g x) Data.List.++ ((bind ma₂ g) Data.List.++ (bind (bind ma f) g))
  ≡⟨ sym (++-assoc (g x) (bind ma₂ g) (bind (bind ma f) g)) ⟩
  ((g x) Data.List.++ (bind ma₂ g)) Data.List.++ (bind (bind ma f) g)
  ≡⟨ refl ⟩  
  bind (x ∷ ma₂) g Data.List.++ (bind (bind ma f) g) ∎

monadAssoc : {A : Set} → (ma : M A) → (f g : A → M A) → bind (bind ma f) g ≡ bind ma (λ x → bind (f x) g)
monadAssoc [] f g = refl
monadAssoc (a ∷ ma) f g =
  begin
  bind (bind (a ∷ ma) f) g 
  ≡⟨ refl ⟩
  bind ((f a) Data.List.++ bind ma f) g
  ≡⟨ monadAssocLemma ma (f a) f g ⟩
  bind (f a) g Data.List.++ (bind (bind ma f) g)
  ≡⟨ cong (λ y → bind (f a) g Data.List.++ y) (monadAssoc ma f g) ⟩
  bind (f a) g Data.List.++ (bind ma (λ x → bind (f x) g))
  ≡⟨ refl ⟩
  bind (a ∷ ma) (λ x → bind (f x) g) ∎

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

mPlusLemma : {A : Set} → (a : M A) → (x c : A) →  (x ∷ (c ∷ a)) M≡ (c ∷ (x ∷ a)) 
mPlusLemma a x c = {!!} 

mplusCommCong : {A : Set} → (a b : M A) → (x : A) → mplus a b M≡ mplus b a → mplus (x ∷ a) b M≡ mplus b (x ∷ a)
mplusCommCong a [] c p = reflM
mplusCommCong a (x ∷ b) c p = let IH = mplusCommCong a b c
                              in transM {!!} {!!}

{--
begin
  mplus (c ∷ a) (x ∷ b)
  ≡⟨ refl ⟩
  c ∷ x ∷ (mplus a b)
  ≡⟨ ? ⟩
  x ∷ c ∷ (mplus b a)
  ≡⟨ ? ⟩
  mplus (x ∷ b) (c ∷ a)
  --}
{--
mplusCommCong [] [] x = λ _ → reflM
mplusCommCong [] (x₁ ∷ b) x = {!!}
mplusCommCong (x₁ ∷ a) [] x = λ _ → reflM
mplusCommCong (x₁ ∷ a) (x₂ ∷ b) x = {!!}
--}
mPlusComm : {A : Set} → (a b : M A)  → mplus a b M≡ mplus b a
mPlusComm [] b = transM mzeroLeft (symmM mzeroRight)
mPlusComm (x ∷ a) b = 
    let IH = mPlusComm a b
    in mplusCommCong a b x IH
    
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
