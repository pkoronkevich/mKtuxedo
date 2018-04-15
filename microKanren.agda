module microKanren where

open import Data.Empty
open import Data.Unit hiding (_≟_)
open import Data.Nat renaming (_≟_ to _ℕ=_ ) 
open import Data.String hiding ( _==_ ; show)
open import Data.Vec hiding (_∈_)
open import Data.List hiding ([_]) 
open import Data.Sum
open import Data.Nat.Show
open import Data.Colist hiding (_∈_ ; [_])
open import Agda.Builtin.Coinduction

open import Data.Product
open import Relation.Nullary
open import Relation.Binary
open import Relation.Nullary.Decidable
open import Relation.Binary.PropositionalEquality hiding ([_])
open ≡-Reasoning

--------------- Type declarations ---------------
Var : Set
Var = Vec String 1

var : String → Var
var c = [ c ]

data Val : Set where
  VNum  : ℕ → Val 
  VStr  : String → Val
  VList : List Val → Val
  VVar  : Var → Val
  
data _var=_ : Var → Var → Set where
  isEqual : ∀ {s s'} → {α : True (s ≟ s')} → [ s ] var= [ s' ]

data _val=?_ : Val → Val → Set where
  num=?  : ∀ {n m} → (n ≡ m) → (VNum n) val=? (VNum m)
  str=?  : ∀ {s s'} → (s ≡ s') → (VStr s) val=? (VStr s')
  mtlist=? : (VList []) val=? (VList [])

data Subst : Set where
  □   : Subst 
  _,_ : (Var × Val) → Subst → Subst

data _∈_ : (Var × Val) → Subst → Set where
  here : ∀ {s x v} → (x , v) ∈ ((x , v) , s)
  skip : ∀ {s x v x' v'} →
   {α : False (x ≟ x')} → ((var x) , v) ∈ s → ((var x) , v) ∈ (([ x' ] , v') , s)

data _∉_ : Var → Subst → Set where
  empty : ∀ {x} → x ∉ □
  nope  : ∀ {s x x' v'} → {α : False (x ≟ x')} →
   (var x) ∉ s → (var x) ∉ (([ x' ] , v') , s)


extend : Var → Val → Subst → Subst
extend x v s = (x , v) , s

data _walks_to_ : Subst → Val → Val → Set where
  walkN : ∀ {s x} → s walks (VNum x) to (VNum x)
  walkS : ∀ {s x} → s walks (VStr x) to (VStr x)
  walkL : ∀ {s x} → s walks (VList x) to (VList x)
  walkFr : ∀ {s x} → x ∉ s → s walks (VVar x) to (VVar x)
  walkGo : ∀ {s x v x'} → s walks x' to v → (x , x') ∈ s →
            s walks (VVar x) to v

data _unifies_w/_to_ : Subst → Val → Val → Subst → Set where
  Uvars : ∀ {u v s u' v'} → {α : True (u' ≟ v')}
    → s walks (VVar u) to (VVar (var u')) → s walks (VVar v) to (VVar (var v'))
    → s unifies (VVar u) w/ (VVar v) to s
  UvarL : ∀ {u v s u' v'} →
    s walks (VVar u) to (VVar u') → s walks v to v' →
    s unifies (VVar u) w/ v to (extend u' v' s)
  UvarR : ∀ {u v s u' v'} →
    s walks u to u' → s walks (VVar v) to (VVar v') →
    s unifies u w/ (VVar v) to (extend v' u' s)
  Ulists : ∀ {u v s s' s'' u' v' α β} →
    s walks u to (VList (α ∷ u')) → s walks v to (VList (β ∷ v')) →
    s unifies α w/ β to s' → s unifies (VList u') w/ (VList v') to s'' →
    s unifies u w/ v to s''
  Uvals : ∀ {u v s u' v'} →
    s walks u to u' → s walks v to v' → (u' val=? v') → s unifies u w/ v to s

-- examples of unify
s1 : Subst
s1 = ((var "x") , (VVar (var "y"))) , ((var "y") , (VNum 3)) , □ 

t1 : s1 unifies (VNum 3) w/ (VNum 3) to s1
t1 = Uvals walkN walkN (num=? refl)

t2 : s1 unifies (VVar (var "x")) w/ (VNum 3) to s1
t2 = Uvals (walkGo (walkGo walkN (skip here)) here) walkN (num=? refl)

t3 : s1 unifies (VVar (var "z")) w/ (VVar (var "y")) to (((var "z") , (VNum 3)) , s1)
t3 = UvarL (walkFr (nope (nope empty))) (walkGo walkN (skip here))

-- substitution and counter
State : Set
State = Subst × ℕ

Unit : Set
Unit = List State

unit : State → Unit
unit s = s ∷ []

data Fail : Set where
  sucks : Fail

_∈?_ : Decidable _∈_
x ∈? □ = no (λ ())
((x ∷ [])  , v)  ∈? (((x₁ ∷ [])  , v₁) , s) with (x ≟ x₁) 
...                                         | (yes refl) = {!!}
...                                         | (no noteq) with ((x ∷ [])  , v) ∈? s
...                                                  | yes later = yes (skip later)
...                                                  | no never = {!!}

walk : (u : Val) → (s : Subst) → Σ[ v ∈ Val ] (s walks u to v)
walk (VNum x) s = (VNum x) , walkN
walk (VStr x) s = (VStr x) , walkS
walk (VList x) s = (VList x) , walkL
walk (VVar x) s = {!!}
unify-help-num : (n : ℕ) → (m : ℕ) → (s : Subst) → Fail ⊎ Σ[ s' ∈ Subst ] (s unifies (VNum n) w/ (VNum m) to s')
unify-help-num n m s with n ℕ= m
...                  | (yes p) = inj₂ (s , Uvals walkN walkN (num=? p))
...                  | (no _) = inj₁ sucks 


unify-help-str : (u : String) → (v : String) → (s : Subst) → Fail ⊎ Σ[ s' ∈ Subst ] (s unifies (VStr u) w/ (VStr v) to s')
unify-help-str u v s with u ≟ v
...                  | (yes p) = inj₂ (s , Uvals walkS walkS (str=? p))
...                  | (no _) = inj₁ sucks 

unify : (u : Val) → (v : Val) → (s : Subst) → Fail ⊎ Σ[ s' ∈ Subst ] (s unifies u w/ v to s')
unify (VNum x) (VNum x₁) s = unify-help-num x x₁ s
unify (VNum x) (VStr x₁) s = inj₁ sucks
unify (VNum x) (VList x₁) s = inj₁ sucks
unify (VNum x) (VVar x₁) s = {!!}
unify (VStr x) (VNum x₁) s = {!!}
unify (VStr x) (VStr x₁) s = unify-help-str x x₁ s
unify (VStr x) (VList x₁) s = inj₁ sucks
unify (VStr x) (VVar x₁) s = {!!}
unify (VList x) (VNum x₁) s = inj₁ sucks
unify (VList x) (VStr x₁) s = inj₁ sucks
unify (VList x) (VList x₁) s = {!!}
unify (VList x) (VVar x₁) s = {!!}
unify (VVar x) (VNum x₁) s = {!!}
unify (VVar x) (VStr x₁) s = {!!}
unify (VVar x) (VList x₁) s = {!!}
unify (VVar x) (VVar x₁) s = {!!} 

==-helper : ∀ {s u v} → ℕ → Fail ⊎ Σ[ s' ∈ Subst ] (s unifies u w/ v to s') → State
==-helper n (inj₁ x) = (□ , n)
==-helper n (inj₂ (s' , unif)) = (s' , n)

_==_ : Val → Val → State → State
u == v = λ s/c → let c = (proj₂ s/c)
                     res = unify u v (proj₁ s/c)
                 in ==-helper c res

call/fresh : (Var → State → State) → State → State
call/fresh f = λ s/c → let c = (proj₂ s/c)
                       in f (var (show c)) ((proj₁ s/c) , suc c)
































---  conj and disj
-- data MPlus : State → Set where
--   mzero : ∀ {s} → MPlus s


-- alt, using streams
  
  
data MPlus : (Colist State) -> Set where
  --  mzero : ∀ {s} → MPlus s


Ans : Set
Ans = Colist State

mzero : Ans
mzero = []


mplus : Ans → Ans → Ans
mplus [] b = b
mplus (x ∷ xs) b = x ∷ ♯ (mplus b (♭ xs))


Goal : Set
Goal = State → Ans

{-# TERMINATING #-}
bind : Ans → Goal → Ans
bind [] g = mzero
bind (x ∷ xs) g = mplus (g x) (bind (♭ xs) g)

disj : Goal → Goal → State → Ans
disj g1 g2 = λ s/c → mplus (g1 s/c) (g2 s/c)

conj : Goal → Goal → State → Ans
conj g1 g2 = λ s/c → bind (g1 s/c) g2


----- Simple proofs

coDbl : Ans → Ans
coDbl [] = []
coDbl (x ∷ xs) = x ∷ ♯ (x ∷ (♯ (coDbl (♭ xs))))



disj-id : ∀ {s} → (g : Goal)  → (disj g g s) ≡ (coDbl (g s))
disj-id {s} g with (g s)
...          | [] = refl
...          | (x ∷ xs) = 
               begin
                mplus (x ∷ xs) (x ∷ xs)
                ≡⟨ {!refl!} ⟩
                x ∷  ♯ (mplus (x ∷ xs) (♭ xs))
                ≡⟨ {!!} ⟩
                {!!} -- x ∷ ♯ (x ∷ (♯ (coDbl (♭ xs))))
                ≡⟨ refl ⟩
                coDbl (x ∷ xs)∎


-- conj-lemma₂ : ∀ {s} → (a₁ a₂ : Ans) → {g₁ g₂ : Goal} → (a₁ ≡ (g₂ s)) → (a₂ ≡ (g₁ s)) → bind a₁ g₁ ≡ bind a₂ g₂
{-- conj-lemma₂ [] [] {g₁} {g₂} p₁ p₂ = refl
conj-lemma₂ [] (x ∷ xs) {g₁} {g₂} p₁ p₂ = {!!}
conj-lemma₂ (x ∷ xs) [] {g₁} {g₂} p₁ p₂ = {!!}
conj-lemma₂ (x ∷ xs) (x₁ ∷ xs₁) {g₁} {g₂} p₁ p₂ = 
            begin
              bind (x ∷ xs) g₁
              ≡⟨ refl ⟩
              mplus (g₁ x) (bind (♭ xs) g₁)
              ≡⟨ {!!} ⟩
              mplus (g₂ x₁) (bind (♭ xs) g₁) 
              ≡⟨ cong (λ q → mplus (g₂ x₁) q) (conj-lemma₂ (♭ xs₁) ⟩
              mplus (g₂ x₁) (bind (♭ xs₁) g₂)
              ≡⟨ refl ⟩
              bind (x₁ ∷ xs₁) g₂ ∎ --} 
conj-lemma : (g1 g2 : Goal) → {s : State} → bind (g1 s) g2 ≡ bind (g2 s) g1
conj-lemma g1 g2 {s} with (g1 s) | (g2 s) 
...                  |  [] | [] = refl
...                  |  [] | (x ∷ xs) =
                             begin
                               bind [] g2
                               ≡⟨ refl ⟩
                               mzero
                               ≡⟨ {!!} ⟩
                               bind (x ∷ xs) g1 ∎
...                  |  (x ∷ xs) | [] = {!!}
...                  |  (x ∷ xs) | (x₂ ∷ xs₂)= {!!} 

conj-comm : (g1 g2 : Goal) → {s : State} → conj g1 g2 s ≡ conj g2 g1 s
conj-comm g1 g2 {s} = conj-lemma g1 g2 {s}

-- conj-assoc : (g1 g2 g3 : Goal) → {s : State} → (bind (conj g1 g2 s) g3) ≡ ( (conj g1 g2 s) g3 s)
-- conj-assoc = ?
