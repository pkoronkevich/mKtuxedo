module microKanren where

open import Data.Empty
open import Data.Unit hiding (_≟_)
open import Data.Nat hiding (_≟_)
open import Data.String hiding ( _==_ ; show)
open import Data.Vec hiding (_∈_)
open import Data.List hiding ([_]) 
open import Data.Sum
open import Data.Nat.Show

open import Data.Product
open import Relation.Nullary
open import Relation.Binary
open import Relation.Nullary.Decidable
open import Relation.Binary.PropositionalEquality hiding ([_])


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

-- _∈?_ : Decidable _∈_
-- (x , v) ∈? □ = no (λ ())
-- (  x ∷ [] , v) ∈? (( x' ∷ [] , v') , s) = if (x == x') then yes here else ?

data _∉_ : Var → Subst → Set where
  empty : ∀ {x} → x ∉ □
  nope  : ∀ {s x x' v'} → {α : False (x ≟ x')} →
   (var x) ∉ s → (var x) ∉ (([ x' ] , v') , s)


extend : Var → Val → Subst → Subst
extend x v s = (x , v) , s

data _walks_to_ : Subst → Val → Val → Set where
  walkN : ∀ {s x} → s walks (VNum x) to (VNum x)
  walkS : ∀ {s x} → s walks (VStr x) to (VStr x)
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

unify : (u : Val) → (v : Val) → (s : Subst) → Fail ⊎ Σ[ s' ∈ Subst ] (s unifies u w/ v to s')
unify u v s = {!!} 

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

