module microKanren where

open import Data.Empty
open import Data.Unit hiding (_≟_)
open import Data.Nat hiding (_≟_)
open import Data.String hiding (_==_)
open import Data.Vec hiding (_∈_)
open import Data.List hiding ([_]) 
open import Data.Sum

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
   {α : False (x ≟ x')} → ((var x)  , v) ∈ s → ((var x)  , v) ∈ (([ x' ] , v') , s)

extend : Var → Val → Subst → Subst
extend x v s = (x , v) , s

data _walks_to_ : Subst → Val → Val → Set where
  walkN : ∀ {s x v} → s walks (VNum x) to v
  walkS : ∀ {s x v} → s walks (VStr x) to v
  walkFr : ∀ {s x v} → ¬ (x , v) ∈ s → s walks (VVar x) to (VVar x)
  walkGo : ∀ {s x v x'} → s walks (VVar x') to v → (x , (VVar x')) ∈ s →
            s walks (VVar x) to v

data _unifies_w/_ : Subst → Val → Val → Set where
  Uvars : ∀ {u v s u' v'} → {α : True (u' ≟ v')}
    → s walks (VVar u) to (VVar (var u')) → s walks (VVar v) to (VVar (var v'))
    → s unifies (VVar u) w/ (VVar v)
  UvarL : ∀ {u v s u' v'} →
    s walks (VVar u) to (VVar u') → s walks v to v' → s unifies (VVar u) w/ v
  UvarR : ∀ {u v s u' v'} →
    s walks u to u' → s walks (VVar v) to (VVar v') → s unifies u w/ (VVar v)
  Ulists : ∀ {u v s u' v' α β} →
    s walks u to (VList (α ∷ u')) → s walks v to (VList (β ∷ v'))
    → s unifies α w/ β → s unifies (VList u') w/ (VList v') → s unifies u w/ v 
  Uvals : ∀ {u v s u' v'} →
    s walks u to u' → s walks v to v' → (u' val=? v') → s unifies u w/ v 

-- substitution and counter
State : Set
State = Subst × ℕ

Unit : Set
Unit = List State

unit : State → Unit
unit s = s ∷ []

-- data _==_toUnit_ : Val → Val → Unit → Set where 
  -- fail : ∀ {u v s} → ¬ s unifies u w/ v → u == v toUnit []
