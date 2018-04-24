module systemF where

open import Data.String
open import Data.Nat hiding (_≟_ ; _>_)
open import Data.Product hiding (map)
open import Data.Sum
open import Data.Empty
open import Data.List
open import Data.Bool hiding (_≟_)
open import Data.Char as C hiding (_≟_ ; _==_)
open import Relation.Nullary.Decidable
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Size


data Typ : Set where
   Int  : Typ
   Tvar : String → Typ
   _⇒_  : Typ → Typ → Typ
   ∀τ   : String → Typ → Typ

data Exp : Set where
   var      : String → Exp
   int      : ℕ → Exp
   add1     : Exp → Exp
   lam      : String → Typ → Exp → Exp
   Λ        : String → Exp → Exp
   app      : Exp → Exp → Exp
   Λapp     : Exp → Typ → Exp 

data Ctx : Set where
   □     : Ctx
   _,_   : String × Typ → Ctx → Ctx
   _:τ,_ : String → Ctx → Ctx

data _∈Γ_ : (String × Typ) → Ctx → Set where
   here : ∀ {Γ x τ} → (x , τ) ∈Γ ((x , τ) , Γ)
   skip : ∀ {Γ x x₁ τ τ₁} →
            {α : False (x ≟ x₁)} → (x , τ) ∈Γ Γ → (x , τ) ∈Γ ((x₁ , τ₁) , Γ)

data STyp : {i : Size} → Set where
   SInt  : {i : Size} → STyp {↑ i}
   STvar : {i : Size} → String → STyp {↑ i}
   _S⇒_  : {i : Size} → STyp {i} → STyp {i} → STyp {↑ i}
   S∀τ   : {i : Size} → String → STyp {i} → STyp {↑ i}

data SExp : {i : Size} → Set where
   Svar      : {i : Size} → String → SExp {↑ i}
   Sint      : {i : Size} → ℕ → SExp {↑ i}
   Sadd1     : {i : Size} → SExp {i} → SExp {↑ i}
   Slam      : {i : Size} → String → STyp → SExp {i} → SExp {↑ i}
   SΛ        : {i : Size} → String → SExp {i} → SExp {↑ i}
   Sapp      : {i : Size} → SExp {i} → SExp {i} → SExp {↑ i}
   SΛapp     : {i : Size} → SExp {i} → STyp → SExp {↑ i} 

sizeτ : Typ → STyp
sizeτ Int = SInt
sizeτ (Tvar x) = STvar x
sizeτ (t ⇒ t₁) = (sizeτ t) S⇒ (sizeτ t₁)
sizeτ (∀τ x t) = S∀τ x (sizeτ t)

size : Exp → SExp
size (var x) = Svar x 
size (int x) = Sint x
size (add1 e) = Sadd1 (size e)
size (lam x x₁ e) = Slam x (sizeτ x₁) (size e)
size (Λ x e) = SΛ x (size e)
size (app e e₁) = Sapp (size e) (size e₁)
size (Λapp e x) = SΛapp (size e) (sizeτ x)

unsizeτ : STyp → Typ
unsizeτ SInt = Int
unsizeτ (STvar x) = Tvar x
unsizeτ (τ S⇒ τ₁) = (unsizeτ τ) ⇒ (unsizeτ τ₁)
unsizeτ (S∀τ x τ) = ∀τ x (unsizeτ τ)
 
unsize : SExp → Exp
unsize (Svar x) = var x
unsize (Sint x) = int x
unsize (Sadd1 se) = add1 (unsize se)
unsize (Slam x t se) = lam x (unsizeτ t) (unsize se)
unsize (SΛ x se) = Λ x (unsize se)
unsize (Sapp se se₁) = app (unsize se) (unsize se₁)
unsize (SΛapp se t) = Λapp (unsize se) (unsizeτ t)


_∈_ : String → List String → Bool
x ∈ [] = false
x ∈ (y ∷ ys) = (x == y) ∨ (x ∈ ys)

_∪_ : List String → List String → List String
[] ∪ ys = ys
(x ∷ xs) ∪ ys = if x ∈ ys then xs ∪ ys else x ∷ (xs ∪ ys)

_\\_ : List String → String → List String
[] \\ x = []
(y ∷ ys) \\ x = if x == y then ys \\ x else y ∷ (ys \\ x)

fvτ : Typ → List String
fvτ Int = []
fvτ (Tvar x) = [ x ]
fvτ (t ⇒ t₁) = fvτ t ∪ fvτ t₁
fvτ (∀τ x t) = fvτ t \\ x

fv : Exp → List String
fv (var x) = [ x ]
fv (int x) = []
fv (add1 e) = fv e
fv (lam x x₁ e) = fv e \\ x
fv (Λ x e) = fv e \\ x
fv (app e e₁) = fv e ∪ fv e₁
fv (Λapp e x) = fv e ∪ fvτ x

-- bv : Exp → List String
-- bv = {!!}

fresh : List String → String
fresh xs = fromList (foldl diagonalize [ 'z' ] (Data.List.map toList xs))
  where diagonalize : List C.Char → List C.Char → List C.Char
        diagonalize [] [] = [ 'z' ]
        diagonalize [] ('z' ∷ _) = [ 'w' ]
        diagonalize [] _ = [ 'z' ]
        diagonalize s [] = s
        diagonalize (x ∷ xs) (y ∷ ys) = 
          if x C.== y then x ∷ diagonalize xs ys else x ∷ xs

renameVarτ : {i : Size} → STyp {i} → String → String → STyp {i}
renameVarτ SInt s₁ s₂ = SInt
renameVarτ (STvar {i} x) s₁ s₂ = if x == s₂ then STvar {i} s₁ else STvar {i} x
renameVarτ (τ S⇒ τ₁) s₁ s₂ = (renameVarτ τ s₁ s₂) S⇒ (renameVarτ τ₁ s₁ s₂)
renameVarτ (S∀τ {i} x τ) s₁ s₂ =
  if x == s₂
  then S∀τ {i} x τ
  else let conflicts = [ s₂ ] ∪ ([ s₁ ] ∪ fvτ (∀τ x (unsizeτ τ)))
           ns = fresh conflicts
       in S∀τ {i} ns (renameVarτ {i} (renameVarτ {i} τ ns x) s₁ s₂)

renameVarτₑ : {i : Size} → SExp {i} → String → String → SExp {i}
renameVarτₑ .{↑ i} (Svar {i} s₂) s₃ s₁ = (Svar s₂)
renameVarτₑ .{↑ i} (Sint {i} x) s₃ s = (Sint x)
renameVarτₑ .{↑ i} (Slam {i} s₁ t e₁) s₃ s₂ = (Slam s₁ (renameVarτ t s₃ s₂) (renameVarτₑ e₁ s₃ s₂))
renameVarτₑ .{↑ i} (Sapp {i} e₁ e₂) s₃ s = Sapp {i} (renameVarτₑ {i} e₁ s₃ s) (renameVarτₑ {i} e₂ s₃ s)
renameVarτₑ .{↑ i} (SΛapp {i} e₁ t) s₃ s = SΛapp {i} (renameVarτₑ {i} e₁ s₃ s) (renameVarτ t s₃ s)
renameVarτₑ .{↑ i} (Sadd1 {i} n) s₃ s = Sadd1 (renameVarτₑ {i} n s₃ s)
renameVarτₑ .{↑ i} (SΛ {i} s₁ e) s₃ s₂ = 
  if s₁ == s₂
  then SΛ {i} s₁ e
  else let conflicts = [ s₂ ] ∪ ([ s₃ ] ∪ fv (Λ s₁ (unsize e)))
           ns = fresh conflicts
       in SΛ {i} ns (renameVarτₑ {i} (renameVarτₑ {i} e ns s₁) s₃ s₂)

renameVar : {i : Size} → SExp {i} → String → String → SExp {i}
renameVar .{↑ i} (Svar {i} s₂) s₃ s₁ = if s₁ == s₂ then Svar {i} s₃ else Svar {i} s₂
renameVar .{↑ i} (Slam {i} s₁ t e₁) s₃ s₂ = 
  if s₁ == s₂
  then Slam {i} s₁ t e₁
  else let conflicts = [ s₂ ] ∪ ([ s₃ ] ∪ fv (lam s₁ (unsizeτ t) (unsize e₁)))
           ns = fresh conflicts
       in Slam {i} ns (renameVarτ t s₃ s₂) (renameVar {i} (renameVar {i} e₁ ns s₁) s₃ s₂)
renameVar .{↑ i} (Sapp {i} e₁ e₂) s₃ s = 
  Sapp {i} (renameVar {i} e₁ s₃ s) (renameVar {i} e₂ s₃ s)
renameVar .{↑ i} (SΛapp {i} e₁ t) s₃ s =
  SΛapp {i} (renameVar {i} e₁ s₃ s) (renameVarτ t s₃ s)
renameVar .{↑ i} (Sint {i} x) s₃ s = (Sint x)
renameVar .{↑ i} (Sadd1 {i} n) s₃ s = Sadd1 (renameVar {i} n s₃ s)
renameVar .{↑ i} (SΛ {i} s₁ e) s₃ s₂ = (SΛ {i} s₁ (renameVar {i} e s₃ s₂))

_[_/_]τ' : {i : Size} → STyp {i} → Typ → String → Typ
SInt [ α / β ]τ' = Int
STvar x [ α / β ]τ' = if x == β then α else Tvar x
(t S⇒ t₁) [ α / β ]τ' = (t [ α / β ]τ') ⇒ (t₁ [ α / β ]τ')
S∀τ x t [ α / β ]τ' =
  if x == β
  then ∀τ x (unsizeτ t)
  else let conflicts = [ β ] ∪ (fvτ α ∪ fvτ (∀τ x (unsizeτ t)))
           s₃ = fresh conflicts
       in ∀τ s₃ ((renameVarτ t s₃ x) [ α / β ]τ')


_[_/_]τₑ' : {i : Size} → SExp {i} → Typ → String → Exp
Svar s₂ [ e / s₁ ]τₑ' = (var s₂)
Slam s₁ t e₁ [ e₂ / s₂ ]τₑ' = lam s₁ (t [ e₂ / s₁ ]τ') (e₁ [ e₂ / s₁ ]τₑ')
Sapp e₁ e₂ [ e₃ / s ]τₑ' = app (e₁ [ e₃ / s ]τₑ') (e₂ [ e₃ / s ]τₑ')
Sint x₁ [ e / x ]τₑ' = int x₁
Sadd1 s [ e / x ]τₑ' = add1 (s [ e / x ]τₑ')
SΛ x₁ s [ e / x ]τₑ' =
  if x₁ == x 
  then Λ x₁ (unsize s)
  else let conflicts = [ x ] ∪ (fvτ e ∪ fv (Λ x₁ (unsize s)))
           s₃ = fresh conflicts
       in Λ s₃ ((renameVarτₑ s s₃ x₁) [ e / x ]τₑ')
SΛapp s x₁ [ e / x ]τₑ' = Λapp (s [ e / x ]τₑ') (x₁ [ e / x ]τ')

_[_/_]' : {i : Size} → SExp {i} → Exp → String → Exp
Svar s₂ [ e / s₁ ]' = if s₁ == s₂ then e else var s₂
Slam s₁ t e₁ [ e₂ / s₂ ]' =
  if s₁ == s₂ 
  then lam s₁ (unsizeτ t) (unsize e₁)
  else let conflicts = [ s₂ ] ∪ (fv e₂ ∪ fv (lam s₁ (unsizeτ t) (unsize e₁)))
           s₃ = fresh conflicts
       in lam s₃ (unsizeτ t) ((renameVar e₁ s₃ s₁) [ e₂ / s₂ ]')
Sapp e₁ e₂ [ e₃ / s ]' = app (e₁ [ e₃ / s ]') (e₂ [ e₃ / s ]')
Sint x₁ [ e / x ]' = int x₁
Sadd1 s [ e / x ]' = add1 (s [ e / x ]')
SΛ x₁ s [ e / x ]' = Λ x₁ (s [ e / x ]')
SΛapp s x₁ [ e / x ]' = Λapp (s [ e / x ]') (unsizeτ x₁)


_[_/_]τ : Typ → Typ → String → Typ
e [ e' / x ]τ = (sizeτ e) [ e' / x ]τ'

_[_/_]τₑ : Exp → Typ → String → Exp
e [ e' / x ]τₑ = (size e) [ e' / x ]τₑ'

_[_/_] : Exp → Exp → String → Exp
e [ e' / x ] = (size e) [ e' / x ]'



data _⊢_∷_ : Ctx → Exp → Typ → Set where
    IntT  : ∀ {Γ n} → Γ ⊢ (int n) ∷ Int
    SucT  : ∀ {Γ n} → Γ ⊢ n ∷ Int → Γ ⊢ (add1 n) ∷ Int
    VarT  : ∀ {Γ x τ} → (x , τ) ∈Γ Γ → Γ ⊢ (var x) ∷ τ
    LamT  : ∀ {Γ x τ₁ b τ₂} →
              ((x , τ₁) , Γ) ⊢ b ∷ τ₂ →
              (Γ ⊢ (lam x τ₁ b) ∷ (τ₁ ⇒ τ₂))
    AllT  : ∀ {Γ α b τ} →
              (α :τ, Γ) ⊢ b ∷ τ →
              (Γ ⊢ (Λ α b) ∷ (∀τ α τ))
    App₁T : ∀ {Γ e₁ e₂ τ₁ τ₂} →
              (Γ ⊢ e₁ ∷ (τ₁ ⇒ τ₂)) →
              (Γ ⊢ e₂ ∷ τ₁) → (Γ ⊢ (app e₁ e₂) ∷ τ₂)
    App₂T : ∀ {Γ e τ₁ α τ₂} →
              (Γ ⊢ e ∷ ∀τ α τ₁) → (Γ ⊢ (Λapp e τ₂)  ∷ (τ₁ [ τ₂ / α ]τ))

--- Dynamic Semantics, bb

data Env : Set

data isVal : Exp → Set where
  VNum : {n : ℕ} → isVal (int n)
  VClo : {x : String} → {t : Typ} → {e : Exp} →
         (ρ : Env) → isVal (lam x t e)
  VΛ   : {x : String} → {e : Exp} →
         (ρ : Env) → isVal (Λ x e)

Val : Set
Val = Σ[ e ∈ Exp ] isVal e

Vnum : ℕ → Val
Vnum n = (int n) , VNum

Vclo : String → Typ → Exp → Env → Val
Vclo x τ n ρ = (lam x τ n) , VClo ρ

VLam : String → Exp → Env → Val
VLam x n ρ = (Λ x n) , VΛ ρ

data Env where
  □    : Env
  _,_  : String × Val → Env → Env
  _,ₜ_ : String × Typ → Env → Env

data _∈ₑ_ : (String × Val) → Env → Set where
  hereₑ : ∀ {ρ x v} → (x , v) ∈ₑ ((x , v) , ρ)
  skipₑ : ∀ {ρ x x₁ v v₁} →
            {α : False (x ≟ x₁)} → (x , v) ∈ₑ ρ → (x , v) ∈ₑ ((x₁ , v₁) , ρ)

Closure : Set
Closure = Exp × Env

data Closure : Set where
  clo₁ : Exp → Env → Closure
  clo₂ : Typ → ... → Closure

data Frame : Set where
  SuccK    : Frame
  AppArgK  : Closure → Frame
  AppFuncK : Val → Frame
  AppΛK    : Typ → Frame
  
Cont : Set
Cont = List Frame


data State : Set where
  Enter  : Closure → Cont → State
  Return : Cont → Val → State

data _>_ : Exp × String × Typ → Exp → Set where
  Var>  : ∀ {x α τ} → ((var x) , α , τ) > (var x)
  Int>  : ∀ {n α τ} → ((int n) , α , τ) > (int n)
  Add1> : ∀ {e α τ e'} → (e , α , τ) > e' → ((add1 e) , α , τ) > (add1 e')
  Lam>  : ∀ {α x τₓ b b' τ} → (b , α , τ) > b' → ((lam x τₓ b) , α , τ) > (lam x (τₓ [ τ / α ]τ) b')
  Λ>    : ∀ {α x b τ} → ((Λ x b) , α , τ) > (Λ x b [ τ / α ]τₑ)
  App>  : ∀ {α e₁ e₁' e₂ e₂' τ} → (e₁ , α , τ) > e₁' →  (e₂ , α , τ) > e₂' →
          ((app e₁ e₂) , α , τ) > (app e₁ e₂)
  ΛApp> : ∀ {α e e' t τ} → (e , α , τ) > e' → (Λapp e t , α , τ) > (Λapp e (t [ τ / α ]τ))

data _>τ_ : Typ × String → Typ → Set where
   Var₁>τ : ∀ {x x₁} → {α : True (x ≟ x₁)} → ((Tvar x) , x₁) >τ (Tvar x₁)
   Var₂>τ : ∀ {x x₁} → {α : False (x ≟ x₁)} → ((Tvar x) , x₁) >τ (Tvar x)
   Int>τ  : ∀ {x} → ((Int , x) >τ Int)
   ⇒>τ    : ∀ {τ₁ τ₂ x τ₁' τ₂'} → ((τ₂ , x) >τ τ₁') → ((τ₂ , x) >τ τ₂') → ((τ₁ ⇒ τ₂) , x) >τ (τ₁' ⇒ τ₂')
   ∀τ₁>τ  : ∀ {x x₁ τ} → {α : True (x ≟ x₁)} → (((∀τ x τ) , x₁) >τ (∀τ x τ))  
   ∀τ₂>τ  : ∀ {x x₁ τ τ'} → {α : False (x ≟ x₁)} → ((τ , x₁) >τ τ') → (((∀τ x τ) , x₁) >τ (∀τ x τ'))
   
data _↦_ : State → State → Set where
  VarE   : ∀ {x v ρ κ} → ((x , v) ∈ₑ ρ) → (Enter (var x , ρ) κ) ↦ (Return κ v)
  IntE   : ∀ {n ρ κ} → (Enter (int n , ρ) κ) ↦ (Return κ (Vnum n))  
  SuccE  : ∀ {e ρ κ} → (Enter (add1 e , ρ) κ) ↦ (Enter (e , ρ) (SuccK ∷ κ))
  SuccR  : ∀ {n κ} → (Return (SuccK ∷ κ) (Vnum n)) ↦ (Return κ (Vnum (suc n)))
  LamE   : ∀ {x t e ρ κ} → (Enter (lam x t e , ρ) κ) ↦ (Return κ (Vclo x t e ρ))  
  BLamE  : ∀ {x e ρ κ} → (Enter (Λ x e , ρ) κ) ↦ (Return κ (VLam x e ρ))
  App₁E  : ∀ {e₁ e₂ ρ κ} → (Enter (app e₁ e₂ , ρ) κ) ↦ (Enter (e₁ , ρ) (AppArgK (e₂ , ρ) ∷ κ))
  App₂E  : ∀ {e₁ t ρ κ} → (Enter (Λapp e₁ t , ρ) κ) ↦ (Enter (e₁ , ρ) (AppΛK t ∷ κ))
  App₁FR : ∀ {κ c v} → (Return (AppArgK c ∷ κ) v) ↦ (Enter c (AppFuncK v ∷ κ))
  App₁VR : ∀ {x t κ e ρ v} → (Return (AppFuncK (Vclo x t e ρ) ∷ κ) v) ↦ (Enter (e , (x , v) , ρ) κ)
  App₂R  : ∀ {κ t x e ρ e₁} → ((e , x , t) > e₁) → (Return (AppΛK t ∷ κ) (VLam x e ρ)) ↦ (Enter (e₁ , ρ) κ)


infixr 10 _●_

data _↦*_ : State → State → Set where
  ∎   : ∀ {s} → s ↦* s
  _●_ : ∀ {s₁ s₂ s₃} → s₁ ↦ s₂ → s₂ ↦* s₃ → s₁ ↦* s₃

Eval : Exp → Val → Set
Eval e v = (Enter (e , □) []) ↦* (Return [] v)

e₁ e₂ : Exp
e₁ = (app (lam "x" Int (add1 (var "x"))) (int 5))
e₂ = (app (Λapp (Λ "α" (lam "x" (Tvar "α") (var "x"))) Int) (int 5))

tr₁ : Eval e₁ (Vnum 6)
tr₁ = App₁E ● LamE ●  App₁FR ● IntE ● App₁VR ● SuccE ● VarE (hereₑ) ● SuccR ● ∎

tr₂ : Eval e₂ (Vnum 5)
tr₂ = App₁E ● App₂E ● BLamE ● App₂R (Lam> Var>) ● LamE ● App₁FR ● IntE ● App₁VR ● VarE (hereₑ) ● ∎


-- equivalences between values,types,envs,contexts

data _∼_ : Val → Typ → Set
data _≈_ : Env → Ctx → Set

data _∼_ where
  num~ : ∀ {n} → (int n , VNum) ∼ Int
  clo~ : ∀ {ρ Γ x τ₁ τ₂ b} → (ρ ≈ Γ) → ((x , τ₁) , Γ) ⊢ b ∷ τ₂ → (lam x τ₁ b , VClo ρ) ∼ (τ₁ ⇒ τ₂)
  ∀~   : ∀ {ρ Γ x τ₂ b} → (ρ ≈ Γ) → ( x :τ, Γ) ⊢ b ∷ τ₂ → (Λ x b , VΛ ρ) ∼ (∀τ x τ₂)

data _≈_ where
  □≈ : □ ≈ □
  x≈ : ∀ {x y v τ ρ Γ} → x ≡ y → v ∼ τ → ρ ≈ Γ → ((x , v) , ρ) ≈ ((y , τ) , Γ)


Γ⇒v : ∀ {x τ Γ ρ} → ρ ≈ Γ → ((x , τ) ∈Γ Γ) → Σ[ v ∈ Val ] (x , v) ∈ₑ ρ
Γ⇒v □≈ ()
Γ⇒v (x≈ refl v∼τ ρ≈Γ) here = _ , hereₑ
Γ⇒v (x≈ refl v∼τ ρ≈Γ) (skip {α = α} inΓ) =
  let (v , inρ) = Γ⇒v ρ≈Γ inΓ in v , skipₑ {α = α} inρ 

ρ⇒vτ : ∀ {x τ v Γ ρ} →
       ρ ≈ Γ → ((x , v) ∈ₑ ρ) → ((x , τ) ∈Γ Γ) → v ∼ τ
ρ⇒vτ □≈ () 
ρ⇒vτ (x≈ refl v∼τ ρ≈Γ) hereₑ here = v∼τ
ρ⇒vτ (x≈ refl v∼τ ρ≈Γ) hereₑ (skip {α = α} inΓ) =
  ⊥-elim (toWitnessFalse α refl)
ρ⇒vτ (x≈ refl v∼τ ρ≈Γ) (skipₑ {α = α} inρ) here =
  ⊥-elim (toWitnessFalse α refl)
ρ⇒vτ (x≈ refl v∼τ ρ≈Γ) (skipₑ inρ) (skip inΓ) = ρ⇒vτ ρ≈Γ inρ inΓ


-- closure typing

-- _⊢c_ : Closure → Typ → Set
_⊢c_ : ∀ {e' a t e} → (Closure ⊎ ((e , a , t) > e')) → Typ → Set
(inj₁ (e , ρ)) ⊢c τ = Σ[ Γ ∈ Ctx ] (ρ ≈ Γ × Γ ⊢ e ∷ τ)
_⊢c_ {e'} (inj₂ reduc) τ = Σ[ Γ ∈ Ctx ] (Γ ⊢ e' ∷ τ)

-- Frame typing

data _⊢f_ : Frame → (Typ × Typ) → Set where
  SuccKT :
    SuccK ⊢f (Int , Int)
  AppArgKT : ∀ {cl τ₁ τ₂} →
    ((inj₁ cl) ⊢c τ₁) → AppArgK cl ⊢f (τ₁ ⇒ τ₂ , τ₂)
  AppFuncKT : ∀ {v τ₁ τ₂} →
    (v ∼ (τ₁ ⇒ τ₂)) → AppFuncK v ⊢f (τ₁ , τ₂)
  AppΛKT : ∀ {α τ τ₂} → AppΛK τ ⊢f (∀τ α τ₂ , τ₂ [ τ / α ]τ)

-- Continuation typing κ ⊢κ (τ , τ)

data _⊢κ_ : Cont → (Typ × Typ) → Set where
  EmptyKT : ∀ {τ} →
    [] ⊢κ (τ , τ)
  PushKT  : ∀ {fr κ τ₁ τ₂ τ₃} →
    fr ⊢f (τ₁ , τ₂) →
    κ ⊢κ (τ₂ , τ₃) →
    (fr ∷ κ) ⊢κ (τ₁ , τ₃)

-- State typing

data _⊢s_ : State → Typ → Set where
  EnterT  : ∀ {cl κ τ₁ τ₂} →
    cl ⊢c τ₁ →
    κ ⊢κ (τ₁ , τ₂) →
    (Enter cl κ) ⊢s τ₂
  ReturnT : ∀ {κ v τ₁ τ₂} →
    κ ⊢κ (τ₁ , τ₂) →
    v ∼ τ₁ →
    Return κ v ⊢s τ₂

-- Initial and final states

loadT : ∀ {e τ} → (□ ⊢ e ∷ τ) → (Enter (e , □) []) ⊢s τ
loadT et = EnterT (□ , □≈ , et) EmptyKT

data Final : State → Typ → Set where
  F : ∀ {v τ} → (v ∼ τ) → Final (Return [] v) τ

-- Progress
-- If we are well-typed and not final then we can make some progress

progress : ∀ {s τ} → s ⊢s τ → (Final s τ) ⊎ (Σ[ s' ∈ State ] s ↦ s')
progress (EnterT (Γ , ρ≈Γ , IntT) κτ) = inj₂ (_ , IntE) 
progress (EnterT (Γ , ρ≈Γ , SucT e) κτ) = inj₂ (_ , SuccE) 
progress (EnterT (Γ , ρ≈Γ , VarT inΓ) κτ) = inj₂ (_ , VarE (proj₂ (Γ⇒v ρ≈Γ inΓ)))
progress (EnterT (Γ , ρ≈Γ , LamT e) κτ) = inj₂ (_ , LamE) 
progress (EnterT (Γ , ρ≈Γ , AllT e) κτ) = inj₂ (_ , BLamE) 
progress (EnterT (Γ , ρ≈Γ , App₁T e e₃) κτ) = inj₂ (_ , App₁E) 
progress (EnterT (Γ , ρ≈Γ , App₂T e) κτ) = inj₂ (_ , App₂E) 
progress (ReturnT EmptyKT v~t) = inj₁ (F v~t)
progress (ReturnT (PushKT SuccKT x₂) num~) = inj₂ (_ , SuccR)
progress (ReturnT (PushKT (AppArgKT x) x₂) (clo~ x₃ x₄)) = inj₂ (_ , App₁FR)
progress (ReturnT (PushKT (AppFuncKT (clo~ x₁ x₃)) x₂) v~t) = inj₂ (_ , App₁VR)
progress (ReturnT (PushKT AppΛKT x₂) (∀~ x x₁)) = inj₂ (_ , (App₂R {!!}))

preservation : ∀ {s s' τ} → s ↦ s' → s ⊢s τ → s' ⊢s τ
preservation IntE (EnterT (Γ , ρ≈Γ , IntT) κt) = ReturnT κt num~
preservation SuccE (EnterT (Γ , ρ≈Γ , SucT v~) κt) = EnterT (Γ , ρ≈Γ , v~) (PushKT SuccKT κt)
preservation (VarE x₂) (EnterT (Γ , ρ≈Γ , VarT x₁) κt) = ReturnT κt (ρ⇒vτ ρ≈Γ x₂ x₁)
preservation LamE (EnterT (Γ , ρ≈Γ , LamT v~) κt) = ReturnT κt (clo~ ρ≈Γ v~)
preservation BLamE (EnterT (Γ , ρ≈Γ , AllT v~) κt) = ReturnT κt (∀~ ρ≈Γ v~)
preservation App₁E (EnterT (Γ , ρ≈Γ , App₁T v~ v~₁) κt) =
  EnterT (Γ , ρ≈Γ , v~) (PushKT (AppArgKT (Γ , ρ≈Γ , v~₁)) κt)
preservation App₂E (EnterT (Γ , ρ≈Γ , App₂T v~) κt) = EnterT (Γ , ρ≈Γ , v~) (PushKT AppΛKT κt)
preservation SuccR (ReturnT (PushKT SuccKT x₂) x₁) = ReturnT x₂ num~
preservation App₁FR (ReturnT (PushKT (AppArgKT (Γ , ρ≈Γ , v~)) κt) x₁) =
  EnterT (Γ , ρ≈Γ , v~) (PushKT (AppFuncKT x₁) κt) 
preservation (App₁VR {x} {t}) (ReturnT (PushKT (AppFuncKT (clo~ {Γ = Γ} ρ≈Γ x₃)) κt) v~t) = 
  EnterT (((x , t) , Γ) , x≈ refl v~t ρ≈Γ , x₃) κt
preservation (App₂R {x = x} {e} {e₁ = e₃} x₂) (ReturnT (PushKT AppΛKT κt) x₁) = EnterT {!!} κt

