module systemF where

open import Data.String
open import Data.Nat hiding (_≟_)
open import Data.Product
open import Relation.Nullary.Decidable


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
   _[_]     : Exp → Typ → Exp 

data Ctx : Set where
   □      : Ctx
   _,_    : String × Typ → Ctx → Ctx
   _:τ,_ : String → Ctx → Ctx

data _∈_ : (String × Typ) → Ctx → Set where
   here : ∀ {Γ x τ} → (x , τ) ∈ ((x , τ) , Γ)
   skip : ∀ {Γ x x₁ τ τ₁} →
            {α : False (x ≟ x₁)} → (x , τ) ∈ Γ → (x , τ) ∈ ((x₁ , τ₁) , Γ)

data _⊫_∷_ : Ctx → Exp → Typ → Set where
    NumT  : ∀ {Γ n} → Γ ⊫ (int n) ∷ Int
    SucT  : ∀ {Γ n} → Γ ⊫ n ∷ Int → Γ ⊫ (add1 n) ∷ Int
    VarT  : ∀ {Γ x τ} → (x , τ) ∈ Γ → Γ ⊫ (var x) ∷ τ
    LamT  : ∀ {Γ x τ₁ b τ₂} →
              ((x , τ₁) , Γ) ⊫ b ∷ τ₂ →
              (Γ ⊫ (lam x τ₁ b) ∷ (τ₁ ⇒ τ₂))
    AllT  : ∀ {Γ α b τ} →
              (α :τ, Γ) ⊫ b ∷ τ →
              (Γ ⊫ (Λ α b) ∷ (∀τ α τ))
    App₁T : ∀ {Γ e₁ e₂ τ₁ τ₂} →
              (Γ ⊫ e₁ ∷ (τ₁ ⇒ τ₂)) →
              (Γ ⊫ e₂ ∷ τ₁) → (Γ ⊫ (app e₁ e₂) ∷ τ₂)
    App₂T : ∀ {Γ e τ₁ α τ₂} →
              (Γ ⊫ e ∷ ∀τ α τ₁) → (Γ ⊫ e [ τ₂ ] ∷ {!!}) 
