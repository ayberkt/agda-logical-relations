open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)
open import Data.Nat   using   (ℕ; suc; zero; _+_)
open import Data.Empty using   (⊥; ⊥-elim)
open import Data.Unit  using   (⊤)
open import Data.Product using (_×_; _,_; Σ-syntax)

data Type : Set where
  Nat   : Type
  _⇒_  : Type → Type → Type

data Exp : Set where
  var  : ℕ → Exp
  _$_  : Exp → Exp → Exp
  lam  : Type → Exp → Exp
  zero : Exp
  succ : Exp → Exp

data Context : Set where
  ε     : Context
  _∙_   : Context → Type → Context

mutual
  data Closure : Set where
    clam  : Type → Exp → Environment → Closure
    _$c_  : Closure → Closure → Closure
    czero : Closure
    csucc : Closure → Closure

  data Environment : Set where
    ∅   : Environment
    _,,_ : Environment → Closure → Environment

isNV : Closure → Set
isNV (clam x x₁ x₂) = ⊥
isNV (c $c c₁) = ⊥
isNV czero = ⊤
isNV (csucc c) = isNV c

subst : Exp → Environment → Closure
subst (var zero) ∅ = ⊥-elim undefined
  where
    postulate undefined : ⊥
subst (var zero) (ρ ,, c) = c
subst (var (suc n)) (ρ ,, c) = subst (var n) ρ
subst (var (suc n)) _ = ⊥-elim undefined
  where
    postulate undefined : ⊥
subst (e₀ $ e₁) ρ = subst e₀ ρ $c subst e₁ ρ
subst (lam x e) ρ = clam x e ρ
subst zero ρ = czero
subst (succ e) ρ = csucc (subst e ρ)

data _↦_ : Closure → Closure → Set where
  E1 : ∀ {A} {e} {ρ} {c} → ((clam A e ρ) $c c) ↦ subst e (ρ ,, c)
  E2 : ∀ {c₀ c₀′ c₁} → c₀ ↦ c₀′ → (c₀ $c c₁) ↦ (c₀′ $c c₁)
  E3 : ∀ {c c′} → c ↦ c′ → csucc c ↦ csucc c′

record LogPred : Set₁ where
  field
    LP : Type → Closure → Set
    A1 : ∀ {c c′} → LP Nat c′ → c ↦ c′ → LP Nat c
    A2 : LP Nat czero
    A3 : ∀ {c} → LP Nat c → LP Nat (csucc c)
    A4 : ∀ {A B : Type}
        → (c₀ : Closure)
        → LP (A ⇒ B) c₀ ≡ ((c₁ : Closure) → LP A c₁ → LP B (c₀ $c c₁))

  mapLP : Context → Environment → Set
  mapLP ε _ = Data.Unit.⊤
  mapLP (Γ ∙ A) ∅ = ⊥
  mapLP (Γ ∙ A) (ρ ,, c) = LP A c × mapLP Γ ρ

postulate SomeLP : LogPred

LP = LogPred.LP SomeLP
A1 = LogPred.A1 SomeLP
A2 = LogPred.A2 SomeLP
A3 = LogPred.A3 SomeLP
A4 = LogPred.A4 SomeLP
mLP = LogPred.mapLP SomeLP

lemma-1 : ∀ {A : Type} {c c′} → LP A c′ → c ↦ c′ → LP A c
lemma-1 {Nat} {c} {c′} p q = A1 p q
lemma-1 {A₀ ⇒ A₁} {c} {c′} A q
  rewrite A4 {A₀} {A₁} c | A4 {A₀} {A₁} c′ = λ ch r → lemma-1 (A ch r) (E2 q)

data _⊢_∈_ : Context → Exp → Type → Set where
  tzero : ∀ {Γ} → Γ ⊢ zero ∈ Nat
  tsucc : ∀ {Γ} {e} → Γ ⊢ e ∈ Nat → Γ ⊢ (succ e) ∈ Nat
  tapp  : ∀ {Γ} {A B} {e₀ e₁} → Γ ⊢ e₀ ∈ (A ⇒ B) → Γ ⊢ e₁ ∈ A → Γ ⊢ e₀ $ e₁ ∈ B
  tlam  : ∀ {Γ} {A} {B} {e} → (Γ ∙ A) ⊢ e ∈ B → Γ ⊢ (lam A e) ∈ (A ⇒ B)
  tvar0 : ∀ {Γ} {T} → (Γ ∙ T) ⊢ var 0 ∈ T
  tvars : ∀ {Γ} {A T} {n} → Γ ⊢ var n ∈ T → (Γ ∙ A) ⊢ var (suc n) ∈ T

mapLP-lemma : ∀ {Γ} {B} {ρ} {c} → mLP (Γ ∙ B) (ρ ,, c) → mLP Γ ρ
mapLP-lemma (proj₁ Data.Product., proj₂) = proj₂

subst-lemma : ∀ {n} {c} {ρ} → subst (var (suc n)) (ρ ,, c) ≡ subst (var n) ρ
subst-lemma {n} {c} {ρ} = refl

theorem1 : ∀ {Γ} {t} {A} {ρ} → Γ ⊢ t ∈ A → mLP Γ ρ → LP A (subst t ρ)
theorem1 tzero B = A2
theorem1 (tsucc A) B = A3 (theorem1 A B)
theorem1 {Γ} {_} {_} {ρ} (tapp{_}{A₀}{A₁}{e₀}{e₁} A B) C =
  IH₁ (subst e₁ ρ) IH₂
  where
    IH₁ : (c₀ : Closure) → LP A₀ c₀ → LP A₁ ((subst e₀ ρ) $c c₀)
    IH₁ rewrite sym (A4 {A₀} {A₁} (subst e₀ ρ)) = theorem1 {Γ} A C
    IH₂ : LogPred.LP SomeLP A₀ (subst e₁ ρ)
    IH₂ = theorem1 {Γ} B C
theorem1 {ρ = ρ} (tlam {Γ′} {A₀} {A₁} {e} D) B
  rewrite A4 {A₀} {A₁} (subst  (lam A₀ e) ρ) = λ ch P →
    lemma-1 (theorem1 D (P , B)) E1
theorem1 {.(Γ ∙ T)} {ρ = ∅} (tvar0 {Γ} {T}) ()
theorem1 {.(Γ ∙ T)} {ρ = ρ ,, x} (tvar0 {Γ} {T}) (proj₁ , proj₂) = proj₁
theorem1 {Γ ∙ x} {ρ = ∅} (tvars A) ()
theorem1 {Γ′ ∙ B} {n} {_} {c ,, ρ} D@(tvars D′) C = theorem1 D′ (mapLP-lemma C)
