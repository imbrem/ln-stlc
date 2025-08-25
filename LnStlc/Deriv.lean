import LnStlc.Syntax

/-- A typing context mapping variables `x` to types `A`

    Supports shadowing: `Γ, x : A, Δ, x : B` maps `x` to `B` -/
inductive Ctx : Type
/-- The empty context -/
| nil
/-- Append a variable to a context -/
| cons (Γ : Ctx) (x : String) (A : Ty)

/-- `Γ` maps variable `x : String` to type `A : Ty` -/
inductive Ctx.Var : Ctx → Ty → String → Type
| here {Γ : Ctx} {A : Ty} {x : String} : Ctx.Var (Ctx.cons Γ x A) A x
| there {Γ : Ctx} {A B : Ty} {x y : String}
  : x ≠ y → Ctx.Var Γ A x → Ctx.Var (Ctx.cons Γ y B) A x

instance Ctx.Var.instSubsingleton {Γ A x} : Subsingleton (Var Γ A x) where
  allEq a b := by
    induction a with
    | here => cases b with | here => rfl | there => contradiction
    | there _ _ I => cases b with
      | here => contradiction
      | there => exact (congrArg _ (I _))

theorem Ctx.Var.disjoint {Γ A B x} (hA : Var Γ A x) (hB : Var Γ B x) : A = B := by
  induction hA with
  | here => cases hB with | here => rfl | there => contradiction
  | there _ _ I => cases hB with
    | here => contradiction
    | there _ hB => exact I hB

/-- Locally nameless typing derivations for the simply-typed lambda calculus -/
inductive Ctx.Deriv : Ctx → Ty → Tm → Type
  | var {Γ A x} : Var Γ A x → Deriv Γ A x
  | null {Γ} : Deriv Γ .unit .null
  | abs {Γ A B b} {L : Finset String}
    : (∀x ∉ L, Deriv (cons Γ x A) B (b^x))
    → Deriv Γ (.arr A B) (.abs A b)
  | pair {Γ A B a b}
    : Deriv Γ A a
    → Deriv Γ B b
    → Deriv Γ (.prod A B) (.pair a b)
  | fst {Γ A B p}
    : Deriv Γ (.prod A B) p
    → Deriv Γ A (.fst p)
  | snd {Γ A B p}
    : Deriv Γ (.prod A B) p
    → Deriv Γ B (.snd p)

notation Γ " ⊢ " a " : " A => Ctx.Deriv Γ A a

theorem Ctx.Deriv.lc {Γ a A} (ha : Γ ⊢ a : A) : a.bvi = 0
  := by induction ha with
  | _ =>
    (try simp only [Tm.subst_var_lc_cf] at *)
    grind [Tm.bvi]
