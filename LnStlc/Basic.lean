import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Finset.Lattice.Basic
import Mathlib.Data.Set.Finite.Basic

/-- Simple types -/
inductive Ty : Type
/-- The unit type. -/
| unit
/-- A function type `A → B`. -/
| arr (A B : Ty)
/-- A product type `A × B`. -/
| prod (A B : Ty)

/-- Untyped STLC terms -/
inductive Tm : Type
/-- A named free variable. -/
| fv (x : String)
/-- A bound variable, represented using a de Bruijn index. -/
| bv (i : ℕ)
/-- The unique value of the unit type. -/
| null
/-- A lambda abstraction `λ (x : A). body`. -/
| abs (ty : Ty) (body : Tm)
/-- A pair `(a, b)`. -/
| pair (lhs rhs : Tm)
/-- The first projection of a pair. -/
| fst (p : Tm)
/-- The second projection of a pair. -/
| snd (p : Tm)

/-- The _closure level_ of an STLC term -/
def Tm.bvi : Tm → ℕ
| .fv _ => 0
| .bv i => i + 1
| .null => 0
| .abs _ body => bvi body - 1
| .pair lhs rhs => bvi lhs ⊔ bvi rhs
| .fst p => bvi p
| .snd p => bvi p

/-- The set of free variables appearing in an STLC term -/
def Tm.fvs : Tm → Finset String
| .fv x => {x}
| .bv _ => ∅
| .null => ∅
| .abs _ body => fvs body
| .pair lhs rhs => fvs lhs ∪ fvs rhs
| .fst p | .snd p => fvs p

/-- Weaken under `n` binders -/
def Tm.wkUnder (n : ℕ) : Tm → Tm
| .fv x => .fv x
| .bv i => if i < n then .bv i else .bv (i + 1)
| .null => .null
| .abs ty body => .abs ty (wkUnder (n + 1) body)
| .pair lhs rhs => .pair (wkUnder n lhs) (wkUnder n rhs)
| .fst p => .fst (wkUnder n p)
| .snd p => .snd (wkUnder n p)

prefix:70 "↑₀" => Tm.wkUnder 0

/-- Substitute the bound variable under `n` binders -/
def Tm.substUnder (n : ℕ) (a : Tm) : Tm → Tm
| .fv x => .fv x
| .bv i => if i < n then .bv i else if i = n then a else .bv (i - 1)
| .null => .null
| .abs ty body => .abs ty (substUnder (n + 1) (↑₀ a) body)
| .pair lhs rhs => .pair (substUnder n a lhs) (substUnder n a rhs)
| .fst p => .fst (substUnder n a p)
| .snd p => .snd (substUnder n a p)

instance Tm.instPow : Pow Tm Tm where
  pow b a := substUnder 0 a b

instance Tm.instCoeVar : Coe String Tm where
  coe x := .fv x

instance Tm.instPowVar : Pow Tm String where
  pow b x := b^(Tm.fv x)

theorem Tm.bvi_le_substUnder_var (n : ℕ) (x : String) (b : Tm)
  : bvi b ≤ (n + 1) ⊔ (bvi (substUnder n x b) + 1)
  := by induction b generalizing n <;> grind [bvi, substUnder, wkUnder]

theorem Tm.pow_def (b : Tm) (a : Tm) : b ^ a = substUnder 0 a b := rfl

theorem Tm.pow_var_def (x : String) (b : Tm) : b ^ x = substUnder 0 x b := rfl

theorem Tm.bvi_le_subst_var (x : String) (b : Tm)
  : bvi b ≤ bvi (b ^ x) + 1
  := by convert bvi_le_substUnder_var 0 x b using 1; simp [Tm.pow_var_def]

theorem Tm.bvi_substUnder_var_le (n : ℕ) (x : String) (b : Tm)
  : bvi (substUnder n x b) ≤ n ⊔ (bvi b - 1)
  := by induction b generalizing n <;> grind [bvi, substUnder, wkUnder]

theorem Tm.bvi_subst_var_le (x : String) (b : Tm) : bvi (b ^ x) ≤ bvi b - 1
  := by convert b.bvi_substUnder_var_le 0 x using 1; simp

theorem Tm.subst_var_lc {x : String} {b : Tm} : bvi (b ^ x) = 0 ↔ bvi b - 1 = 0
  := by have h := b.bvi_le_subst_var x; have h' := b.bvi_subst_var_le x; omega

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

theorem Tm.subst_var_lc_cf {L : Finset String} {b : Tm} : (∀x ∉ L, bvi (b ^ x) = 0) ↔ bvi b - 1 = 0
  := by
  simp only [subst_var_lc]
  exact ⟨fun h => have ⟨x, hx⟩ := L.exists_notMem; h x hx, fun h _ _ => h⟩

theorem Ctx.Deriv.lc {Γ a A} (ha : Γ ⊢ a : A) : a.bvi = 0
  := by induction ha with
  | _ =>
    (try simp only [Tm.subst_var_lc_cf] at *)
    grind [Tm.bvi]
