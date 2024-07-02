import Mathlib.Computability.TuringMachine
namespace Turing

inductive Λ -- states
| A
| B
| C
| D
| E
| F

inductive Γ -- symbols
| zero
| one

instance Λ.inhabited : Inhabited Λ := ⟨Λ.A⟩
instance Γ.inhabited : Inhabited Γ := ⟨Γ.zero⟩

-- initial state and empty tape:
def cfg₀ : Turing.TM0.Cfg Γ Λ := Turing.TM0.init []

-- chainable step function:
def step' (M : Turing.TM0.Machine Γ Λ) (x : Option (Turing.TM0.Cfg Γ Λ)) :
  Option (Turing.TM0.Cfg Γ Λ) :=
    x.bind (Turing.TM0.step M)

-- step a given number of times:
def multistep (M : Turing.TM0.Machine Γ Λ) (n : ℕ) (cfg : Turing.TM0.Cfg Γ Λ) :
  Option (Turing.TM0.Cfg Γ Λ) :=
    (step' M)^[n] (some cfg)

theorem multistep_none_add {cfg M n m} (hn : multistep M n cfg = none) :
  multistep M (n + m) cfg = none := by
  have h': n + Nat.zero = n := by rfl
  induction' m with n ih
  rw [h']
  exact hn
  rw [multistep, Nat.add_succ, Function.iterate_succ_apply', ← multistep,ih]
  exact rfl

theorem multistep_none_ge {cfg M n} {m:ℕ} {h' : m ≥ n} (hn : multistep M n cfg = none) :
  multistep M m cfg = none := by
  rw [← Nat.add_sub_of_le h']
  exact multistep_none_add hn

def halts (M : Turing.TM0.Machine Γ Λ) : Prop :=
  ∃ n, multistep M n cfg₀ = none

-- machine that halts immediately:
def M₁ : Turing.TM0.Machine Γ Λ
  | _,_ => none


theorem M₁_halts_immediately : Turing.TM0.step M₁ cfg₀ = none :=
rfl

theorem M₁_halts : halts M₁ :=
⟨1, rfl⟩

-- machine that goes A → B → halt:
def M₂ : Turing.TM0.Machine Γ Λ
| Λ.A,symbol => some ⟨Λ.B, Turing.TM0.Stmt.write symbol⟩
| _, _ => none

-- step 0, Λ.A:
#reduce multistep M₂ 0 cfg₀
-- step 1, Λ.B:
#reduce multistep M₂ 1 cfg₀
-- step 2, halt:
#reduce multistep M₂ 2 cfg₀
-- step 3, still halted:
#reduce multistep M₂ 3 cfg₀

theorem M₂_halts : halts M₂ := ⟨2, rfl⟩

--#reduce TM0.eval M₂ []


-- machine that loops A → B → A → B → ⋯:
def M₃ : Turing.TM0.Machine Γ Λ
--| Λ.A, symbol => some ⟨Λ.B, Turing.TM0.Stmt.write symbol⟩
--| Λ.B, symbol => some ⟨Λ.C, Turing.TM0.Stmt.write symbol⟩
| Λ.A, symbol => some ⟨Λ.B, Turing.TM0.Stmt.move Dir.left⟩
| Λ.B, symbol => some ⟨Λ.A, Turing.TM0.Stmt.write Γ.one⟩
| _, _ => none

#reduce multistep M₃ 1 cfg₀
-- step 2, halt:
#reduce multistep M₃ 2 cfg₀
-- step 3, still halted:
#reduce  multistep M₃ 99 cfg₀

#reduce TM0.eval M₃ []
