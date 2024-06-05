import Mathlib.InformationTheory.Code.Equiv
open Code

variable {α γ T :Type*} (gdist:T) (s:Set α)
variable--? [_Code γ gdist s] =>
  [CompleteLinearOrder γ] [AddCommMonoid γ]
  [CovariantClass γ γ (fun x x_1 ↦ x + x_1) fun x x_1 ↦ x ≤ x_1] [FunLike T α (α → γ)]
  [GPseudoMetricClass T α γ] [Set.GMetric.IsDelone gdist s]

@[reducible]
def CodeAut [_Code γ gdist s] :Type _ := CodeEquiv gdist s gdist s

namespace CodeAut

instance instGroup [_Code γ gdist s] : Group (CodeAut gdist s) := {
    mul := fun a b => b.trans a
    mul_assoc := fun a b c ↦ rfl
    one := CodeEquiv.refl gdist s
    one_mul := fun a ↦ rfl
    mul_one := fun a ↦ rfl
    inv := CodeEquiv.symm
    mul_left_inv := CodeEquiv.self_trans_symm
    }


@[simp]
theorem coe_mul (e₁ e₂ : CodeAut gdist s) : ⇑(e₁ * e₂) = e₁ ∘ e₂ :=
  rfl

@[simp]
theorem coe_one : ⇑(1 : CodeAut gdist s) = id :=
  rfl

theorem mul_def (e₁ e₂ : CodeAut gdist s) : e₁ * e₂ = e₂.trans e₁ :=
  rfl

theorem one_def : (1 : CodeAut gdist s) = CodeEquiv.refl _ _ :=
  rfl

theorem inv_def (e₁ : CodeAut gdist s) : e₁⁻¹ = e₁.symm :=
  rfl


@[simp]
theorem mul_apply (e₁ e₂ : CodeAut gdist s) (a : α) : (e₁ * e₂) a = e₁ (e₂ a) :=
  rfl

@[simp]
theorem one_apply (a : α) : (1 : CodeAut gdist s) a = a :=
  rfl

@[simp]
theorem apply_inv_self (e : CodeAut gdist s) (a : α) : e (e⁻¹ a) = a :=
  CodeEquiv.apply_symm_apply _ _

@[simp]
theorem inv_apply_self (e : CodeAut gdist s) (a : α) : e⁻¹ (e a) = a :=
  CodeEquiv.apply_symm_apply _ _

def toPerm : CodeAut gdist s →* Equiv.Perm α where
  toFun := fun f => EquivLike.toEquiv f
  map_one' := by simp_all only; rfl
  map_mul' := fun x y => by simp_all only; rfl

end CodeAut
