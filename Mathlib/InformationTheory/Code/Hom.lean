import Mathlib.InformationTheory.Code.Basic
import Mathlib.Topology.GMetric.Isometry
import Mathlib.Topology.GMetric.GNorm
open Set
open GMetric
open GIsometry
open Code

variable {T:Type*}
variable {γ :Type*} [CompleteLinearOrder γ] [AddCommMonoid γ]

variable {α₁ T₁:Type*} {gdist₁:T₁} {s₁:Set α₁}
variable--? [_Code γ gdist s] =>
  [CovariantClass γ γ (fun x x_1 ↦ x + x_1) fun x x_1 ↦ x ≤ x_1]
  [FunLike T₁ α₁ (α₁ → γ)] [GPseudoMetricClass T₁ α₁ γ] [IsDelone gdist₁ s₁]

variable {α₂ T₂ :Type*} {gdist₂:T₂} {s₂ : Set α₂}
variable--? [_Code γ gdist₂ s₂] =>
  [FunLike T₂ α₂ (α₂ → γ)] [GPseudoMetricClass T₂ α₂ γ]
  [IsDelone gdist₂ s₂]


variable [FunLike T α₁ α₂] [GIsometryClass T gdist₁ gdist₂]

section
variable (T gdist₁ s₁ gdist₂ s₂)
structure CodeHom [_Code γ gdist₁ s₁] [_Code γ gdist₂ s₂] extends GIsometry gdist₁ gdist₂ where
  map_code : ∀ x ∈ s₁, toFun x ∈ s₂

class CodeHomClass {γ :outParam Type*} [CompleteLinearOrder γ] [AddCommMonoid γ]
    [CovariantClass γ γ (.+.) (.≤.)]
    {α₁ α₂ T₁ T₂:outParam Type*} [FunLike T₁ α₁ (α₁ → γ)] (gdist₁:outParam T₁) (s₁: outParam (Set α₁))
    [GPseudoMetricClass T₁ α₁ γ] [IsDelone gdist₁ s₁] [_Code γ gdist₁ s₁]
    [FunLike T₂ α₂ (α₂ → γ)] (gdist₂:outParam T₂) (s₂: outParam (Set α₂))
    [GPseudoMetricClass T₂ α₂ γ] [IsDelone gdist₂ s₂] [_Code γ gdist₂ s₂]
    [FunLike T α₁ α₂] extends GIsometryClass T gdist₁ gdist₂ :Prop where
  map_code' : ∀ (φ:T), ∀ x ∈ s₁, φ x ∈ s₂
end

namespace CodeHom
instance instFunLike : FunLike (CodeHom gdist₁ s₁ gdist₂ s₂) α₁ α₂ where
  coe := fun φ => φ.toGIsometry
  coe_injective' := fun φ₁ φ₂ h => by
    cases φ₁; cases φ₂; congr; simp_all

@[ext]
lemma ext ⦃φ:CodeHom gdist₁ s₁ gdist₂ s₂⦄ ⦃φ₂:CodeHom gdist₁ s₁ gdist₂ s₂⦄
    (h:∀ x, φ x = φ₂ x): φ = φ₂ := DFunLike.ext _ _ h

instance instCodeHomClass :
    CodeHomClass (CodeHom gdist₁ s₁ gdist₂ s₂) gdist₁ s₁ gdist₂ s₂ where
  map_dist' := fun φ => φ.map_dist
  map_code' := fun φ => φ.map_code
end CodeHom

def CodeHomClass.toCodeHom
    [CodeHomClass T gdist₁ s₁ gdist₂ s₂] (φ:T) : CodeHom gdist₁ s₁ gdist₂ s₂ where
  toFun := φ
  map_dist := GIsometryClass.map_dist' φ
  map_code := map_code' φ

instance [CodeHomClass T gdist₁ s₁ gdist₂ s₂]: CoeTC T (CodeHom gdist₁ s₁ gdist₂ s₂) :=
  ⟨CodeHomClass.toCodeHom⟩

namespace CodeHom
@[simp]
theorem coe_coe
    [CodeHomClass T gdist₁ s₁ gdist₂ s₂] (φ:T) : ((φ : CodeHom gdist₁ s₁ gdist₂ s₂): α₁ → α₂) = φ := by
  rfl

@[simp]
theorem coe_mk
  (f : GIsometry gdist₁ gdist₂) (map_code: ∀ x ∈ s₁, f x ∈ s₂) :
  (CodeHom.mk f map_code : α₁ → α₂) = f := rfl

protected def copy
    (f : CodeHom gdist₁ s₁ gdist₂ s₂) (f' : α₁ → α₂) (h : f' = f) :
    CodeHom gdist₁ s₁ gdist₂ s₂ := {
      f.toGIsometry.copy f' h with
      map_code := by
        simp_rw [GIsometry.copy]
        exact h.symm ▸ f.map_code
    }

@[simp]
theorem coe_copy (f : CodeHom gdist₁ s₁ gdist₂ s₂) (f' : α₁ → α₂) (h : f' = f) :
    (f.copy f' h) = f' := rfl

theorem coe_copy_eq
    (f :CodeHom gdist₁ s₁ gdist₂ s₂) (f' : α₁ → α₂) (h : f' = f) : f.copy f' h = f :=
  DFunLike.ext' h

variable {T₃ α₃ :Type*} {gdist₃:T₃} {s₃:Set α₃}
variable--? [_Code γ gdist₃ s₃] =>
  [FunLike T₃ α₃ (α₃ → γ)] [GPseudoMetricClass T₃ α₃ γ] [IsDelone gdist₃ s₃]


section id
variable (gdist₁ s₁)
@[simps!]
def id [_Code γ gdist₁ s₁] : CodeHom gdist₁ s₁ gdist₁ s₁ := {
  GIsometry.id gdist₁ with
  map_code := fun _ a ↦ a
}
end id

def comp
    (φ₂: CodeHom gdist₂ s₂ gdist₃ s₃) (φ: CodeHom gdist₁ s₁ gdist₂ s₂) : CodeHom gdist₁ s₁ gdist₃ s₃ := {
  φ₂.toGIsometry.comp φ.toGIsometry with
  map_code := fun x hx => φ₂.map_code (φ x) <| φ.map_code x hx
  }

@[simp]
theorem coe_comp (g : CodeHom gdist₂ s₂ gdist₃ s₃) (f : CodeHom gdist₁ s₁ gdist₂ s₂) :
    ↑(g.comp f) = g ∘ f := rfl

theorem comp_apply
    (g : CodeHom gdist₂ s₂ gdist₃ s₃) (f : CodeHom gdist₁ s₁ gdist₂ s₂) (x : α₁):
  g.comp f x = g (f x) := rfl

variable {α₄ T₄:Type*} {gdist₄:T₄} {s₄:Set α₄}
variable--? [_Code γ gdist₄ s₄] =>
  [FunLike T₄ α₄ (α₄ → γ)] [GPseudoMetricClass T₄ α₄ γ] [IsDelone gdist₄ s₄]


theorem comp_assoc (h: CodeHom gdist₃ s₃ gdist₄ s₄)
    (g : CodeHom gdist₂ s₂ gdist₃ s₃) (f : CodeHom gdist₁ s₁ gdist₂ s₂):
    (h.comp g).comp f = h.comp (g.comp f) := rfl

theorem cancel_right {g₁ g₂ : CodeHom gdist₂ s₂ gdist₃ s₃} {f : CodeHom gdist₁ s₁ gdist₂ s₂}
    (hf : Function.Surjective f) : g₁.comp f = g₂.comp f ↔ g₁ = g₂ := by
  constructor
  . intro h
    apply ext
    intro y
    apply (@Function.Surjective.forall α₁ α₂ f hf (fun y => g₁ y = g₂ y)).2
    intro x
    rw [← CodeHom.comp_apply,h,CodeHom.comp_apply]
  . exact fun h => h ▸ rfl

@[simp]
theorem comp_id (f : CodeHom gdist₁ s₁ gdist₂ s₂) : f.comp (CodeHom.id gdist₁ s₁) = f :=
  ext fun _ => rfl

@[simp]
theorem id_comp (f : CodeHom gdist₁ s₁ gdist₂ s₂) : (id gdist₂ s₂).comp f = f :=
  CodeHom.ext fun _ => rfl
