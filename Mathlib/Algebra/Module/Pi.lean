/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon, Patrick Massot
-/
module

public import Mathlib.Algebra.GroupWithZero.Action.Pi
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Regular.SMul
public import Mathlib.Algebra.Ring.Pi

set_option doc.verso true
set_option doc.verso.suggestions false

/-!
# Pi instances for modules

This file defines instances for module and related structures on Pi types.

We also define the natural maps `LinearMap.pi` and `LinearMap.proj` on `Pi` types in the domain and
codomain, respectively.
-/

public section


universe u v w

variable {I : Type u}

-- The indexing type
variable {f : I → Type v}

namespace Pi

theorem _root_.IsSMulRegular.pi {α : Type*} [∀ i, SMul α <| f i] {k : α}
    (hk : ∀ i, IsSMulRegular (f i) k) : IsSMulRegular (∀ i, f i) k := fun _ _ h =>
  funext fun i => hk i congr($h i)

variable (I f)

instance module (α) {r : Semiring α} {m : ∀ i, AddCommMonoid <| f i} [∀ i, Module α <| f i] :
    @Module α (∀ i : I, f i) r (@Pi.addCommMonoid I f m) :=
  { Pi.distribMulAction _ with
    add_smul := fun _ _ _ => funext fun _ => add_smul _ _ _
    zero_smul := fun _ => funext fun _ => zero_smul α _ }

/- Extra instance to short-circuit type class resolution.
For unknown reasons, this is necessary for certain inference problems. E.g., for this to succeed:
```lean
example (β X : Type*) [NormedAddCommGroup β] [NormedSpace ℝ β] : Module ℝ (X → β) := inferInstance
```
See: https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/Typeclass.20resolution.20under.20binders/near/281296989
-/
/-- A special case of `Pi.module` for non-dependent types. Lean struggles to elaborate
definitions elsewhere in the library without this. -/
instance Function.module (α β : Type*) [Semiring α] [AddCommMonoid β] [Module α β] :
    Module α (I → β) :=
  Pi.module _ _ _

variable {I f}

instance module' {g : I → Type*} {r : ∀ i, Semiring (f i)} {m : ∀ i, AddCommMonoid (g i)}
    [∀ i, Module (f i) (g i)] : Module (∀ i, f i) (∀ i, g i) where
  add_smul := by
    intros
    ext1
    apply add_smul
  zero_smul := by
    intros
    ext1
    rw [zero_smul]

end Pi

@[expose] section

namespace LinearMap

variable {R M M₂ M₃ ι ι' : Type*}
variable [Semiring R] [AddCommMonoid M₂] [Module R M₂] [AddCommMonoid M₃] [Module R M₃]
  {φ : ι → Type*} [(i : ι) → AddCommMonoid (φ i)] [(i : ι) → Module R (φ i)]

/-- `pi` construction for linear functions. From a family of linear functions it produces a linear
function into a family of modules. -/
def pi (f : (i : ι) → M₂ →ₗ[R] φ i) : M₂ →ₗ[R] (i : ι) → φ i :=
  { AddHom.pi fun i => (f i).toAddHom with
    toFun := fun c i => f i c
    map_smul' := fun _ _ => funext fun i => (f i).map_smul _ _ }

@[simp]
theorem pi_apply (f : (i : ι) → M₂ →ₗ[R] φ i) (c : M₂) (i : ι) : pi f c i = f i c :=
  rfl

theorem pi_eq_zero (f : (i : ι) → M₂ →ₗ[R] φ i) : pi f = 0 ↔ ∀ i, f i = 0 := by
  simp only [LinearMap.ext_iff, pi_apply, funext_iff]
  exact ⟨fun h a b => h b a, fun h a b => h b a⟩

theorem pi_zero : pi (fun _ => 0 : (i : ι) → M₂ →ₗ[R] φ i) = 0 := by ext; rfl

theorem pi_comp (f : (i : ι) → M₂ →ₗ[R] φ i) (g : M₃ →ₗ[R] M₂) :
    (pi f).comp g = pi fun i => (f i).comp g :=
  rfl

/-- The constant linear map, taking `x` to `Function.const ι x`. -/
def const : M₂ →ₗ[R] (ι → M₂) := pi fun _ ↦ .id

@[simp] lemma const_apply (x : M₂) : LinearMap.const (R := R) x = Function.const ι x := rfl

/-- The projections from a family of modules are linear maps.

Note: this definition would be called `Pi.evalLinearMap` if we followed the pattern established by
`Pi.evalAddHom`, `Pi.evalMonoidHom`, `Pi.evalRingHom`, ... -/
def proj (i : ι) : ((i : ι) → φ i) →ₗ[R] φ i where
  toFun := Function.eval i
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem coe_proj (i : ι) : ⇑(proj i : ((i : ι) → φ i) →ₗ[R] φ i) = Function.eval i :=
  rfl

@[simp]
theorem toAddMonoidHom_proj (i : ι) : (proj i).toAddMonoidHom (R := R) = Pi.evalAddMonoidHom φ i :=
  rfl

theorem proj_apply (i : ι) (b : (i : ι) → φ i) : (proj i : ((i : ι) → φ i) →ₗ[R] φ i) b = b i :=
  rfl

@[simp]
theorem proj_pi (f : (i : ι) → M₂ →ₗ[R] φ i) (i : ι) : (proj i).comp (pi f) = f i := rfl

@[simp]
theorem pi_proj : pi proj = LinearMap.id (R := R) (M := ∀ i, φ i) := rfl

@[simp]
theorem pi_proj_comp (f : M₂ →ₗ[R] ∀ i, φ i) : pi (proj · ∘ₗ f) = f := rfl

theorem proj_surjective (i : ι) : Function.Surjective (proj i : ((i : ι) → φ i) →ₗ[R] φ i) :=
  Function.surjective_eval i

end LinearMap
