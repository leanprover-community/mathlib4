/-
Copyright (c) 2020 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers, Yury Kudryashov
-/
import Mathlib.Algebra.AddTorsor.Defs
import Mathlib.Algebra.Group.Action.Basic
import Mathlib.Algebra.Group.End
import Mathlib.Algebra.Group.Pointwise.Set.Scalar

/-!
# Torsors of additive group actions

Further results for torsors, that are not in `Mathlib/Algebra/AddTorsor/Defs.lean` to avoid
increasing imports there.
-/

open scoped Pointwise


section General

variable {G : Type*} {P : Type*} [AddGroup G] [T : AddTorsor G P]

namespace Set

theorem singleton_vsub_self (p : P) : ({p} : Set P) -ᵥ {p} = {(0 : G)} := by
  rw [Set.singleton_vsub_singleton, vsub_self]

end Set

/-- If the same point subtracted from two points produces equal
results, those points are equal. -/
theorem vsub_left_cancel {p₁ p₂ p : P} (h : p₁ -ᵥ p = p₂ -ᵥ p) : p₁ = p₂ := by
  rwa [← sub_eq_zero, vsub_sub_vsub_cancel_right, vsub_eq_zero_iff_eq] at h

/-- The same point subtracted from two points produces equal results
if and only if those points are equal. -/
@[simp]
theorem vsub_left_cancel_iff {p₁ p₂ p : P} : p₁ -ᵥ p = p₂ -ᵥ p ↔ p₁ = p₂ :=
  ⟨vsub_left_cancel, fun h => h ▸ rfl⟩

/-- Subtracting the point `p` is an injective function. -/
theorem vsub_left_injective (p : P) : Function.Injective ((· -ᵥ p) : P → G) := fun _ _ =>
  vsub_left_cancel

/-- If subtracting two points from the same point produces equal
results, those points are equal. -/
theorem vsub_right_cancel {p₁ p₂ p : P} (h : p -ᵥ p₁ = p -ᵥ p₂) : p₁ = p₂ := by
  refine vadd_left_cancel (p -ᵥ p₂) ?_
  rw [vsub_vadd, ← h, vsub_vadd]

/-- Subtracting two points from the same point produces equal results
if and only if those points are equal. -/
@[simp]
theorem vsub_right_cancel_iff {p₁ p₂ p : P} : p -ᵥ p₁ = p -ᵥ p₂ ↔ p₁ = p₂ :=
  ⟨vsub_right_cancel, fun h => h ▸ rfl⟩

/-- Subtracting a point from the point `p` is an injective
function. -/
theorem vsub_right_injective (p : P) : Function.Injective ((p -ᵥ ·) : P → G) := fun _ _ =>
  vsub_right_cancel

end General

section comm

variable {G : Type*} {P : Type*} [AddCommGroup G] [AddTorsor G P]

/-- Cancellation subtracting the results of two subtractions. -/
@[simp]
theorem vsub_sub_vsub_cancel_left (p₁ p₂ p₃ : P) : p₃ -ᵥ p₂ - (p₃ -ᵥ p₁) = p₁ -ᵥ p₂ := by
  rw [sub_eq_add_neg, neg_vsub_eq_vsub_rev, add_comm, vsub_add_vsub_cancel]

@[simp]
theorem vadd_vsub_vadd_cancel_left (v : G) (p₁ p₂ : P) : (v +ᵥ p₁) -ᵥ (v +ᵥ p₂) = p₁ -ᵥ p₂ := by
  rw [vsub_vadd_eq_vsub_sub, vadd_vsub_assoc, add_sub_cancel_left]

theorem vadd_vsub_vadd (v₁ v₂ : G) (p₁ p₂ : P) : (v₁ +ᵥ p₁) -ᵥ (v₂ +ᵥ p₂) = (v₁ - v₂)
    + (p₁ -ᵥ p₂) := by
  rw [vsub_vadd_eq_vsub_sub, vadd_vsub_assoc, add_sub_assoc, ← add_comm_sub]

theorem vsub_vadd_comm (p₁ p₂ p₃ : P) : (p₁ -ᵥ p₂ : G) +ᵥ p₃ = (p₃ -ᵥ p₂) +ᵥ p₁ := by
  rw [← @vsub_eq_zero_iff_eq G, vadd_vsub_assoc, vsub_vadd_eq_vsub_sub]
  simp

theorem vadd_eq_vadd_iff_sub_eq_vsub {v₁ v₂ : G} {p₁ p₂ : P} :
    v₁ +ᵥ p₁ = v₂ +ᵥ p₂ ↔ v₂ - v₁ = p₁ -ᵥ p₂ := by
  rw [vadd_eq_vadd_iff_neg_add_eq_vsub, neg_add_eq_sub]

theorem vsub_sub_vsub_comm (p₁ p₂ p₃ p₄ : P) : p₁ -ᵥ p₂ - (p₃ -ᵥ p₄) = p₁ -ᵥ p₃ - (p₂ -ᵥ p₄) := by
  rw [← vsub_vadd_eq_vsub_sub, vsub_vadd_comm, vsub_vadd_eq_vsub_sub]

namespace Set

@[simp] lemma vadd_set_vsub_vadd_set (v : G) (s t : Set P) : (v +ᵥ s) -ᵥ (v +ᵥ t) = s -ᵥ t := by
  ext; simp [mem_vsub, mem_vadd_set]

end Set

end comm

namespace Prod

variable {G G' P P' : Type*} [AddGroup G] [AddGroup G'] [AddTorsor G P] [AddTorsor G' P']

instance instAddTorsor : AddTorsor (G × G') (P × P') where
  vadd v p := (v.1 +ᵥ p.1, v.2 +ᵥ p.2)
  zero_vadd _ := Prod.ext (zero_vadd _ _) (zero_vadd _ _)
  add_vadd _ _ _ := Prod.ext (add_vadd _ _ _) (add_vadd _ _ _)
  vsub p₁ p₂ := (p₁.1 -ᵥ p₂.1, p₁.2 -ᵥ p₂.2)
  vsub_vadd' _ _ := Prod.ext (vsub_vadd _ _) (vsub_vadd _ _)
  vadd_vsub' _ _ := Prod.ext (vadd_vsub _ _) (vadd_vsub _ _)

@[simp]
theorem fst_vadd (v : G × G') (p : P × P') : (v +ᵥ p).1 = v.1 +ᵥ p.1 :=
  rfl

@[simp]
theorem snd_vadd (v : G × G') (p : P × P') : (v +ᵥ p).2 = v.2 +ᵥ p.2 :=
  rfl

@[simp]
theorem mk_vadd_mk (v : G) (v' : G') (p : P) (p' : P') : (v, v') +ᵥ (p, p') = (v +ᵥ p, v' +ᵥ p') :=
  rfl

@[simp]
theorem fst_vsub (p₁ p₂ : P × P') : (p₁ -ᵥ p₂ : G × G').1 = p₁.1 -ᵥ p₂.1 :=
  rfl

@[simp]
theorem snd_vsub (p₁ p₂ : P × P') : (p₁ -ᵥ p₂ : G × G').2 = p₁.2 -ᵥ p₂.2 :=
  rfl

@[simp]
theorem mk_vsub_mk (p₁ p₂ : P) (p₁' p₂' : P') :
    ((p₁, p₁') -ᵥ (p₂, p₂') : G × G') = (p₁ -ᵥ p₂, p₁' -ᵥ p₂') :=
  rfl

end Prod

namespace Pi

universe u v w

variable {I : Type u} {fg : I → Type v} [∀ i, AddGroup (fg i)] {fp : I → Type w}

open AddAction AddTorsor

/-- A product of `AddTorsor`s is an `AddTorsor`. -/
instance instAddTorsor [∀ i, AddTorsor (fg i) (fp i)] : AddTorsor (∀ i, fg i) (∀ i, fp i) where
  vadd g p i := g i +ᵥ p i
  zero_vadd p := funext fun i => zero_vadd (fg i) (p i)
  add_vadd g₁ g₂ p := funext fun i => add_vadd (g₁ i) (g₂ i) (p i)
  vsub p₁ p₂ i := p₁ i -ᵥ p₂ i
  vsub_vadd' p₁ p₂ := funext fun i => vsub_vadd (p₁ i) (p₂ i)
  vadd_vsub' g p := funext fun i => vadd_vsub (g i) (p i)

end Pi

namespace Equiv

variable (G : Type*) (P : Type*) [AddGroup G] [AddTorsor G P]

@[simp]
theorem constVAdd_zero : constVAdd P (0 : G) = 1 :=
  ext <| zero_vadd G

variable {G}

@[simp]
theorem constVAdd_add (v₁ v₂ : G) : constVAdd P (v₁ + v₂) = constVAdd P v₁ * constVAdd P v₂ :=
  ext <| add_vadd v₁ v₂

/-- `Equiv.constVAdd` as a homomorphism from `Multiplicative G` to `Equiv.perm P` -/
def constVAddHom : Multiplicative G →* Equiv.Perm P where
  toFun v := constVAdd P (v.toAdd)
  map_one' := constVAdd_zero G P
  map_mul' := constVAdd_add P

variable {P}

open Function

@[simp]
theorem left_vsub_pointReflection (x y : P) : x -ᵥ pointReflection x y = y -ᵥ x :=
  neg_injective <| by simp

@[simp]
theorem right_vsub_pointReflection (x y : P) : y -ᵥ pointReflection x y = 2 • (y -ᵥ x) :=
  neg_injective <| by simp [← neg_nsmul]

/-- `x` is the only fixed point of `pointReflection x`. This lemma requires
`x + x = y + y ↔ x = y`. There is no typeclass to use here, so we add it as an explicit argument. -/
theorem pointReflection_fixed_iff_of_injective_two_nsmul {x y : P} (h : Injective (2 • · : G → G)) :
    pointReflection x y = y ↔ y = x := by
  rw [pointReflection_apply, eq_comm, eq_vadd_iff_vsub_eq, ← neg_vsub_eq_vsub_rev,
    neg_eq_iff_add_eq_zero, ← two_nsmul, ← nsmul_zero 2, h.eq_iff, vsub_eq_zero_iff_eq, eq_comm]

@[deprecated (since := "2024-11-18")] alias pointReflection_fixed_iff_of_injective_bit0 :=
pointReflection_fixed_iff_of_injective_two_nsmul

theorem injective_pointReflection_left_of_injective_two_nsmul {G P : Type*} [AddCommGroup G]
    [AddTorsor G P] (h : Injective (2 • · : G → G)) (y : P) :
    Injective fun x : P => pointReflection x y :=
  fun x₁ x₂ (hy : pointReflection x₁ y = pointReflection x₂ y) => by
  rwa [pointReflection_apply, pointReflection_apply, vadd_eq_vadd_iff_sub_eq_vsub,
    vsub_sub_vsub_cancel_right, ← neg_vsub_eq_vsub_rev, neg_eq_iff_add_eq_zero,
    ← two_nsmul, ← nsmul_zero 2, h.eq_iff, vsub_eq_zero_iff_eq] at hy

@[deprecated (since := "2024-11-18")] alias injective_pointReflection_left_of_injective_bit0 :=
injective_pointReflection_left_of_injective_two_nsmul

/-- In the special case of additive commutative groups (as opposed to just additive torsors),
`Equiv.pointReflection x` coincides with `Equiv.subLeft (2 • x)`. -/
lemma pointReflection_eq_subLeft {G : Type*} [AddCommGroup G] (x : G) :
    pointReflection x = Equiv.subLeft (2 • x) := by
  ext; simp [pointReflection, sub_add_eq_add_sub, two_nsmul]

end Equiv
