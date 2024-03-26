/-
Copyright (c) 2024 Edward van de Meent. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Edward van de Meent
-/
import Mathlib.Algebra.CovariantAndContravariant
import Mathlib.Algebra.NeZero
import Mathlib.Algebra.Order.Monoid.Lemmas
import Mathlib.Data.Set.Lattice

/-!
# Pseudo-metrics with generic codomain

In this file we introduce `GPseudoMetric`.
This differs from `PseudoMetricSpace` by not requiring that the codomain of the metric be `ℝ`,
instead only requiring that it is an (additive) commutative monoid, with a linear ordering.

## Main definitions

- `GPseudoMetric α β`: a structure containing a distance function on `α` with codomain `β`,
which may be equal to 0 for non-equal elements. The distance function is 0 for equal elements,
is commutative in its arguments, and satisfies the triangle inequality.
- `GPseudoMetricClass α β`: the class of types of generic pseudo-metrics on `α` to `β`.

Additional useful definitions:

- `ball gdist x δ`: the set of points with distance to x strictly less than δ
- `closedBall gdist x δ`: the set of points with distance to x less than or equal to δ
- `sphere gdist x δ`: the set of points with distance to x equal to δ
-/

open Set

/-- Generic pseudo-metrics

A generic pseudo-metric is a distance function `gdist : α → α → β`, which is zero for identical
elements, for which the arguments commute, and for which the triangle inequality holds.
As opposed to a classical pseudo-metric, the codomain of this distance function is not
necessarily ℝ (or ℝ≥0∞), and as a result does not endow α with a uniform space structure.
-/
structure GPseudoMetric (α : Type*) (β : Type*) [LinearOrder β] [AddCommMonoid β] where
  /-- A distance function on α with values in β -/
  toFun : α → α → β
  gdist_self : ∀ x : α, toFun x x = 0
  comm' : ∀ x y : α, toFun x y = toFun y x
  triangle' : ∀ x y z : α, toFun x z ≤ toFun x y + toFun y z

variable {α β : Type*} [LinearOrder β] [AddCommMonoid β] [CovariantClass β β (. + .) (. ≤ .)]

@[ext]
theorem GPseudoMetric.ext {d₁ d₂ : GPseudoMetric α β} (h : d₁.toFun = d₂.toFun) : d₁ = d₂ := by
  cases' d₁; cases' d₂; congr

instance : FunLike (GPseudoMetric α β) α (α → β) where
  coe := GPseudoMetric.toFun
  coe_injective' := by apply GPseudoMetric.ext

/-- A class for types of pseudo-metric functions on α with values in β -/
class GPseudoMetricClass (T : Type*) (α β : outParam Type*) [LinearOrder β] [AddCommMonoid β]
    [CovariantClass β β (. + .) (. ≤ .)] [FunLike T α (α → β)] : Prop :=
  gdist_self : ∀ (gdist : T), ∀ x : α, gdist x x = 0
  comm' : ∀ (gdist : T), ∀ x y:α, gdist x y = gdist y x
  triangle' : ∀ (gdist : T), ∀ (x y z : α), gdist x z ≤ gdist x y + gdist y z

instance: GPseudoMetricClass (GPseudoMetric α β) α β where
  gdist_self := GPseudoMetric.gdist_self
  comm' := GPseudoMetric.comm'
  triangle' := GPseudoMetric.triangle'

variable {T : Type*} [FunLike T α (α → β)] [GPseudoMetricClass T α β] (gdist : T)

@[simp]
theorem gdist_self (x : α) : gdist x x = 0 :=
  GPseudoMetricClass.gdist_self gdist x

theorem comm' (x y : α) : gdist x y = gdist y x :=
  GPseudoMetricClass.comm' gdist x y

theorem triangle' (x y z : α) : gdist x z ≤ gdist x y + gdist y z :=
  GPseudoMetricClass.triangle' gdist x y z

theorem triangle_left (x y z : α) : gdist x y ≤ gdist z x + gdist z y := by
  rw [comm' gdist z]; apply triangle'

theorem triangle_right (x y z : α) : gdist x y ≤ gdist x z + gdist y z := by
  rw [comm' gdist y]; apply triangle'

theorem triangle4 (x y z w : α) : gdist x w ≤ gdist x y + gdist y z + gdist z w :=
  calc
    gdist x w
      ≤ gdist x z + gdist z w := triangle' gdist x z w
    _ ≤ (gdist x y + gdist y z + gdist z w : β) :=
      @act_rel_act_of_rel β β (Function.swap (. + .)) (. ≤ .) _ _ _ _ (triangle' gdist x y z)

theorem triangle4_left (x₁ y₁ x₂ y₂ : α) :
    gdist x₂ y₂ ≤ gdist x₁ y₁ + (gdist x₁ x₂ + gdist y₁ y₂) := by
  rw [add_left_comm, comm' gdist x₁,← add_assoc]
  apply triangle4

theorem triangle4_right (x₁ y₁ x₂ y₂ : α) :
    gdist x₁ y₁ ≤ gdist x₁ x₂ + gdist y₁ y₂ + gdist x₂ y₂ := by
  rw [add_right_comm, comm' gdist y₁]
  apply triangle4

theorem gdist_nonneg {x y : α} : 0 ≤ gdist x y := by
  have h1 : 0 ≤ gdist x y + gdist x y :=
    calc
      0 = gdist x x             := (gdist_self gdist _).symm
      _ ≤ gdist x y + gdist y x := triangle' gdist _ _ _
      _ = gdist x y + gdist x y := by rw [comm' gdist]
  contrapose! h1
  exact Left.add_neg' h1 h1

namespace GMetric

variable {x y z : α} {δ ε ε₁ ε₂ : β} {s : Set α}

section non_cancel

/-- `ball gdist x ε` is the set of all points `y` with `gdist y x < ε` -/
def ball (x : α) (ε : β) : Set α :=
  { y | gdist y x < ε }

@[simp]
theorem mem_ball : y ∈ ball gdist x ε ↔ gdist y x < ε :=
  Iff.rfl

theorem mem_ball' : y ∈ ball gdist x ε ↔ gdist x y < ε := by rw [comm', mem_ball]

theorem pos_of_mem_ball (hy : y ∈ ball gdist x ε) : 0 < ε :=
  (gdist_nonneg gdist).trans_lt hy

theorem mem_ball_self (h : 0 < ε) : x ∈ ball gdist x ε := by
  rwa [mem_ball, gdist_self]

@[simp]
theorem nonempty_ball : (ball gdist x ε).Nonempty ↔ 0 < ε :=
  ⟨fun ⟨_x, hx⟩ => pos_of_mem_ball gdist hx, fun h => ⟨x, mem_ball_self gdist h⟩⟩

@[simp]
theorem ball_eq_empty : ball gdist x ε = ∅ ↔ ε ≤ 0 := by
  rw [← not_nonempty_iff_eq_empty, nonempty_ball, not_lt]

@[simp]
theorem ball_zero : ball gdist x (0 : β) = ∅ := by rw [ball_eq_empty]

/-- `closedBall gdist x ε` is the set of all points `y` with `gdist y x ≤ ε` -/
def closedBall (x : α) (ε : β) :=
  { y | gdist y x ≤ ε }

@[simp] theorem mem_closedBall : y ∈ closedBall gdist x ε ↔ gdist y x ≤ ε := Iff.rfl

theorem mem_closedBall' : y ∈ closedBall gdist x ε ↔ gdist x y ≤ ε := by rw [comm', mem_closedBall]

/-- `sphere gdist x ε` is the set of all points `y` with `gdist y x = ε` -/
def sphere (x : α) (ε : β) := { y | gdist y x = ε }

@[simp] theorem mem_sphere : y ∈ sphere gdist x ε ↔ gdist y x = ε := Iff.rfl

theorem mem_sphere' : y ∈ sphere gdist x ε ↔ gdist x y = ε := by rw [comm', mem_sphere]

theorem ne_of_mem_sphere (h : y ∈ sphere gdist x ε) (hε : ε ≠ 0) : y ≠ x :=
  ne_of_mem_of_not_mem h <| by simpa using hε.symm

theorem nonneg_of_mem_sphere (hy : y ∈ sphere gdist x ε) : 0 ≤ ε :=
  (gdist_nonneg gdist).trans_eq hy

@[simp]
theorem sphere_eq_empty_of_neg (hε : ε < 0) : sphere gdist x ε = ∅ :=
  Set.eq_empty_iff_forall_not_mem.mpr fun _y hy => (nonneg_of_mem_sphere gdist hy).not_lt hε

theorem sphere_eq_empty_of_subsingleton [Subsingleton α] (hε : ε ≠ 0) : sphere gdist x ε = ∅ :=
  Set.eq_empty_iff_forall_not_mem.mpr fun _ h => ne_of_mem_sphere gdist h hε (Subsingleton.elim _ _)

instance sphere_isEmpty_of_subsingleton
    [Subsingleton α] [NeZero ε] : IsEmpty (sphere gdist x ε) := by
  rw [sphere_eq_empty_of_subsingleton gdist (NeZero.ne ε)]; infer_instance

theorem mem_closedBall_self (h : 0 ≤ ε) : x ∈ closedBall gdist x ε := by
  rwa [mem_closedBall, gdist_self]

@[simp]
theorem nonempty_closedBall : (closedBall gdist x ε).Nonempty ↔ 0 ≤ ε :=
  ⟨fun ⟨_x, hx⟩ => (gdist_nonneg gdist).trans hx, fun h => ⟨x, mem_closedBall_self gdist h⟩⟩

@[simp]
theorem closedBall_eq_empty : closedBall gdist x ε = ∅ ↔ ε < 0 := by
  rw [← not_nonempty_iff_eq_empty, nonempty_closedBall, not_le]

/-- Closed balls and spheres coincide when the radius is non-positive -/
theorem closedBall_eq_sphere_of_nonpos (hε : ε ≤ 0) : closedBall gdist x ε = sphere gdist x ε :=
  Set.ext fun _ => (hε.trans (gdist_nonneg gdist)).le_iff_eq

theorem ball_subset_closedBall : ball gdist x ε ⊆ closedBall gdist x ε := fun _y hy =>
  (mem_closedBall gdist).2 (le_of_lt hy)

theorem sphere_subset_closedBall : sphere gdist x ε ⊆ closedBall gdist x ε := fun _ => le_of_eq

lemma sphere_subset_ball {r R : β} (h : r < R) : sphere gdist x r ⊆ ball gdist x R := fun _x hx ↦
  ((mem_sphere gdist).1 hx).trans_lt h

end non_cancel

section weak_cancel

variable [ContravariantClass β β (. + .) (. < .)]

theorem closedBall_disjoint_closedBall (h : δ + ε < gdist x y) :
    Disjoint (closedBall gdist x δ) (closedBall gdist y ε) :=
  Set.disjoint_left.mpr fun _a ha1 ha2 =>
    h.not_le <| (triangle_left gdist _ _ _).trans <| add_le_add ha1 ha2

theorem sphere_disjoint_ball : Disjoint (sphere gdist x ε) (ball gdist x ε) :=
  Set.disjoint_left.mpr fun _y hy₁ hy₂ => absurd hy₁ <| ne_of_lt hy₂

@[simp]
theorem ball_union_sphere : ball gdist x ε ∪ sphere gdist x ε = closedBall gdist x ε :=
  Set.ext fun _y => (@le_iff_lt_or_eq β _ _ _).symm

@[simp]
theorem sphere_union_ball : sphere gdist x ε ∪ ball gdist x ε = closedBall gdist x ε := by
  rw [union_comm, ball_union_sphere]

@[simp]
theorem closedBall_diff_sphere : closedBall gdist x ε \ sphere gdist x ε = ball gdist x ε := by
  rw [← ball_union_sphere, Set.union_diff_cancel_right (sphere_disjoint_ball gdist).symm.le_bot]

@[simp]
theorem closedBall_diff_ball : closedBall gdist x ε \ ball gdist x ε = sphere gdist x ε := by
  rw [← ball_union_sphere, Set.union_diff_cancel_left (sphere_disjoint_ball gdist).symm.le_bot]

theorem mem_ball_comm : x ∈ ball gdist y ε ↔ y ∈ ball gdist x ε := by rw [mem_ball', mem_ball]

theorem mem_closedBall_comm : x ∈ closedBall gdist y ε ↔ y ∈ closedBall gdist x ε := by
  rw [mem_closedBall', mem_closedBall]

theorem mem_sphere_comm : x ∈ sphere gdist y ε ↔ y ∈ sphere gdist x ε := by
  rw [mem_sphere', mem_sphere]

theorem ball_subset_ball (h : ε₁ ≤ ε₂) : ball gdist x ε₁ ⊆ ball gdist x ε₂ := fun _y yx =>
  lt_of_lt_of_le ((mem_ball gdist).1 yx) h

theorem closedBall_eq_bInter_ball : closedBall gdist x ε = ⋂ δ > ε, ball gdist x δ := by
  ext y; rw [mem_closedBall, ← forall_lt_iff_le', mem_iInter₂]; rfl

theorem closedBall_subset_closedBall (h : ε₁ ≤ ε₂) :
    closedBall gdist x ε₁ ⊆ closedBall gdist x ε₂ :=
  fun _y (yx : _ ≤ ε₁) => le_trans yx h

theorem closedBall_subset_closedBall' (h : ε₁ + gdist x y ≤ ε₂) :
    closedBall gdist x ε₁ ⊆ closedBall gdist y ε₂ := fun z hz =>
  calc
    gdist z y
      ≤ gdist z x + gdist x y := triangle' gdist _ _ _
    _ ≤ ε₁ + gdist x y        := add_le_add_right ((mem_closedBall gdist).1 hz) _
    _ ≤ ε₂                    := h

theorem closedBall_subset_ball (h : ε₁ < ε₂) : closedBall gdist x ε₁ ⊆ ball gdist x ε₂ :=
  fun y (yh : gdist y x ≤ ε₁) => lt_of_le_of_lt yh h

theorem closedBall_subset_ball' (h : ε₁ + gdist x y < ε₂) :
    closedBall gdist x ε₁ ⊆ ball gdist y ε₂ := fun z hz =>
  calc
    gdist z y
      ≤ gdist z x + gdist x y := triangle' gdist _ _ _
    _ ≤ ε₁ + gdist x y        := add_le_add_right ((mem_closedBall gdist).1 hz) _
    _ < ε₂                    := h

theorem gdist_le_add_of_nonempty_closedBall_inter_closedBall
    (h : (closedBall gdist x ε₁ ∩ closedBall gdist y ε₂).Nonempty) : gdist x y ≤ ε₁ + ε₂ :=
  let ⟨z, hz⟩ := h
  calc
    gdist x y
      ≤ gdist z x + gdist z y := triangle_left gdist _ _ _
    _ ≤ ε₁ + ε₂               := add_le_add hz.1 hz.2
end weak_cancel

section strong_cancel

variable [ContravariantClass β β (. + .) (. ≤ .)]

theorem closedBall_disjoint_ball
    (h : δ + ε ≤ gdist x y) : Disjoint (closedBall gdist x δ) (ball gdist y ε) :=
  Set.disjoint_left.mpr fun _a ha1 ha2 =>
    (h.trans <| triangle_left gdist _ _ _).not_lt <| add_lt_add_of_le_of_lt ha1 ha2

theorem ball_disjoint_closedBall
    (h : δ + ε ≤ gdist x y) : Disjoint (ball gdist x δ) (closedBall gdist (y : α) (ε : β)) :=
  (closedBall_disjoint_ball gdist <| by rwa [add_comm, comm']).symm

theorem ball_disjoint_ball (h : δ + ε ≤ gdist x y) : Disjoint (ball gdist x δ) (ball gdist y ε) :=
  (closedBall_disjoint_ball gdist h).mono_left (ball_subset_closedBall gdist)

theorem ball_subset_ball' (h : ε₁ + gdist x y ≤ ε₂) : ball gdist x ε₁ ⊆ ball gdist y ε₂ := fun
  z hz =>
    calc
      gdist z y
        ≤ gdist z x + gdist x y := by apply triangle' gdist
      _ < ε₁ + gdist x y := by exact add_lt_add_right hz _
      _ ≤ ε₂ := h

theorem gdist_lt_add_of_nonempty_closedBall_inter_ball
    (h : (closedBall gdist x ε₁ ∩ ball gdist y ε₂).Nonempty) : gdist x y < ε₁ + ε₂ :=
  let ⟨z, hz⟩ := h
  calc
    gdist x y
      ≤ gdist z x + gdist z y := triangle_left gdist _ _ _
    _ < ε₁ + ε₂               := add_lt_add_of_le_of_lt hz.1 hz.2

theorem gdist_lt_add_of_nonempty_ball_inter_closedBall
    (h : (ball gdist x ε₁ ∩ closedBall gdist y ε₂).Nonempty) : gdist x y < ε₁ + ε₂ := by
  rw [inter_comm] at h
  rw [add_comm, comm']
  exact gdist_lt_add_of_nonempty_closedBall_inter_ball gdist h

theorem gdist_lt_add_of_nonempty_ball_inter_ball
    (h : (ball gdist x ε₁ ∩ ball gdist y ε₂).Nonempty) : gdist x y < ε₁ + ε₂ :=
  gdist_lt_add_of_nonempty_closedBall_inter_ball gdist <|
    h.mono (inter_subset_inter (ball_subset_closedBall gdist) Subset.rfl)
end strong_cancel
