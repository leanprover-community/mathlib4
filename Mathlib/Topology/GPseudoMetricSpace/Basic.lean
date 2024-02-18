/-
Copyright (c) 2024 Edward van de Meent. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Edward van de Meent
-/
import Mathlib.Algebra.BigOperators.Order
import Mathlib.Data.Nat.Interval
import Mathlib.Topology.Bornology.Basic
import Mathlib.Topology.GPseudoMetricSpace.IsOrderedAddCommMonoid

/-!
# General Pseudo-Metric Spaces

In this file we introduce `GPseudoMetricSpace`.
This differs from `PseudoMetricSpace` by not requiring that the codomain of the metric be `ℝ`,
instead only requiring that it is an (additive) commutative monoid, with a linear ordering that
respects sensible assumptions about interactions between `+` and `≤`.
## Main Definitions

- `GDist β`: Endows a space `β` with a function `gdist β x y`.
- `GPseudoMetricSpace α β`: A space `α` endowed with a generic distance function with codomain `β`,
which may be equal to 0 for non-equal elements. the distance function is 0 for equal elements,
is commutative in its arguments, and satisifies the triangle inequality.

Additional useful definitions:

- `ball x δ`: the set of points with distance to x strictly less than δ
- `closedBall x δ`: the set of points with distance to x less than or equal to δ

## Implementation notes

Although `GDist α β` has a field `gdist : α → α → β`, in typical usecases lean has a hard time
inferring the intended return type without type annotations.
Because of this, the field is set as protected, and a function
`gdist (β :Type*) ... : α → α → β` is shadowing the name of the field.
-/

open Set Filter Bornology
open scoped BigOperators

/-- Construct a bornology from a generic distance function and metric space axioms.
this is not declared as an instance, as it would lead to multiple instances of bornology on α,
as well as a free type variable when trying to infer the instance. -/
@[reducible]
def Bornology.ofGDist {α : Type*} {β : Type*} [LinearOrder β] [AddCommMonoid β]
    [IsOrderedAddCommMonoid β] (gdist : α → α → β) (gdist_comm : ∀ x y, gdist x y = gdist y x)
    (gdist_triangle : ∀ x y z, gdist x z ≤ gdist x y + gdist y z) : Bornology α :=
  Bornology.ofBounded { s : Set α | ∃ C, ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → gdist x y ≤ C }
    ⟨0,fun x hx y => hx.elim⟩
    (fun s ⟨c, hc⟩ t h => ⟨c, fun x hx y hy => hc (h hx) (h hy)⟩)
    (fun s hs t ht => by
      rcases s.eq_empty_or_nonempty with rfl | ⟨x, hx⟩
      · rwa [empty_union]
      rcases t.eq_empty_or_nonempty with rfl | ⟨y, hy⟩
      · rwa [union_empty]
      rsuffices ⟨C, hC⟩ : ∃ C, ∀ z ∈ s ∪ t, gdist x z ≤ C
      · refine ⟨C + C, fun a ha b hb => (gdist_triangle a x b).trans ?_⟩
        simpa only [gdist_comm] using add_le_add (hC _ ha) (hC _ hb)
      rcases hs with ⟨Cs, hs⟩; rcases ht with ⟨Ct, ht⟩
      refine ⟨max Cs (gdist x y + Ct), fun z hz => hz.elim
        (fun hz => (hs hx hz).trans (le_max_left _ _))
        (fun hz => (gdist_triangle x y z).trans <|
          (add_le_add le_rfl (ht hy hz)).trans (le_max_right _ _))⟩)
    fun z => ⟨gdist z z, forall_eq.2 <| forall_eq.2 le_rfl⟩

/-- the class of spaces α with a generic distance function on which return an element of type β -/
@[ext]
class GDist
    (α : Type*) (β : Type*) [LinearOrder β] [AddCommMonoid β] [IsOrderedAddCommMonoid β] where
  /-- the generic distance function on α to β -/
  protected gdist : α → α → β

/-- the generic distance function on a space α which returns an element of type β,
with an explicit type parameter β for ease of inferring the return type-/
def gdist (β : Type*) [LinearOrder β] [AddCommMonoid β] [IsOrderedAddCommMonoid β]
    {α :Type*} [GDist α β] :α → α → β :=
  GDist.gdist

export GDist (gdist)

variable {α : Type*} {β : Type*}
private theorem gdist_nonneg' [LinearOrder β] [AddCommMonoid β] [IsOrderedAddCommMonoid β] {x y : α}
    (gdist : α → α → β) (gdist_self : ∀ x : α, gdist x x = 0)
    (gdist_comm : ∀ x y : α, gdist x y = gdist y x)
    (gdist_triangle : ∀ x y z : α, gdist x z ≤ gdist x y + gdist y z) : 0 ≤ gdist x y := by
  have : 0 ≤ gdist x y + gdist x y :=
    calc 0 = gdist x x := (gdist_self _).symm
    _ ≤ gdist x y + gdist y x := gdist_triangle _ _ _
    _ = gdist x y + gdist x y:= by rw [gdist_comm]
  exact nonneg_add_self_iff.mp this

/-- generic Pseudo-metric spaces
a generic Pseudo metric space is a space endowed with some distance function `gdist : α → α → β`
which is zero for identical elements, for which the arguments commute, and for which the triangle
inequality holds. As opposed to a classical pseudo metric space, the codomain of this distance
function is not necessarily ℝ (or ℝ≥0∞), and as a result does not endow the space with a uniform
space.
-/
class GPseudoMetricSpace
    (α : Type*) (β : Type*) [LinearOrder β] [AddCommMonoid β] [IsOrderedAddCommMonoid β]
    extends GDist α β where
  gdist_self : ∀ x : α, gdist x x = 0
  gdist_comm : ∀ x y : α, gdist x y = gdist y x
  gdist_triangle : ∀ x y z : α, gdist x z ≤ gdist x y + gdist y z

lemma cobounded_sets [LinearOrder β] [AddCommMonoid β] [IsOrderedAddCommMonoid β]
    (gdist : α → α → β)
    (gdist_comm : ∀ x y, gdist x y = gdist y x)
    (gdist_triangle : ∀ x y z, gdist x z ≤ gdist x y + gdist y z):
    (@Bornology.cobounded α (Bornology.ofGDist (gdist) gdist_comm gdist_triangle)
    ).sets =
    { (s:Set α) | ∃ (C : β), ∀ x ∈ sᶜ, ∀ y ∈ sᶜ, (gdist x y ≤ C) } :=
  by intros; rfl

@[ext]
theorem GPseudoMetricSpace.ext [LinearOrder β] [AddCommMonoid β] [IsOrderedAddCommMonoid β]
    {m m' : GPseudoMetricSpace α β} (h : m.toGDist = m'.toGDist) : m = m' := by
  cases' m with d _ _ _ B hB
  cases' m' with d' _ _ _ B' hB'
  obtain rfl : d = d' := h
  congr

section
variable [LinearOrder β] [AddCommMonoid β] [IsOrderedAddCommMonoid β] [GPseudoMetricSpace α β]

@[simp]
theorem gdist_self (x : α) : gdist β x x = 0 :=
  GPseudoMetricSpace.gdist_self x

theorem gdist_comm (x y : α) : gdist β x y = gdist β y x :=
  GPseudoMetricSpace.gdist_comm x y

theorem gdist_triangle (x y z : α) : gdist β x z ≤ gdist β x y + gdist β y z:=
  GPseudoMetricSpace.gdist_triangle x y z

theorem gdist_triangle_left (x y z : α) : gdist β x y ≤ gdist β z x + gdist β z y := by
  rw [gdist_comm z]; apply gdist_triangle

theorem gdist_triangle_right (x y z : α) : gdist β x y ≤ gdist β x z + gdist β y z := by
  rw [gdist_comm y]; apply gdist_triangle

theorem gdist_triangle4 (x y z w : α) : gdist β x w ≤ gdist β x y + gdist β y z + gdist β z w :=
  calc
    gdist β x w ≤ gdist β x z + gdist β z w := gdist_triangle x z w
    _ ≤ (gdist β x y + gdist β y z + gdist β z w:β) := add_le_add_right (gdist_triangle x y z) _

theorem gdist_triangle4_left (x₁ y₁ x₂ y₂ : α) :
    gdist β x₂ y₂ ≤ gdist β x₁ y₁ + (gdist β x₁ x₂ + gdist β y₁ y₂) := by
  rw [add_left_comm, gdist_comm x₁, ← add_assoc]
  apply gdist_triangle4

theorem gdist_triangle4_right (x₁ y₁ x₂ y₂ : α) :
    gdist β x₁ y₁ ≤ gdist β x₁ x₂ + gdist β y₁ y₂ + gdist β x₂ y₂ := by
  rw [add_right_comm, gdist_comm y₁]
  apply gdist_triangle4

/-- The triangle (polygon) inequality for sequences of points; `Finset.Ico` version. -/
theorem gdist_le_Ico_sum_dist (f : ℕ → α) {m n} (h : m ≤ n) :
    gdist β (f m) (f n) ≤ ∑ i in Finset.Ico m n, gdist β (f i) (f (i + 1)) := by
  induction n, h using Nat.le_induction with
  | base => rw [Finset.Ico_self, Finset.sum_empty, gdist_self]
  | succ n hle ihn =>
    calc
      gdist β (f m) (f (n + 1)) ≤ gdist β (f m) (f n) + gdist β (f n) (f (n + 1)) :=
        gdist_triangle _ _ _
      _ ≤ (∑ i in Finset.Ico m n, _) + _ := add_le_add ihn le_rfl
      _ = ∑ i in Finset.Ico m (n + 1), _ := by
      { rw [Nat.Ico_succ_right_eq_insert_Ico hle, Finset.sum_insert, add_comm]; simp }

/-- The triangle (polygon) inequality for sequences of points; `Finset.range` version. -/
theorem gdist_le_range_sum_dist (f : ℕ → α) (n : ℕ) :
    gdist β (f 0) (f n) ≤ ∑ i in Finset.range n, gdist β (f i) (f (i + 1)) :=
  Nat.Ico_zero_eq_range ▸ gdist_le_Ico_sum_dist f (Nat.zero_le n)

/-- A version of `gdist_le_Ico_sum_dist` with each intermediate distance replaced
with an upper estimate. -/
theorem gdist_le_Ico_sum_of_dist_le {f : ℕ → α} {m n} (hmn : m ≤ n) {d : ℕ → β}
    (hd : ∀ {k}, m ≤ k → k < n → gdist β (f k) (f (k + 1)) ≤ d k) :
    gdist β (f m) (f n) ≤ ∑ i in Finset.Ico m n, d i :=
  le_trans (gdist_le_Ico_sum_dist f hmn) <|
    Finset.sum_le_sum fun _k hk => hd (Finset.mem_Ico.1 hk).1 (Finset.mem_Ico.1 hk).2

/-- A version of `gdist_le_range_sum_dist` with each intermediate distance replaced
with an upper estimate. -/
theorem gdist_le_range_sum_of_dist_le {f : ℕ → α} (n : ℕ) {d : ℕ → β}
    (hd : ∀ {k}, k < n → gdist β (f k) (f (k + 1)) ≤ d k) :
    gdist β (f 0) (f n) ≤ ∑ i in Finset.range n, d i :=
  Nat.Ico_zero_eq_range ▸ gdist_le_Ico_sum_of_dist_le (zero_le n) fun _ => hd

theorem swap_gdist : Function.swap (gdist β) = (gdist β:α → α → β) := by
  funext x y; exact gdist_comm _ _

theorem gdist_nonneg {x y : α} : 0 ≤ (gdist β x y) :=
  gdist_nonneg' (gdist β) gdist_self gdist_comm gdist_triangle
end


namespace GMetricSpace
section non_cancel
variable [LinearOrder β] [AddCommMonoid β] [IsOrderedAddCommMonoid β] [GPseudoMetricSpace α β]
variable {x y z : α} {δ ε ε₁ ε₂ : β} {s : Set α}

/-- `ball x ε` is the set of all points `y` with `dist y x < ε` -/
def ball (x : α) (ε : β) : Set α :=
  { y | gdist β y x < ε }

@[simp]
theorem mem_ball : y ∈ ball x ε ↔ gdist β y x < ε :=
  Iff.rfl

theorem mem_ball' : y ∈ ball x ε ↔ gdist β x y < ε := by rw [gdist_comm, mem_ball]

theorem pos_of_mem_ball (hy : y ∈ ball x ε) : 0 < ε :=
  gdist_nonneg.trans_lt hy

theorem mem_ball_self (h : 0 < ε) : x ∈ ball x ε := by
  rwa [mem_ball, gdist_self]

@[simp]
theorem nonempty_ball : (ball x ε).Nonempty ↔ 0 < ε :=
  ⟨fun ⟨_x, hx⟩ => pos_of_mem_ball hx, fun h => ⟨x, mem_ball_self h⟩⟩

@[simp]
theorem ball_eq_empty : ball x ε = ∅ ↔ ε ≤ 0 := by
  rw [← not_nonempty_iff_eq_empty, nonempty_ball, not_lt]

@[simp]
theorem ball_zero : ball x (0:β) = ∅ := by rw [ball_eq_empty]

/-- `closedBall x ε` is the set of all points `y` with `dist y x ≤ ε` -/
def closedBall (x : α) (ε : β) :=
  { y | gdist β y x ≤ ε }

@[simp] theorem mem_closedBall : y ∈ closedBall x ε ↔ gdist β y x ≤ ε := Iff.rfl

theorem mem_closedBall' : y ∈ closedBall x ε ↔ gdist β x y ≤ ε := by rw [gdist_comm, mem_closedBall]

/-- `sphere x ε` is the set of all points `y` with `dist y x = ε` -/
def sphere (x : α) (ε : β) := { y | gdist β y x = ε }

@[simp] theorem mem_sphere : y ∈ sphere x ε ↔ gdist β y x = ε := Iff.rfl

theorem mem_sphere' : y ∈ sphere x ε ↔ gdist β x y = ε := by rw [gdist_comm, mem_sphere]

theorem ne_of_mem_sphere (h : y ∈ sphere x ε) (hε : ε ≠ 0) : y ≠ x :=
  ne_of_mem_of_not_mem h <| by simpa using hε.symm

theorem nonneg_of_mem_sphere (hy : y ∈ sphere x ε) : 0 ≤ ε :=
  gdist_nonneg.trans_eq hy

@[simp]
theorem sphere_eq_empty_of_neg (hε : ε < 0) : sphere x ε = ∅ :=
  Set.eq_empty_iff_forall_not_mem.mpr fun _y hy => (nonneg_of_mem_sphere hy).not_lt hε

theorem sphere_eq_empty_of_subsingleton [Subsingleton α] (hε : ε ≠ 0) : sphere x ε = ∅ :=
  Set.eq_empty_iff_forall_not_mem.mpr fun _ h => ne_of_mem_sphere h hε (Subsingleton.elim _ _)

instance sphere_isEmpty_of_subsingleton [Subsingleton α] [NeZero ε] : IsEmpty (sphere x ε) := by
  rw [sphere_eq_empty_of_subsingleton (NeZero.ne ε)]; infer_instance

theorem mem_closedBall_self (h : 0 ≤ ε) : x ∈ closedBall x ε := by
  rwa [mem_closedBall, gdist_self]

@[simp]
theorem nonempty_closedBall : (closedBall x ε).Nonempty ↔ 0 ≤ ε :=
  ⟨fun ⟨_x, hx⟩ => gdist_nonneg.trans hx, fun h => ⟨x, mem_closedBall_self h⟩⟩

@[simp]
theorem closedBall_eq_empty : closedBall x ε = ∅ ↔ ε < 0 := by
  rw [← not_nonempty_iff_eq_empty, nonempty_closedBall, not_le]

/-- Closed balls and spheres coincide when the radius is non-positive -/
theorem closedBall_eq_sphere_of_nonpos (hε : ε ≤ 0) : closedBall x ε = sphere x ε :=
  Set.ext fun _ => (hε.trans gdist_nonneg).le_iff_eq

theorem ball_subset_closedBall : ball x ε ⊆ closedBall x ε := fun _y hy =>
  mem_closedBall.2 (le_of_lt hy)

theorem sphere_subset_closedBall : sphere x ε ⊆ closedBall x ε := fun _ => le_of_eq

lemma sphere_subset_ball {r R : β} (h : r < R) : sphere x r ⊆ ball x R := fun _x hx ↦
  (mem_sphere.1 hx).trans_lt h

end non_cancel


section cancel
variable [LinearOrder β] [AddCommMonoid β] [IsOrderedCancelAddCommMonoid β] [GPseudoMetricSpace α β]
variable {x y z : α} {δ ε ε₁ ε₂ : β} {s : Set α}

theorem closedBall_disjoint_ball (h : δ + ε ≤ gdist β x y) : Disjoint (closedBall x δ) (ball y ε) :=
  Set.disjoint_left.mpr fun _a ha1 ha2 =>
    (h.trans <| gdist_triangle_left _ _ _).not_lt <| add_lt_add_of_le_of_lt ha1 ha2

theorem ball_disjoint_closedBall
    (h : δ + ε ≤ gdist β x y) : Disjoint (ball x δ) (closedBall (y:α) (ε :β)) :=
  (closedBall_disjoint_ball <| by rwa [add_comm, gdist_comm]).symm

theorem ball_disjoint_ball (h : δ + ε ≤ gdist β x y) : Disjoint (ball x δ) (ball y ε) :=
  (closedBall_disjoint_ball h).mono_left ball_subset_closedBall

theorem closedBall_disjoint_closedBall (h : δ + ε < gdist β x y) :
    Disjoint (closedBall x δ) (closedBall y ε) :=
  Set.disjoint_left.mpr fun _a ha1 ha2 =>
    h.not_le <| (gdist_triangle_left _ _ _).trans <| add_le_add ha1 ha2

theorem sphere_disjoint_ball : Disjoint (sphere x ε) (ball x ε) :=
  Set.disjoint_left.mpr fun _y hy₁ hy₂ => absurd hy₁ <| ne_of_lt hy₂

@[simp]
theorem ball_union_sphere : ball x ε ∪ sphere x ε = closedBall x ε :=
  Set.ext fun _y => (@le_iff_lt_or_eq β _ _ _).symm

@[simp]
theorem sphere_union_ball : sphere x ε ∪ ball x ε = closedBall x ε := by
  rw [union_comm, ball_union_sphere]

@[simp]
theorem closedBall_diff_sphere : closedBall x ε \ sphere x ε = ball x ε := by
  rw [← ball_union_sphere, Set.union_diff_cancel_right sphere_disjoint_ball.symm.le_bot]

@[simp]
theorem closedBall_diff_ball : closedBall x ε \ ball x ε = sphere x ε := by
  rw [← ball_union_sphere, Set.union_diff_cancel_left sphere_disjoint_ball.symm.le_bot]

theorem mem_ball_comm : x ∈ ball y ε ↔ y ∈ ball x ε := by rw [mem_ball', mem_ball]

theorem mem_closedBall_comm : x ∈ closedBall y ε ↔ y ∈ closedBall x ε := by
  rw [mem_closedBall', mem_closedBall]

theorem mem_sphere_comm : x ∈ sphere y ε ↔ y ∈ sphere x ε := by rw [mem_sphere', mem_sphere]

theorem ball_subset_ball (h : ε₁ ≤ ε₂) : ball x ε₁ ⊆ ball x ε₂ := fun _y yx =>
  lt_of_lt_of_le (mem_ball.1 yx) h

theorem closedBall_eq_bInter_ball : closedBall x ε = ⋂ δ > ε, ball x δ := by
  ext y; rw [mem_closedBall, ← forall_lt_iff_le', mem_iInter₂]; rfl

theorem ball_subset_ball' (h : ε₁ + gdist β x y ≤ ε₂) : ball x ε₁ ⊆ ball y ε₂ := fun z hz =>
  calc
   gdist β z y ≤ gdist β z x + gdist β x y := by apply gdist_triangle
    _ < ε₁ + gdist β x y := by exact add_lt_add_right hz _
    _ ≤ ε₂ := h

theorem closedBall_subset_closedBall (h : ε₁ ≤ ε₂) : closedBall x ε₁ ⊆ closedBall x ε₂ :=
  fun _y (yx : _ ≤ ε₁) => le_trans yx h

theorem closedBall_subset_closedBall' (h : ε₁ + gdist β x y ≤ ε₂) :
    closedBall x ε₁ ⊆ closedBall y ε₂ := fun z hz =>
  calc
    gdist β z y ≤ gdist β z x + gdist β x y := gdist_triangle _ _ _
    _ ≤ ε₁ + gdist β x y := add_le_add_right (mem_closedBall.1 hz) _
    _ ≤ ε₂ := h

theorem closedBall_subset_ball (h : ε₁ < ε₂) : closedBall x ε₁ ⊆ ball x ε₂ :=
  fun y (yh : gdist β y x ≤ ε₁) => lt_of_le_of_lt yh h

theorem closedBall_subset_ball' (h : ε₁ + gdist β x y < ε₂) :
    closedBall x ε₁ ⊆ ball y ε₂ := fun z hz =>
  calc
    gdist β z y ≤ gdist β z x + gdist β x y := gdist_triangle _ _ _
    _ ≤ ε₁ + gdist β x y := add_le_add_right (mem_closedBall.1 hz) _
    _ < ε₂ := h

theorem dist_le_add_of_nonempty_closedBall_inter_closedBall
    (h : (closedBall x ε₁ ∩ closedBall y ε₂).Nonempty) : gdist β x y ≤ ε₁ + ε₂ :=
  let ⟨z, hz⟩ := h
  calc
    gdist β x y ≤ gdist β z x + gdist β z y := gdist_triangle_left _ _ _
    _ ≤ ε₁ + ε₂ := add_le_add hz.1 hz.2

theorem dist_lt_add_of_nonempty_closedBall_inter_ball (h : (closedBall x ε₁ ∩ ball y ε₂).Nonempty) :
    gdist β x y < ε₁ + ε₂ :=
  let ⟨z, hz⟩ := h
  calc
    gdist β x y ≤ gdist β z x + gdist β z y := gdist_triangle_left _ _ _
    _ < ε₁ + ε₂ := add_lt_add_of_le_of_lt hz.1 hz.2

theorem dist_lt_add_of_nonempty_ball_inter_closedBall (h : (ball x ε₁ ∩ closedBall y ε₂).Nonempty) :
    gdist β x y < ε₁ + ε₂ := by
  rw [inter_comm] at h
  rw [add_comm, gdist_comm]
  exact dist_lt_add_of_nonempty_closedBall_inter_ball h

theorem dist_lt_add_of_nonempty_ball_inter_ball (h : (ball x ε₁ ∩ ball y ε₂).Nonempty) :
    gdist β x y < ε₁ + ε₂ :=
  dist_lt_add_of_nonempty_closedBall_inter_ball <|
    h.mono (inter_subset_inter ball_subset_closedBall Subset.rfl)
