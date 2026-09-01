/-
Copyright (c) 2026 Hang Lu Su, Justus Springer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hang Lu Su, Justus Springer
-/
module

public import Mathlib.Algebra.Group.Pointwise.Set.Basic
public import Mathlib.Data.ENat.Lattice
public import Mathlib.Data.Set.Finite.List
public import Mathlib.GroupTheory.FreeGroup.Reduce
public import Mathlib.GroupTheory.Presentation

/-!
# Dehn functions

For a presentation `P` of a group `G` and a word `w : FreeGroup α` that evaluates to
the identity in `G`, the *area* of `w` is the least number of conjugates of relators and of
inverse relators whose product is `w`. The *Dehn function* of `P` is given by
`n ↦ max {area w | w = 1 in G, ‖w‖ ≤ n}`, where `‖w‖` is the length of `w`.

## Main definitions

* `Group.Presentation.IsConjRelDecomp P w l`:
* `Group.Presentation.area`:
* `Group.Presentation.kerBall`:
* `Group.Presentation.dehn`:

## Main results

* `Group.Presentation.area_ne_top_iff` and `Group.Presentation.area_eq_top_iff`: the area of `w` is
  finite exactly when `w` evaluates to the identity in `G`.
* `Group.Presentation.area_mul_le`, `Group.Presentation.area_inv` and
  `Group.Presentation.area_conj`: area is subadditive, and invariant under inversion and
  conjugation.
* `Group.Presentation.area_le_dehn` and `Group.Presentation.dehn_le_iff`: `P.dehn` is the least
  isoperimetric function of `P`.

## Design notes

* The factors of the product range over `Group.conjugatesOfSet P.symmRel`, the conjugates of
  relators *and* of inverse relators. Both signs are needed: the conjugates of `P.rel` alone
  generate only a submonoid, whereas the products must realise every element of the kernel
  `Subgroup.normalClosure P.rel`, a subgroup.
* `area` takes values in `ℕ∞`; it is `⊤` exactly when `w` does not evaluate to the identity in `G`
  (there is then no product of conjugates equal to `w`), and finite otherwise. This mirrors
  `SimpleGraph.edist`, and keeps `area w = 0 ↔ w = 1` rather than colliding with the junk value.
* `FreeGroup.norm` needs `[DecidableEq α]`, so `kerBall` and `dehn` do too.

## Tags

Dehn function
-/

@[expose] public section

open scoped Pointwise

-- TODO: this belongs next to `FreeGroup.norm` in `Mathlib/GroupTheory/FreeGroup/Reduce.lean`;
-- it lives here only to avoid adding `Mathlib.Data.Set.Finite.List` to that file's imports.
/-- Over a finite alphabet there are only finitely many elements of norm at most `n`, since
distinct elements have distinct reduced words. -/
lemma FreeGroup.finite_setOf_norm_le (α : Type*) [DecidableEq α] [Finite α] (n : ℕ) :
    {w : FreeGroup α | FreeGroup.norm w ≤ n}.Finite :=
  Set.Finite.of_finite_image
    ((List.finite_length_le (α × Bool) n).subset (by rintro _ ⟨w, hw, rfl⟩; exact hw))
    FreeGroup.toWord_injective.injOn

variable {G α : Type*} [Group G]

namespace Group.Presentation

variable (P : Group.Presentation G α)

/-- A list `l` of elements of the free group is a decomposition of `w` into conjugates of relators
of `P` if every entry of `l` is a conjugate of a relator or of an inverse relator, and the product
of `l` is `w`. -/
structure IsConjRelDecomp (w : FreeGroup α) (l : List (FreeGroup α)) : Prop where
  mem_conjugatesOfSet : ∀ x ∈ l, x ∈ Group.conjugatesOfSet P.symmRel
  prod_eq : l.prod = w

attribute [simp] IsConjRelDecomp.prod_eq

lemma isConjRelDecomp_one_nil : P.IsConjRelDecomp (1 : FreeGroup α) [] where
  mem_conjugatesOfSet := by simp
  prod_eq := by simp

/-- A conjugate of a relator or of an inverse relator is a one-term decomposition of itself. -/
lemma isConjRelDecomp_singleton {x : FreeGroup α} (hx : x ∈ Group.conjugatesOfSet P.symmRel) :
    P.IsConjRelDecomp x [x] where
  mem_conjugatesOfSet := by simpa using hx
  prod_eq := by simp

/-- Concatenating decompositions of `w₁` and of `w₂` decomposes `w₁ * w₂`. -/
lemma IsConjRelDecomp.append {w₁ w₂ : FreeGroup α} {l₁ l₂ : List (FreeGroup α)}
    (h₁ : P.IsConjRelDecomp w₁ l₁) (h₂ : P.IsConjRelDecomp w₂ l₂) :
    P.IsConjRelDecomp (w₁ * w₂) (l₁ ++ l₂) where
  mem_conjugatesOfSet x hx := by
    rcases List.mem_append.mp hx with h | h
    exacts [h₁.mem_conjugatesOfSet x h, h₂.mem_conjugatesOfSet x h]
  prod_eq := by simp [h₁.prod_eq, h₂.prod_eq]

/-- Reversing a decomposition of `w` and inverting its entries decomposes `w⁻¹`. -/
lemma IsConjRelDecomp.inv {w : FreeGroup α} {l : List (FreeGroup α)}
    (h : P.IsConjRelDecomp w l) : P.IsConjRelDecomp w⁻¹ (l.map (·⁻¹)).reverse where
  mem_conjugatesOfSet x hx := by
    simp only [List.mem_reverse, List.mem_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact P.inv_mem_conjugatesOfSet_symmRel (h.mem_conjugatesOfSet y hy)
  prod_eq := by rw [← List.prod_inv_reverse, h.prod_eq]

/-- Conjugating a decomposition of `w` entrywise decomposes the conjugate `u * w * u⁻¹`. -/
lemma IsConjRelDecomp.conj {w : FreeGroup α} {l : List (FreeGroup α)}
    (h : P.IsConjRelDecomp w l) (u : FreeGroup α) :
    P.IsConjRelDecomp (u * w * u⁻¹) (l.map (u * · * u⁻¹)) where
  mem_conjugatesOfSet x hx := by
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    exact Group.conj_mem_conjugatesOfSet (h.mem_conjugatesOfSet y hy)
  prod_eq := by
    rw [← h.prod_eq]
    exact List.prod_hom l (MulAut.conj u)

/-- The area of a word `w` over the presentation `P` is the least length of a decomposition
`l` of `w` into conjugates of elements of the symmetric relator set. It is valued in `ℕ∞`
so that it returns a finite number when `l` exists, and the junk value `⊤` when `w` is not the
identity of `G`, since then no such decomposition exists and the infimum is taken over
the empty set. -/
noncomputable def area (w : FreeGroup α) : ℕ∞ :=
  sInf ((fun l : List (FreeGroup α) ↦ (l.length)) '' {l | P.IsConjRelDecomp w l})

variable {w : FreeGroup α} {l : List (FreeGroup α)} {n : ℕ}

/-- The area  of `w` is less or equal than the length of a conjugate decomposition. -/
lemma IsConjRelDecomp.area_le (h : P.IsConjRelDecomp w l) : P.area w ≤ l.length :=
  sInf_le ⟨l, h, rfl⟩

/-- A word admitting a decomposition into conjugates of relators evaluates to the identity in
`G`. -/
lemma IsConjRelDecomp.lift_eq_one (h : P.IsConjRelDecomp w l) : P.lift w = 1 := by
  obtain ⟨hmem, rfl⟩ := h
  rw [← List.prod_hom l P.lift]
  refine List.prod_eq_one fun x hx => ?_
  obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
  exact P.lift_eq_one_of_mem_conjugatesOfSet_symmRel (hmem y hy)

/-- The infimum defining the area is attained: a word of finite area admits a decomposition into
conjugates of relators whose length is exactly its area. -/
lemma exists_isConjRelDecomp_length_eq_area (h : P.area w ≠ ⊤) :
    ∃ l, P.IsConjRelDecomp w l ∧ (l.length : ℕ∞) = P.area w := by
  have hne : ((fun l : List (FreeGroup α) ↦ (l.length : ℕ∞)) ''
      {l | P.IsConjRelDecomp w l}).Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    rintro he
    exact h (by rw [area, he, sInf_empty])
  exact csInf_mem hne

@[simp]
lemma area_one_eq_zero : P.area (1 : FreeGroup α) = 0 := by
  simpa using IsConjRelDecomp.area_le P (isConjRelDecomp_one_nil P)

lemma area_eq_zero_iff : P.area w = 0 ↔ w = (1 : FreeGroup α) := by
  constructor
  · intro h
    have hne : P.area w ≠ ⊤ := by simp [h]
    obtain ⟨l, hl, hlen⟩ := P.exists_isConjRelDecomp_length_eq_area hne
    rw [h, Nat.cast_eq_zero, List.length_eq_zero_iff] at hlen
    rw [← hl.prod_eq, hlen, List.prod_nil]
  · rintro rfl
    simp

/-- A word is a product of conjugates of relators and inverse relators exactly when it evaluates to
the identity in `G`. -/
lemma exists_isConjRelDecomp_iff_mem_ker :
    (∃ l, P.IsConjRelDecomp w l) ↔ w ∈ P.lift.ker := by
  refine ⟨fun ⟨l, hl⟩ => hl.lift_eq_one, fun hw => ?_⟩
  rw [P.ker_lift, Subgroup.normalClosure, ← Subgroup.mem_toSubmonoid,
    Subgroup.closure_toSubmonoid] at hw
  obtain ⟨l, hmem, rfl⟩ := Submonoid.exists_list_of_mem_closure hw
  refine ⟨l, fun x hx => ?_, rfl⟩
  have hsub := Group.conjugatesOfSet_mono P.rel_subset_symmRel
  rcases hmem x hx with h | h
  · exact hsub h
  · simpa using P.inv_mem_conjugatesOfSet_symmRel (hsub (Set.mem_inv.mp h))

/-- A word has finite area exactly when it evaluates to the identity in `G`. -/
theorem area_ne_top_iff : P.area w ≠ ⊤ ↔ w ∈ P.lift.ker := by
  rw [← P.exists_isConjRelDecomp_iff_mem_ker]
  refine ⟨fun h => ?_, fun ⟨l, hl⟩ => (hl.area_le.trans_lt (by simp)).ne⟩
  by_contra hw
  have hempty : {l : List (FreeGroup α) | P.IsConjRelDecomp w l} = ∅ :=
    Set.eq_empty_iff_forall_notMem.2 fun l hl => hw ⟨l, hl⟩
  exact h (by rw [area, hempty, Set.image_empty, sInf_empty])

/-- A word has infinite area exactly when it does not evaluate to the identity in `G`. -/
lemma area_eq_top_iff : P.area w = ⊤ ↔ w ∉ P.lift.ker := by
  rw [← P.area_ne_top_iff, not_not]

/-- `area` as an infimum over the decompositions of `w`, rather than over their lengths. -/
lemma area_eq_iInf (w : FreeGroup α) :
    P.area w = ⨅ l ∈ {l : List (FreeGroup α) | P.IsConjRelDecomp w l}, (l.length : ℕ∞) :=
  sInf_image

/-- A conjugate of a relator or of an inverse relator has area at most one. -/
lemma area_le_one_of_mem_conjugatesOfSet_symmRel {x : FreeGroup α}
    (hx : x ∈ Group.conjugatesOfSet P.symmRel) : P.area x ≤ 1 := by
  simpa using (P.isConjRelDecomp_singleton hx).area_le

/-- A relator or inverse relator has area at most one. -/
lemma area_le_one_of_mem_symmRel {x : FreeGroup α} (hx : x ∈ P.symmRel) : P.area x ≤ 1 :=
  P.area_le_one_of_mem_conjugatesOfSet_symmRel (Group.subset_conjugatesOfSet hx)

/-- Every relator has area at most one. -/
lemma area_le_one_of_mem_rel {x : FreeGroup α} (hx : x ∈ P.rel) : P.area x ≤ 1 :=
  P.area_le_one_of_mem_symmRel (P.rel_subset_symmRel hx)

/-- Area is subadditive: concatenating decompositions of `w₁` and of `w₂` decomposes `w₁ * w₂`. -/
lemma area_mul_le (w₁ w₂ : FreeGroup α) : P.area (w₁ * w₂) ≤ P.area w₁ + P.area w₂ := by
  rw [P.area_eq_iInf w₁, P.area_eq_iInf w₂]
  refine ENat.le_iInf₂_add_iInf₂ fun l₁ hl₁ l₂ hl₂ ↦ ?_
  exact (IsConjRelDecomp.append P hl₁ hl₂).area_le.trans (by simp)

lemma area_inv_le (w : FreeGroup α) : P.area w⁻¹ ≤ P.area w := by
  rw [P.area_eq_iInf w]
  refine le_iInf₂ fun l hl ↦ ?_
  simpa using (IsConjRelDecomp.inv P hl).area_le

/-- Area is invariant under inversion. -/
@[simp]
lemma area_inv (w : FreeGroup α) : P.area w⁻¹ = P.area w :=
  le_antisymm (P.area_inv_le w) (by simpa using P.area_inv_le w⁻¹)

lemma area_conj_le (u w : FreeGroup α) : P.area (u * w * u⁻¹) ≤ P.area w := by
  rw [P.area_eq_iInf w]
  refine le_iInf₂ fun l hl ↦ ?_
  simpa using (IsConjRelDecomp.conj P hl u).area_le

/-- Area is invariant under conjugation. -/
@[simp]
lemma area_conj (u w : FreeGroup α) : P.area (u * w * u⁻¹) = P.area w := by
  refine le_antisymm (P.area_conj_le u w) ?_
  have h := P.area_conj_le u⁻¹ (u * w * u⁻¹)
  rwa [show u⁻¹ * (u * w * u⁻¹) * u⁻¹⁻¹ = w by group] at h

section Dehn

variable [DecidableEq α]

/-- The set of words of length at most `n` that evaluate to the identity in `G`. -/
def kerBall (n : ℕ) : Set (FreeGroup α) := {w | w ∈ P.lift.ker ∧ FreeGroup.norm w ≤ n}

/-- The Dehn function of a presentation: `P.dehn n` is the largest area of a word of length at most
`n` that evaluates to the identity in `G`. Equivalently, it is the least isoperimetric function
of `P`.

This is junk unless the generating set is finite; the relevant lemmas assume `[Finite α]`. The
areas involved are all finite (the words evaluate to the identity in `G`), so truncating the
`ℕ∞`-valued supremum back to `ℕ` with `ENat.toNat` loses nothing. -/
noncomputable def dehn (n : ℕ) : ℕ := (sSup (P.area '' P.kerBall n)).toNat

@[simp]
lemma mem_kerBall : w ∈ P.kerBall n ↔ w ∈ P.lift.ker ∧ FreeGroup.norm w ≤ n := Iff.rfl

lemma kerBall_subset_ker (n : ℕ) : P.kerBall n ⊆ P.lift.ker := fun _ hw ↦ hw.1

lemma kerBall_mono : Monotone P.kerBall := fun _ _ hmn _ hw ↦ ⟨hw.1, hw.2.trans hmn⟩

@[simp]
lemma one_mem_kerBall (n : ℕ) : (1 : FreeGroup α) ∈ P.kerBall n := ⟨one_mem _, by simp⟩

lemma kerBall_nonempty (n : ℕ) : (P.kerBall n).Nonempty := ⟨1, P.one_mem_kerBall n⟩

@[simp]
lemma kerBall_zero : P.kerBall 0 = {1} := by
  ext w
  simp only [mem_kerBall, Nat.le_zero, FreeGroup.norm_eq_zero, Set.mem_singleton_iff]
  exact ⟨And.right, fun hw ↦ ⟨hw ▸ one_mem _, hw⟩⟩

/-- A word evaluating to the identity in `G` lies in the ball of radius its own length. -/
lemma mem_kerBall_norm (hw : w ∈ P.lift.ker) : w ∈ P.kerBall (FreeGroup.norm w) := ⟨hw, le_rfl⟩

lemma inv_mem_kerBall (hw : w ∈ P.kerBall n) : w⁻¹ ∈ P.kerBall n :=
  ⟨inv_mem hw.1, by simpa [FreeGroup.norm_inv_eq] using hw.2⟩

lemma mul_mem_kerBall {m : ℕ} {w₁ w₂ : FreeGroup α} (h₁ : w₁ ∈ P.kerBall m)
    (h₂ : w₂ ∈ P.kerBall n) : w₁ * w₂ ∈ P.kerBall (m + n) :=
  ⟨mul_mem h₁.1 h₂.1, (FreeGroup.norm_mul_le w₁ w₂).trans (Nat.add_le_add h₁.2 h₂.2)⟩

lemma area_ne_top_of_mem_kerBall (hw : w ∈ P.kerBall n) : P.area w ≠ ⊤ :=
  P.area_ne_top_iff.mpr hw.1

/-- Over a finite generating set there are only finitely many words of length at most `n`, so the
ball `P.kerBall n` is finite. -/
lemma kerBall_finite [Finite α] (n : ℕ) : (P.kerBall n).Finite :=
  (FreeGroup.finite_setOf_norm_le α n).subset fun _ hw ↦ hw.2

/-- Over a finite generating set the supremum defining `P.dehn n` is finite: the ball is finite
and each of its words has finite area. -/
lemma sSup_area_image_kerBall_ne_top [Finite α] (n : ℕ) : sSup (P.area '' P.kerBall n) ≠ ⊤ := by
  obtain ⟨w, hw, hwa⟩ :=
    ((P.kerBall_nonempty n).image P.area).csSup_mem ((P.kerBall_finite n).image P.area)
  exact hwa ▸ P.area_ne_top_of_mem_kerBall hw

/-- Over a finite generating set, `P.dehn n` is the `ℕ∞`-valued supremum of the areas: nothing is
lost by truncating with `ENat.toNat`. -/
lemma natCast_dehn [Finite α] (n : ℕ) : (P.dehn n : ℕ∞) = sSup (P.area '' P.kerBall n) :=
  ENat.natCast_toNat (P.sSup_area_image_kerBall_ne_top n)

/-- The Dehn function is an isoperimetric function: every word of length at most `n` that
evaluates to the identity in `G` has area at most `P.dehn n`. -/
lemma area_le_dehn [Finite α] (hw : w ∈ P.kerBall n) : P.area w ≤ P.dehn n := by
  rw [P.natCast_dehn n]
  exact le_sSup ⟨w, hw, rfl⟩

lemma area_le_dehn_norm [Finite α] (hw : w ∈ P.lift.ker) :
    P.area w ≤ P.dehn (FreeGroup.norm w) :=
  P.area_le_dehn (P.mem_kerBall_norm hw)

/-- The Dehn function is the *least* isoperimetric function: `P.dehn n ≤ m` exactly when `m` bounds
the area of every word of length at most `n` that evaluates to the identity in `G`. -/
lemma dehn_le_iff [Finite α] {m : ℕ} : P.dehn n ≤ m ↔ ∀ w ∈ P.kerBall n, P.area w ≤ m := by
  rw [← Nat.cast_le (α := ℕ∞), P.natCast_dehn n, sSup_le_iff, Set.forall_mem_image]

@[simp]
lemma dehn_zero : P.dehn 0 = 0 := by simp [dehn]

lemma dehn_mono [Finite α] : Monotone P.dehn := fun _ n hmn ↦
  ENat.toNat_le_toNat (sSup_le_sSup (Set.image_mono (P.kerBall_mono hmn)))
    (P.sSup_area_image_kerBall_ne_top n)

end Dehn

end Group.Presentation
