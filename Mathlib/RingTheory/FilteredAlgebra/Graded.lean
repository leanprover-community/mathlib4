/-
Copyright (c) 2026 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan
-/
module

public import Mathlib.RingTheory.FilteredAlgebra.Basic
public import Mathlib.RingTheory.FilteredAlgebra.Lattice
public import Mathlib.RingTheory.GradedAlgebra.Basic
public import Mathlib.RingTheory.HahnSeries.Multiplication
public import Mathlib.LinearAlgebra.Quotient.Bilinear
public import Mathlib.Algebra.DirectSum.Algebra
public import Mathlib.LinearAlgebra.TensorProduct.Submodule


/-!
# Relations between graded rings and filtered rings

In this file, we introduce the associated graded ring attached to a filtered ring, and
the filtered ring attached to a graded ring, when the grading is by an ordered additive
commutative monoid.

-/

public section

noncomputable section

universe u v w

variable {ι : Type v} {R : Type w} {A : Type u}

section

variable [DecidableEq ι] [AddCommMonoid ι] [PartialOrder ι] [IsOrderedAddMonoid ι] [CommSemiring R]
  [Semiring A] [Algebra R A] (F : ι → Submodule R A) [GradedAlgebra F]

open DirectSum

lemma isRingFiltration_of_graded :
    IsRingFiltration (fun i ↦ ⨆ j ≤ i, F j) (fun i ↦ ⨆ j < i, F j) where
  mono _ j h := by
    simp only [iSup_le_iff]
    intro i hi
    refine le_iSup_of_le i ?_
    rw [le_iSup_iff]
    have : i ≤ j := hi.trans h
    tauto
  is_le {_ j} h := by
    simp only [iSup_le_iff]
    intro i hi
    refine le_iSup_of_le i ?_
    rw [le_iSup_iff]
    have : i < j := lt_of_le_of_lt hi h
    tauto
  is_sup _ _ h := by
    simp only [iSup_le_iff]
    intro i hi
    simp only [iSup_le_iff] at h
    exact h i hi i (Std.IsPreorder.le_refl i)
  one_mem := mem_of_le_of_mem (S := F 0)
    (le_iSup_iff.mpr fun _ h ↦ (by simpa using h 0)) (SetLike.one_mem_graded F)
  mul_mem {i j} gi gj hi hj := by
    classical
    obtain ⟨fgi, hgi⟩ := (Submodule.mem_biSup_iff_exists_dfinsupp R (fun k ↦ k ≤ i) F gi).mp hi
    obtain ⟨fgj, hgj⟩ := (Submodule.mem_biSup_iff_exists_dfinsupp R (fun k ↦ k ≤ j) F gj).mp hj
    rw [← hgi, ← hgj]
    simp only [DFinsupp.lsum_apply_apply, DFinsupp.sumAddHom_apply, DFinsupp.sum,
      DFinsupp.support_filter, DFinsupp.filter_apply, LinearMap.toAddMonoidHom_coe,
      Submodule.subtype_apply, Finset.sum_mul_sum]
    refine sum_mem fun k hk ↦ sum_mem fun l hl ↦ ?_
    have hki : k ≤ i := by grind
    have hlj : l ≤ j := by grind
    simp only [hki, ↓reduceIte, hlj]
    refine Set.mem_of_subset_of_mem (IsConcreteLE.coe_subset_coe'.mpr (le_sSup ?_)) <|
      SetLike.mul_mem_graded (Submodule.coe_mem (fgi k)) (Submodule.coe_mem (fgj l))
    use k + l
    simp [add_le_add hki hlj]

end

section

open DirectSum

variable [CommRing R] [Ring A] [Algebra R A] (F : ι → Submodule R A) (F_lt : ι → Submodule R A)

abbrev gradedPart (i : ι) := (F i) ⧸ (F_lt i).submoduleOf (F i)

--def quotmap (i : ι) : F i → gradedPart F i := Submodule.Quotient.mk
--instance (i : ι) : AddCommGroup (gradedPart F F_lt i) := inferInstance

abbrev associatedGraded := ⨁ i, gradedPart F F_lt i

namespace AssociatedGraded

/-- Cast between "equal" graded parts. -/
def cast {i j} (h : i = j) : gradedPart F F_lt i ≃ₗ[R] gradedPart F F_lt j := LinearEquiv.cast h

theorem cast_mk {i j} (h : i = j) (a : F i) :
    cast F F_lt h (Submodule.Quotient.mk a) =
    (Submodule.Quotient.mk (LinearEquiv.cast (M := fun k ↦ F k) (R := R) h a)) := by
  subst h
  rfl

@[simp]
theorem cast_refl {i} (h : i = i) : cast F F_lt h = LinearEquiv.refl _ _ :=
  LinearEquiv.toLinearMap_inj.mp rfl

@[simp]
theorem cast_symm {i j} (h : i = j) : (cast F F_lt h).symm = cast F F_lt h.symm :=
  LinearEquiv.toLinearMap_inj.mp rfl

@[simp]
theorem cast_trans {i j k} (h : i = j) (h' : j = k) :
    (cast F F_lt h).trans (cast F F_lt h') = cast F F_lt (h.trans h') := by
  subst h h'
  simp

@[simp]
theorem cast_cast {i j k} (h : i = j) (h' : j = k) (a : gradedPart F F_lt i) :
    cast F F_lt h' (cast F F_lt h a) = cast F F_lt (h.trans h') a := by
  subst h h'
  simp

@[ext (iff := false)]
theorem gradedMonoid_eq_of_cast {a b : GradedMonoid fun i => gradedPart F F_lt i}
    (h : a.fst = b.fst) (h2 : cast F F_lt h a.snd = b.snd) :
    a = b := by
  obtain ⟨a1, a2⟩ := a
  obtain ⟨b1, b2⟩ := b
  simp only at h h2
  subst h
  simp only [cast_refl, LinearEquiv.refl_apply] at h2
  rw [h2]

theorem cast_eq_cast {i j} (h : i = j) :
    ⇑(cast F F_lt h) = _root_.cast (congrArg (fun i => gradedPart F F_lt i) h) := by
  subst h
  rw [cast_refl]
  rfl

-- see LinearAlgebra/TensorPower/Basic.lean for use of casts.

variable [PartialOrder ι]

lemma DFinsupp.lsum_subtype_coe [DecidableEq ι] [AddMonoid ι] [IsRingFiltration F F_lt]
    (x : Π₀ i, F i) [(i : ι) → (x : ↥(F i)) → Decidable (x ≠ 0)] (p : ι → Prop) [DecidablePred p] :
    ((DFinsupp.lsum R) fun i ↦ (F i).subtype) (DFinsupp.filter (fun i ↦ p i) x) =
      x.sum fun i r ↦ if p i then r else 0 := by
  simp only [DFinsupp.filter_def, SetLike.coe_sort_coe, DFinsupp.lsum_apply_apply,
    DFinsupp.sumAddHom_apply, DFinsupp.sum, DFinsupp.mk_apply, Finset.mem_filter,
    DFinsupp.mem_support_toFun, ne_eq, dite_eq_ite, LinearMap.toAddMonoidHom_coe,
    Submodule.subtype_apply, Finset.sum_ite, Finset.sum_const_zero, add_zero]
  exact Finset.sum_congr (by grind) (by grind)
--#find_home! dfinsupp_lsum_coe -- here

omit [PartialOrder ι] in
lemma dfinsupp_mul [DecidableEq ι] (x : Π₀ i, F i) {y : A}
    [(i : ι) → (x : ↥(F i)) → Decidable (x ≠ 0)] :
    (x.sum fun _ r ↦ (r : A)) * y = x.sum fun _ r ↦ r * y := by
  simp only [DFinsupp.sum]
  rw [Finset.sum_mul]
--#find_home! dfinsupp_mul --[Mathlib.LinearAlgebra.DFinsupp]

lemma mul_mem_f_lt [AddCommMonoid ι] [AddRightStrictMono ι]
    [IsRingFiltration F F_lt] (i j : ι) {x y : A} (hx : x ∈ F_lt i) (hy : y ∈ F j) :
    x * y ∈ F_lt (i + j) := by
  classical
  rw [IsFiltration.f_lt_eq_sup F F_lt i, Submodule.mem_biSup_iff_exists_dfinsupp R] at hx
  obtain ⟨f, hf⟩ := hx
  rw [← hf, DFinsupp.lsum_subtype_coe, DFinsupp.sum, Finset.sum_mul]
  refine Submodule.sum_mem (F_lt (i + j)) ?_
  intro k _
  by_cases hk : k < i
  · simp only [hk, ↓reduceIte]
    suffices F (k + j) ≤ F_lt (i + j) by
      exact (Submodule.mem_toAddSubgroup (F_lt (i + j))).mp
        (this (SetLike.mul_mem_graded (Submodule.coe_mem (f k)) hy))
    exact IsFiltration.is_le <| add_lt_add_left hk j
  · simp [hk]

lemma mul_mem_f_lt' [AddCommMonoid ι] [AddLeftStrictMono ι]
    [IsRingFiltration F F_lt] (i j : ι) {x y : A} (hx : x ∈ F i) (hy : y ∈ F_lt j) :
    x * y ∈ F_lt (i + j) := by
  classical
  rw [IsFiltration.f_lt_eq_sup F F_lt j, Submodule.mem_biSup_iff_exists_dfinsupp R] at hy
  obtain ⟨f, hf⟩ := hy
  rw [← hf, DFinsupp.lsum_subtype_coe, DFinsupp.sum, Finset.mul_sum]
  refine Submodule.sum_mem (F_lt (i + j)) ?_
  intro k _
  by_cases hk : k < j
  · simp only [hk, ↓reduceIte]
    suffices F (i + k) ≤ F_lt (i + j) by
      exact (Submodule.mem_toAddSubgroup (F_lt (i + j))).mp
        (this (SetLike.mul_mem_graded hx (Submodule.coe_mem (f k))))
    refine IsFiltration.is_le <| add_lt_add_right hk i
  · simp [hk]


variable [AddCommMonoid ι] [IsOrderedCancelAddMonoid ι] [IsRingFiltration F F_lt]

def filteredMul (i j : ι) : F i →ₗ[R] F j →ₗ[R] F (i + j) where
  toFun x := {
    toFun y := ⟨x.val * y.val, SetLike.mul_mem_graded x.2 y.2⟩
    map_add' _ _ := by simp [mul_add]
    map_smul' _ _ := by simp }
  map_add' _ _ := by ext; simp [add_mul]
  map_smul' _ _ := by ext; simp

lemma mem_lt_of_mul_left (i j : ι) {x y : A} (hx : x ∈ F i) (hxlt : x ∈ F_lt i)
    (hy : y ∈ F j) :
    (filteredMul F F_lt i j ⟨x, hx⟩ ⟨y, hy⟩).val ∈ F_lt (i + j) := by
  simp only [filteredMul, LinearMap.coe_mk, AddHom.coe_mk]
  exact mul_mem_f_lt F F_lt _ _ hxlt hy

noncomputable def mulQuotient (i j : ι) :
    F i →ₗ[R] F j →ₗ[R] gradedPart F F_lt (i + j) :=
  (filteredMul F F_lt i j).compr₂ (Submodule.mkQ _)

omit [IsOrderedCancelAddMonoid ι] in
lemma mulQuotient_eq {i j} (x : F i) (y : F j) :
    mulQuotient F F_lt i j x y = Submodule.Quotient.mk (filteredMul F F_lt i j x y) := by
  simp [mulQuotient]

lemma submodule_le_mulQuotient (i j : ι) :
    (F_lt i).submoduleOf (F i) ≤ (mulQuotient F F_lt i j).ker := by
  intro x hx
  ext y
  simp only [mulQuotient, filteredMul, LinearMap.compr₂_apply, LinearMap.coe_mk, AddHom.coe_mk,
    Submodule.mkQ_apply, LinearMap.zero_apply, Submodule.Quotient.mk_eq_zero]
  exact mul_mem_f_lt F F_lt i j hx y.2

lemma submodule_le_flip_mulQuotient (i j : ι) :
    (F_lt j).submoduleOf (F j) ≤ (mulQuotient F F_lt i j).flip.ker := by
  intro x hx
  ext y
  simp only [mulQuotient, filteredMul, LinearMap.flip_apply, LinearMap.compr₂_apply,
    LinearMap.coe_mk, AddHom.coe_mk, Submodule.mkQ_apply, LinearMap.zero_apply,
    Submodule.Quotient.mk_eq_zero]
  exact mul_mem_f_lt' F F_lt i j y.2 hx

@[simps]
noncomputable instance : GradedMonoid.GMul (gradedPart F F_lt) where
  mul {i j} x y := (mulQuotient F F_lt i j).liftQ₂ _ _ (submodule_le_mulQuotient F F_lt i j)
    (submodule_le_flip_mulQuotient F F_lt i j) x y

@[simps]
noncomputable instance : GradedMonoid.GOne (gradedPart F F_lt) where
  one := Submodule.Quotient.mk (1 : F 0)

/-
theorem mk_mul_mk {i j} (a : F i) (b : F j) :
    GradedMonoid.GMul.mul ((Submodule.mkQ _ a) :
    gradedPart F F_lt i) ((Submodule.mkQ _ b) : gradedPart F F_lt j) =
    Submodule.Quotient.mk (filteredMul F F_lt i j a b) := by
  sorry

theorem one_mul {n} (a : gradedPart F F_lt n) :
    cast F F_lt (zero_add n) (GradedMonoid.GOne.one (A := gradedPart F F_lt) a) = a := by

noncomputable instance : GradedMonoid.GMonoid (gradedPart F F_lt) where
  one_mul x := by
    obtain ⟨k, x⟩ := x
    induction x using Quotient.inductionOn with
    | h x =>
      obtain ⟨x, hx⟩ := x
      simp only [HMul.hMul, Mul.mul, GradedMonoid.fst_one, GradedMonoid.snd_one, one_def, mul_def]
      congr 1
      · exact AddZeroClass.zero_add k
      ·
        sorry


noncomputable instance :
    DirectSum.GRing (gradedPart F F_lt) where
  mul {i j} x y := (mulQuotient F F_lt i j).liftQ₂ _ _ (submodule_le_mulQuotient F F_lt i j)
    (submodule_le_flip_mulQuotient F F_lt i j)  x y
  mul_zero _ := by simp
  zero_mul _ := by simp
  mul_add  _ _ _ := by simp
  add_mul _ _ _ := by simp
  one := Submodule.Quotient.mk (1 : F 0)
  one_mul x := by
    obtain ⟨k, x⟩ := x
    induction x using Quotient.inductionOn with
    | h a => sorry
    --have : (1 : gradedPart' F F_lt 0) = Submodule.Quotient.mk (1 : F 0) := rfl
  mul_one x := by sorry
  mul_assoc := by sorry
  natCast := by sorry
  natCast_zero := by sorry
  natCast_succ := by sorry
  intCast
-/

end AssociatedGraded
