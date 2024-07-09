/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.LinearAlgebra.Finsupp
import Mathlib.Algebra.MonoidAlgebra.Support
import Mathlib.Algebra.DirectSum.Internal
import Mathlib.RingTheory.GradedAlgebra.Basic

#align_import algebra.monoid_algebra.grading from "leanprover-community/mathlib"@"feb99064803fd3108e37c18b0f77d0a8344677a3"

/-!
# Internal grading of an `AddMonoidAlgebra`

In this file, we show that an `AddMonoidAlgebra` has an internal direct sum structure.

## Main results

* `AddMonoidAlgebra.gradeBy R f i`: the `i`th grade of an `R[M]` given by the
  degree function `f`.
* `AddMonoidAlgebra.grade R i`: the `i`th grade of an `R[M]` when the degree
  function is the identity.
* `AddMonoidAlgebra.gradeBy.gradedAlgebra`: `AddMonoidAlgebra` is an algebra graded by
  `AddMonoidAlgebra.gradeBy`.
* `AddMonoidAlgebra.grade.gradedAlgebra`: `AddMonoidAlgebra` is an algebra graded by
  `AddMonoidAlgebra.grade`.
* `AddMonoidAlgebra.gradeBy.isInternal`: propositionally, the statement that
  `AddMonoidAlgebra.gradeBy` defines an internal graded structure.
* `AddMonoidAlgebra.grade.isInternal`: propositionally, the statement that
  `AddMonoidAlgebra.grade` defines an internal graded structure when the degree function
  is the identity.
-/


noncomputable section

namespace AddMonoidAlgebra

variable {M : Type*} {ι : Type*} {R : Type*}

section

variable (R) [CommSemiring R]

/-- The submodule corresponding to each grade given by the degree function `f`. -/
abbrev gradeBy (f : M → ι) (i : ι) : Submodule R R[M] where
  carrier := { a | ∀ m, m ∈ a.support → f m = i }
  zero_mem' m h := by cases h
  add_mem' {a b} ha hb m h := by
    classical exact (Finset.mem_union.mp (Finsupp.support_add h)).elim (ha m) (hb m)
  smul_mem' a m h := Set.Subset.trans Finsupp.support_smul h
#align add_monoid_algebra.grade_by AddMonoidAlgebra.gradeBy

/-- The submodule corresponding to each grade. -/
abbrev grade (m : M) : Submodule R R[M] :=
  gradeBy R id m
#align add_monoid_algebra.grade AddMonoidAlgebra.grade

theorem gradeBy_id : gradeBy R (id : M → M) = grade R := rfl
#align add_monoid_algebra.grade_by_id AddMonoidAlgebra.gradeBy_id

theorem mem_gradeBy_iff (f : M → ι) (i : ι) (a : R[M]) :
    a ∈ gradeBy R f i ↔ (a.support : Set M) ⊆ f ⁻¹' {i} := by rfl
#align add_monoid_algebra.mem_grade_by_iff AddMonoidAlgebra.mem_gradeBy_iff

theorem mem_grade_iff (m : M) (a : R[M]) : a ∈ grade R m ↔ a.support ⊆ {m} := by
  rw [← Finset.coe_subset, Finset.coe_singleton]
  rfl
#align add_monoid_algebra.mem_grade_iff AddMonoidAlgebra.mem_grade_iff

theorem mem_grade_iff' (m : M) (a : R[M]) :
    a ∈ grade R m ↔ a ∈ (LinearMap.range (Finsupp.lsingle m : R →ₗ[R] M →₀ R) :
      Submodule R R[M]) := by
  rw [mem_grade_iff, Finsupp.support_subset_singleton']
  apply exists_congr
  intro r
  constructor <;> exact Eq.symm
#align add_monoid_algebra.mem_grade_iff' AddMonoidAlgebra.mem_grade_iff'

theorem grade_eq_lsingle_range (m : M) :
    grade R m = LinearMap.range (Finsupp.lsingle m : R →ₗ[R] M →₀ R) :=
  Submodule.ext (mem_grade_iff' R m)
#align add_monoid_algebra.grade_eq_lsingle_range AddMonoidAlgebra.grade_eq_lsingle_range

theorem single_mem_gradeBy {R} [CommSemiring R] (f : M → ι) (m : M) (r : R) :
    Finsupp.single m r ∈ gradeBy R f (f m) := by
  intro x hx
  rw [Finset.mem_singleton.mp (Finsupp.support_single_subset hx)]
#align add_monoid_algebra.single_mem_grade_by AddMonoidAlgebra.single_mem_gradeBy

theorem single_mem_grade {R} [CommSemiring R] (i : M) (r : R) : Finsupp.single i r ∈ grade R i :=
  single_mem_gradeBy _ _ _
#align add_monoid_algebra.single_mem_grade AddMonoidAlgebra.single_mem_grade

end

open DirectSum

instance gradeBy.gradedMonoid [AddMonoid M] [AddMonoid ι] [CommSemiring R] (f : M →+ ι) :
    SetLike.GradedMonoid (gradeBy R f : ι → Submodule R R[M]) where
  one_mem m h := by
    rw [one_def] at h
    obtain rfl : m = 0 := Finset.mem_singleton.1 <| Finsupp.support_single_subset h
    apply map_zero
  mul_mem i j a b ha hb c hc := by
    classical
    obtain ⟨ma, hma, mb, hmb, rfl⟩ : ∃ y ∈ a.support, ∃ z ∈ b.support, y + z = c :=
      Finset.mem_add.1 <| support_mul a b hc
    rw [map_add, ha ma hma, hb mb hmb]
#align add_monoid_algebra.grade_by.graded_monoid AddMonoidAlgebra.gradeBy.gradedMonoid

instance grade.gradedMonoid [AddMonoid M] [CommSemiring R] :
    SetLike.GradedMonoid (grade R : M → Submodule R R[M]) := by
  apply gradeBy.gradedMonoid (AddMonoidHom.id _)
#align add_monoid_algebra.grade.graded_monoid AddMonoidAlgebra.grade.gradedMonoid

variable [AddMonoid M] [DecidableEq ι] [AddMonoid ι] [CommSemiring R] (f : M →+ ι)

/-- Auxiliary definition; the canonical grade decomposition, used to provide
`DirectSum.decompose`. -/
def decomposeAux : R[M] →ₐ[R] ⨁ i : ι, gradeBy R f i :=
  AddMonoidAlgebra.lift R M _
    { toFun := fun m =>
        DirectSum.of (fun i : ι => gradeBy R f i) (f (Multiplicative.toAdd m))
          ⟨Finsupp.single (Multiplicative.toAdd m) 1, single_mem_gradeBy _ _ _⟩
      map_one' :=
        DirectSum.of_eq_of_gradedMonoid_eq
          (by congr 2 <;> simp)
      map_mul' := fun i j => by
        symm
        dsimp only [toAdd_one, Eq.ndrec, Set.mem_setOf_eq, ne_eq, OneHom.toFun_eq_coe,
          OneHom.coe_mk, toAdd_mul]
        convert DirectSum.of_mul_of (A := (fun i : ι => gradeBy R f i)) _ _
        repeat { rw [ AddMonoidHom.map_add] }
        simp only [SetLike.coe_gMul]
        exact Eq.trans (by rw [one_mul]) single_mul_single.symm }
#align add_monoid_algebra.decompose_aux AddMonoidAlgebra.decomposeAux

theorem decomposeAux_single (m : M) (r : R) :
    decomposeAux f (Finsupp.single m r) =
      DirectSum.of (fun i : ι => gradeBy R f i) (f m)
        ⟨Finsupp.single m r, single_mem_gradeBy _ _ _⟩ := by
  refine (lift_single _ _ _).trans ?_
  refine (DirectSum.of_smul R _ _ _).symm.trans ?_
  apply DirectSum.of_eq_of_gradedMonoid_eq
  refine Sigma.subtype_ext rfl ?_
  refine (Finsupp.smul_single' _ _ _).trans ?_
  rw [mul_one]
  rfl
#align add_monoid_algebra.decompose_aux_single AddMonoidAlgebra.decomposeAux_single

theorem decomposeAux_coe {i : ι} (x : gradeBy R f i) :
    decomposeAux f ↑x = DirectSum.of (fun i => gradeBy R f i) i x := by
  classical
  obtain ⟨x, hx⟩ := x
  revert hx
  refine Finsupp.induction x ?_ ?_
  · intro hx
    symm
    exact AddMonoidHom.map_zero _
  · intro m b y hmy hb ih hmby
    have : Disjoint (Finsupp.single m b).support y.support := by
      simpa only [Finsupp.support_single_ne_zero _ hb, Finset.disjoint_singleton_left]
    rw [mem_gradeBy_iff, Finsupp.support_add_eq this, Finset.coe_union, Set.union_subset_iff]
      at hmby
    cases' hmby with h1 h2
    have : f m = i := by
      rwa [Finsupp.support_single_ne_zero _ hb, Finset.coe_singleton, Set.singleton_subset_iff]
        at h1
    subst this
    simp only [AlgHom.map_add, Submodule.coe_mk, decomposeAux_single f m]
    let ih' := ih h2
    dsimp at ih'
    rw [ih', ← AddMonoidHom.map_add]
    apply DirectSum.of_eq_of_gradedMonoid_eq
    congr 2
#align add_monoid_algebra.decompose_aux_coe AddMonoidAlgebra.decomposeAux_coe

instance gradeBy.gradedAlgebra : GradedAlgebra (gradeBy R f) :=
  GradedAlgebra.ofAlgHom _ (decomposeAux f)
    (by
      ext : 2
      simp only [MonoidHom.coe_comp, MonoidHom.coe_coe, AlgHom.coe_comp, Function.comp_apply,
        of_apply, AlgHom.coe_id, id_eq]
      rw [decomposeAux_single, DirectSum.coeAlgHom_of, Subtype.coe_mk])
    fun i x => by rw [decomposeAux_coe f x]
#align add_monoid_algebra.grade_by.graded_algebra AddMonoidAlgebra.gradeBy.gradedAlgebra

-- Lean can't find this later without us repeating it
instance gradeBy.decomposition : DirectSum.Decomposition (gradeBy R f) := by infer_instance
#align add_monoid_algebra.grade_by.decomposition AddMonoidAlgebra.gradeBy.decomposition

@[simp]
theorem decomposeAux_eq_decompose :
    ⇑(decomposeAux f : R[M] →ₐ[R] ⨁ i : ι, gradeBy R f i) =
      DirectSum.decompose (gradeBy R f) :=
  rfl
#align add_monoid_algebra.decompose_aux_eq_decompose AddMonoidAlgebra.decomposeAux_eq_decompose

theorem GradesBy.decompose_single (m : M) (r : R) :
    DirectSum.decompose (gradeBy R f) (Finsupp.single m r : R[M]) =
      DirectSum.of (fun i : ι => gradeBy R f i) (f m)
        ⟨Finsupp.single m r, single_mem_gradeBy _ _ _⟩ :=
  decomposeAux_single _ _ _
#align add_monoid_algebra.grades_by.decompose_single AddMonoidAlgebra.GradesBy.decompose_single

instance grade.gradedAlgebra : GradedAlgebra (grade R : ι → Submodule _ _) :=
  AddMonoidAlgebra.gradeBy.gradedAlgebra (AddMonoidHom.id _)
#align add_monoid_algebra.grade.graded_algebra AddMonoidAlgebra.grade.gradedAlgebra

-- Lean can't find this later without us repeating it
instance grade.decomposition : DirectSum.Decomposition (grade R : ι → Submodule _ _) := by
  infer_instance
#align add_monoid_algebra.grade.decomposition AddMonoidAlgebra.grade.decomposition

theorem grade.decompose_single (i : ι) (r : R) :
    DirectSum.decompose (grade R : ι → Submodule _ _) (Finsupp.single i r : AddMonoidAlgebra _ _) =
      DirectSum.of (fun i : ι => grade R i) i ⟨Finsupp.single i r, single_mem_grade _ _⟩ :=
  decomposeAux_single _ _ _
#align add_monoid_algebra.grade.decompose_single AddMonoidAlgebra.grade.decompose_single

/-- `AddMonoidAlgebra.gradeBy` describe an internally graded algebra. -/
theorem gradeBy.isInternal : DirectSum.IsInternal (gradeBy R f) :=
  DirectSum.Decomposition.isInternal _
#align add_monoid_algebra.grade_by.is_internal AddMonoidAlgebra.gradeBy.isInternal

/-- `AddMonoidAlgebra.grade` describe an internally graded algebra. -/
theorem grade.isInternal : DirectSum.IsInternal (grade R : ι → Submodule R _) :=
  DirectSum.Decomposition.isInternal _
#align add_monoid_algebra.grade.is_internal AddMonoidAlgebra.grade.isInternal

end AddMonoidAlgebra
