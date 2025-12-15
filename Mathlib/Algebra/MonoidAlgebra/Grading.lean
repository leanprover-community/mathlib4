/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.Algebra.DirectSum.Internal
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.MonoidAlgebra.Support
public import Mathlib.LinearAlgebra.Finsupp.SumProd
public import Mathlib.RingTheory.GradedAlgebra.Basic

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

@[expose] public section


noncomputable section

namespace AddMonoidAlgebra

variable {M : Type*} {ι : Type*} {R : Type*}

section

variable (R) [CommSemiring R]

/-- The submodule corresponding to each grade given by the degree function `f`. -/
abbrev gradeBy (f : M → ι) (i : ι) : Submodule R R[M] where
  carrier := { a | ∀ m, m ∈ a.coeff.support → f m = i }
  zero_mem' m h := by cases h
  add_mem' {a b} ha hb m h := by
    classical exact (Finset.mem_union.mp (Finsupp.support_add h)).elim (ha m) (hb m)
  smul_mem' _ _ h := Set.Subset.trans Finsupp.support_smul h

/-- The submodule corresponding to each grade. -/
abbrev grade (m : M) : Submodule R R[M] :=
  gradeBy R id m

theorem gradeBy_id : gradeBy R (id : M → M) = grade R := rfl

theorem mem_gradeBy_iff (f : M → ι) (i : ι) (a : R[M]) :
    a ∈ gradeBy R f i ↔ (a.coeff.support : Set M) ⊆ f ⁻¹' {i} := by rfl

theorem mem_grade_iff (m : M) (a : R[M]) : a ∈ grade R m ↔ a.coeff.support ⊆ {m} := by
  rw [← Finset.coe_subset, Finset.coe_singleton]
  rfl

theorem mem_grade_iff' (m : M) (a : R[M]) :
    a ∈ grade R m ↔ a ∈ LinearMap.range (lsingle (R := R) m) := by
  rw [mem_grade_iff, Finsupp.support_subset_singleton']; simp [← coeff_inj, eq_comm]

theorem grade_eq_lsingle_range (m : M) : grade R m = LinearMap.range (lsingle m) :=
  Submodule.ext (mem_grade_iff' R m)

theorem single_mem_gradeBy {R} [CommSemiring R] (f : M → ι) (m : M) (r : R) :
    single m r ∈ gradeBy R f (f m) := by
  intro x hx
  rw [Finset.mem_singleton.mp (Finsupp.support_single_subset hx)]

theorem single_mem_grade {R} [CommSemiring R] (i : M) (r : R) : single i r ∈ grade R i :=
  single_mem_gradeBy _ _ _

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
    obtain ⟨ma, hma, mb, hmb, rfl⟩ : ∃ y ∈ a.coeff.support, ∃ z ∈ b.coeff.support, y + z = c :=
      Finset.mem_add.1 <| support_coeff_mul_subset a b hc
    rw [map_add, ha ma hma, hb mb hmb]

instance grade.gradedMonoid [AddMonoid M] [CommSemiring R] :
    SetLike.GradedMonoid (grade R : M → Submodule R R[M]) := by
  apply gradeBy.gradedMonoid (AddMonoidHom.id _)

variable [AddMonoid M] [DecidableEq ι] [AddMonoid ι] [CommSemiring R] (f : M →+ ι)

/-- Auxiliary definition; the canonical grade decomposition, used to provide
`DirectSum.decompose`. -/
def decomposeAux : R[M] →ₐ[R] ⨁ i : ι, gradeBy R f i :=
  lift R _ M {
    toFun m := .of (fun i ↦ gradeBy R f i) (f m.toAdd) ⟨single m.toAdd 1, single_mem_gradeBy _ _ _⟩
    map_one' := of_eq_of_gradedMonoid_eq (by congr 2 <;> simp)
    map_mul' i j := by
      dsimp only [toAdd_one, Eq.ndrec, Set.mem_setOf_eq, ne_eq, OneHom.toFun_eq_coe,
        OneHom.coe_mk, toAdd_mul]
      convert (of_mul_of _ _).symm <;> simp [SetLike.coe_gMul] }

theorem decomposeAux_single (m : M) (r : R) :
    decomposeAux f (single m r) =
      .of (fun i ↦ gradeBy R f i) (f m) ⟨single m r, single_mem_gradeBy _ _ _⟩ := by
  refine (lift_single _ _ _).trans ?_
  refine (DirectSum.of_smul R _ _ _).symm.trans ?_
  apply DirectSum.of_eq_of_gradedMonoid_eq
  refine Sigma.subtype_ext rfl ?_
  refine (smul_single' _ _ _).trans ?_
  rw [mul_one]
  rfl

theorem decomposeAux_coe {i : ι} (x : gradeBy R f i) :
    decomposeAux f ↑x = DirectSum.of (fun i => gradeBy R f i) i x := by
  classical
  obtain ⟨x, hx⟩ := x
  revert hx
  refine induction x ?_ ?_
  · intro hx
    symm
    exact map_zero _
  · intro m b y hmy hb ih hmby
    have : Disjoint (Finsupp.single m b).support y.coeff.support := by
      simpa only [Finsupp.support_single_ne_zero _ hb, Finset.disjoint_singleton_left]
    rw [mem_gradeBy_iff, coeff_add, coeff_single, Finsupp.support_add_eq this, Finset.coe_union,
      Set.union_subset_iff] at hmby
    obtain ⟨h1, h2⟩ := hmby
    have : f m = i := by
      rwa [Finsupp.support_single_ne_zero _ hb, Finset.coe_singleton, Set.singleton_subset_iff]
        at h1
    subst this
    simp only [map_add, decomposeAux_single f m]
    let ih' := ih h2
    dsimp at ih'
    rw [ih', ← map_add]
    apply DirectSum.of_eq_of_gradedMonoid_eq
    congr 2

instance gradeBy.gradedAlgebra : GradedAlgebra (gradeBy R f) :=
  GradedAlgebra.ofAlgHom _ (decomposeAux f)
    (by
      ext : 4
      dsimp
      rw [decomposeAux_single, DirectSum.coeAlgHom_of, Subtype.coe_mk])
    fun i x => by rw [decomposeAux_coe f x]

-- Lean can't find this later without us repeating it
instance gradeBy.decomposition : DirectSum.Decomposition (gradeBy R f) := by infer_instance

@[simp]
theorem decomposeAux_eq_decompose :
    ⇑(decomposeAux f : R[M] →ₐ[R] ⨁ i : ι, gradeBy R f i) =
      DirectSum.decompose (gradeBy R f) :=
  rfl

theorem GradesBy.decompose_single (m : M) (r : R) :
    DirectSum.decompose (gradeBy R f) (single m r : R[M]) =
      .of (fun i ↦ gradeBy R f i) (f m) ⟨single m r, single_mem_gradeBy _ _ _⟩ :=
  decomposeAux_single _ _ _

instance grade.gradedAlgebra : GradedAlgebra (grade R : ι → Submodule _ _) :=
  AddMonoidAlgebra.gradeBy.gradedAlgebra (AddMonoidHom.id _)

-- Lean can't find this later without us repeating it
instance grade.decomposition : DirectSum.Decomposition (grade R : ι → Submodule _ _) := by
  infer_instance

theorem grade.decompose_single (i : ι) (r : R) :
    DirectSum.decompose (grade R : ι → Submodule _ _) (single i r) =
      .of (fun i ↦ grade R i) i ⟨single i r, single_mem_grade _ _⟩ :=
  decomposeAux_single _ _ _

/-- `AddMonoidAlgebra.gradeBy` describe an internally graded algebra. -/
theorem gradeBy.isInternal : DirectSum.IsInternal (gradeBy R f) :=
  DirectSum.Decomposition.isInternal _

/-- `AddMonoidAlgebra.grade` describe an internally graded algebra. -/
theorem grade.isInternal : DirectSum.IsInternal (grade R : ι → Submodule R _) :=
  DirectSum.Decomposition.isInternal _

end AddMonoidAlgebra
