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

* `AddMonoidAlgebra.gradeBy R f i`: the `i`th grade of an `AddMonoidAlgebra R M` given by the
  degree function `f`.
* `AddMonoidAlgebra.grade R i`: the `i`th grade of an `AddMonoidAlgebra R M` when the degree
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

variable {M : Type*} {ι : Type*} {R : Type*} [DecidableEq M]

section

variable (R) [CommSemiring R]

/-- The submodule corresponding to each grade given by the degree function `f`. -/
abbrev gradeBy (f : M → ι) (i : ι) : Submodule R (AddMonoidAlgebra R M) where
  carrier := { a | ∀ m, m ∈ a.support → f m = i }
  zero_mem' m h := by cases h
                      -- 🎉 no goals
  add_mem' {a b} ha hb m h := Or.recOn (Finset.mem_union.mp (Finsupp.support_add h)) (ha m) (hb m)
  smul_mem' a m h := Set.Subset.trans Finsupp.support_smul h
#align add_monoid_algebra.grade_by AddMonoidAlgebra.gradeBy

/-- The submodule corresponding to each grade. -/
abbrev grade (m : M) : Submodule R (AddMonoidAlgebra R M) :=
  gradeBy R id m
#align add_monoid_algebra.grade AddMonoidAlgebra.grade

theorem gradeBy_id : gradeBy R (id : M → M) = grade R := by rfl
                                                            -- 🎉 no goals
#align add_monoid_algebra.grade_by_id AddMonoidAlgebra.gradeBy_id

theorem mem_gradeBy_iff (f : M → ι) (i : ι) (a : AddMonoidAlgebra R M) :
    a ∈ gradeBy R f i ↔ (a.support : Set M) ⊆ f ⁻¹' {i} := by rfl
                                                              -- 🎉 no goals
#align add_monoid_algebra.mem_grade_by_iff AddMonoidAlgebra.mem_gradeBy_iff

theorem mem_grade_iff (m : M) (a : AddMonoidAlgebra R M) : a ∈ grade R m ↔ a.support ⊆ {m} := by
  rw [← Finset.coe_subset, Finset.coe_singleton]
  -- ⊢ a ∈ grade R m ↔ ↑a.support ⊆ {m}
  rfl
  -- 🎉 no goals
#align add_monoid_algebra.mem_grade_iff AddMonoidAlgebra.mem_grade_iff

theorem mem_grade_iff' (m : M) (a : AddMonoidAlgebra R M) :
    a ∈ grade R m ↔ a ∈ (LinearMap.range (Finsupp.lsingle m : R →ₗ[R] M →₀ R) :
      Submodule R (AddMonoidAlgebra R M)) := by
  rw [mem_grade_iff, Finsupp.support_subset_singleton']
  -- ⊢ (∃ b, a = Finsupp.single m b) ↔ a ∈ LinearMap.range (Finsupp.lsingle m)
  apply exists_congr
  -- ⊢ ∀ (a_1 : R), a = Finsupp.single m a_1 ↔ ↑(Finsupp.lsingle m) a_1 = a
  intro r
  -- ⊢ a = Finsupp.single m r ↔ ↑(Finsupp.lsingle m) r = a
  constructor <;> exact Eq.symm
  -- ⊢ a = Finsupp.single m r → ↑(Finsupp.lsingle m) r = a
                  -- 🎉 no goals
                  -- 🎉 no goals
#align add_monoid_algebra.mem_grade_iff' AddMonoidAlgebra.mem_grade_iff'

theorem grade_eq_lsingle_range (m : M) :
    grade R m = LinearMap.range (Finsupp.lsingle m : R →ₗ[R] M →₀ R) :=
  Submodule.ext (mem_grade_iff' R m)
#align add_monoid_algebra.grade_eq_lsingle_range AddMonoidAlgebra.grade_eq_lsingle_range

theorem single_mem_gradeBy {R} [CommSemiring R] (f : M → ι) (m : M) (r : R) :
    Finsupp.single m r ∈ gradeBy R f (f m) := by
  intro x hx
  -- ⊢ f x = f m
  rw [Finset.mem_singleton.mp (Finsupp.support_single_subset hx)]
  -- 🎉 no goals
#align add_monoid_algebra.single_mem_grade_by AddMonoidAlgebra.single_mem_gradeBy

theorem single_mem_grade {R} [CommSemiring R] (i : M) (r : R) : Finsupp.single i r ∈ grade R i :=
  single_mem_gradeBy _ _ _
#align add_monoid_algebra.single_mem_grade AddMonoidAlgebra.single_mem_grade

end

open DirectSum

instance gradeBy.gradedMonoid [AddMonoid M] [AddMonoid ι] [CommSemiring R] (f : M →+ ι) :
    SetLike.GradedMonoid (gradeBy R f : ι → Submodule R (AddMonoidAlgebra R M)) where
  one_mem m h := by
    rw [one_def] at h
    -- ⊢ ↑f m = 0
    by_cases H : (1 : R) = (0 : R)
    -- ⊢ ↑f m = 0
    · rw [H, single, Finsupp.single_zero] at h
      -- ⊢ ↑f m = 0
      cases h
      -- 🎉 no goals
    · rw [Finsupp.support_single_ne_zero _ H, Finset.mem_singleton] at h
      -- ⊢ ↑f m = 0
      rw [h, AddMonoidHom.map_zero]
      -- 🎉 no goals
  mul_mem i j a b ha hb c hc := by
    set h := support_mul a b hc
    -- ⊢ ↑f c = i + j
    simp only [Finset.mem_biUnion] at h
    -- ⊢ ↑f c = i + j
    rcases h with ⟨ma, ⟨hma, ⟨mb, ⟨hmb, hmc⟩⟩⟩⟩
    -- ⊢ ↑f c = i + j
    rw [← ha ma hma, ← hb mb hmb, Finset.mem_singleton.mp hmc]
    -- ⊢ ↑f (ma + mb) = ↑f ma + ↑f mb
    apply AddMonoidHom.map_add
    -- 🎉 no goals
#align add_monoid_algebra.grade_by.graded_monoid AddMonoidAlgebra.gradeBy.gradedMonoid

instance grade.gradedMonoid [AddMonoid M] [CommSemiring R] :
    SetLike.GradedMonoid (grade R : M → Submodule R (AddMonoidAlgebra R M)) := by
  apply gradeBy.gradedMonoid (AddMonoidHom.id _)
  -- 🎉 no goals
#align add_monoid_algebra.grade.graded_monoid AddMonoidAlgebra.grade.gradedMonoid

variable [AddMonoid M] [DecidableEq ι] [AddMonoid ι] [CommSemiring R] (f : M →+ ι)

set_option maxHeartbeats 260000 in
/-- Auxiliary definition; the canonical grade decomposition, used to provide
`DirectSum.decompose`. -/
def decomposeAux : AddMonoidAlgebra R M →ₐ[R] ⨁ i : ι, gradeBy R f i :=
  AddMonoidAlgebra.lift R M _
    { toFun := fun m =>
        DirectSum.of (fun i : ι => gradeBy R f i) (f (Multiplicative.toAdd m))
          ⟨Finsupp.single (Multiplicative.toAdd m) 1, single_mem_gradeBy _ _ _⟩
      map_one' :=
        DirectSum.of_eq_of_gradedMonoid_eq
          (by congr 2 <;> simp)
                          -- 🎉 no goals
                          -- 🎉 no goals
                          -- 🎉 no goals
      map_mul' := fun i j => by
        symm
        -- ⊢ OneHom.toFun { toFun := fun m => ↑(DirectSum.of (fun i => { x // x ∈ gradeBy …
        dsimp only [toAdd_one, Eq.ndrec, Set.mem_setOf_eq, ne_eq, OneHom.toFun_eq_coe,
          OneHom.coe_mk, toAdd_mul]
        convert DirectSum.of_mul_of (A := (fun i : ι => gradeBy R f i)) _ _
        repeat { rw [ AddMonoidHom.map_add] }
        -- ⊢ Finsupp.single (↑Multiplicative.toAdd i + ↑Multiplicative.toAdd j) 1 = ↑(Gra …
        simp only [SetLike.coe_gMul]
        -- ⊢ Finsupp.single (↑Multiplicative.toAdd i + ↑Multiplicative.toAdd j) 1 = Finsu …
        refine Eq.trans (by rw [one_mul]) single_mul_single.symm }
        -- 🎉 no goals
#align add_monoid_algebra.decompose_aux AddMonoidAlgebra.decomposeAux

theorem decomposeAux_single (m : M) (r : R) :
    decomposeAux f (Finsupp.single m r) =
      DirectSum.of (fun i : ι => gradeBy R f i) (f m)
        ⟨Finsupp.single m r, single_mem_gradeBy _ _ _⟩ := by
  refine' (lift_single _ _ _).trans _
  -- ⊢ r • ↑{ toOneHom := { toFun := fun m => ↑(DirectSum.of (fun i => { x // x ∈ g …
  refine' (DirectSum.of_smul R _ _ _).symm.trans _
  -- ⊢ ↑(DirectSum.of (fun i => (fun i => { x // x ∈ gradeBy R (↑f) i }) i) (↑f (↑M …
  apply DirectSum.of_eq_of_gradedMonoid_eq
  -- ⊢ GradedMonoid.mk (↑f (↑Multiplicative.toAdd (↑Multiplicative.ofAdd m))) (r •  …
  refine' Sigma.subtype_ext rfl _
  -- ⊢ ↑(GradedMonoid.mk (↑f (↑Multiplicative.toAdd (↑Multiplicative.ofAdd m))) (r  …
  refine' (Finsupp.smul_single' _ _ _).trans _
  -- ⊢ Finsupp.single (↑Multiplicative.toAdd (↑Multiplicative.ofAdd m)) (r * 1) = ↑ …
  rw [mul_one]
  -- ⊢ Finsupp.single (↑Multiplicative.toAdd (↑Multiplicative.ofAdd m)) r = ↑(Grade …
  rfl
  -- 🎉 no goals
#align add_monoid_algebra.decompose_aux_single AddMonoidAlgebra.decomposeAux_single

theorem decomposeAux_coe {i : ι} (x : gradeBy R f i) :
    decomposeAux f ↑x = DirectSum.of (fun i => gradeBy R f i) i x := by
  obtain ⟨x, hx⟩ := x
  -- ⊢ ↑(decomposeAux f) ↑{ val := x, property := hx } = ↑(DirectSum.of (fun i => { …
  revert hx
  -- ⊢ ∀ (hx : x ∈ gradeBy R (↑f) i), ↑(decomposeAux f) ↑{ val := x, property := hx …
  refine' Finsupp.induction x _ _
  -- ⊢ ∀ (hx : 0 ∈ gradeBy R (↑f) i), ↑(decomposeAux f) ↑{ val := 0, property := hx …
  · intro hx
    -- ⊢ ↑(decomposeAux f) ↑{ val := 0, property := hx } = ↑(DirectSum.of (fun i => { …
    symm
    -- ⊢ ↑(DirectSum.of (fun i => { x // x ∈ gradeBy R (↑f) i }) i) { val := 0, prope …
    exact AddMonoidHom.map_zero _
    -- 🎉 no goals
  · intro m b y hmy hb ih hmby
    -- ⊢ ↑(decomposeAux f) ↑{ val := Finsupp.single m b + y, property := hmby } = ↑(D …
    have : Disjoint (Finsupp.single m b).support y.support := by
      simpa only [Finsupp.support_single_ne_zero _ hb, Finset.disjoint_singleton_left]
    rw [mem_gradeBy_iff, Finsupp.support_add_eq this, Finset.coe_union, Set.union_subset_iff]
      at hmby
    cases' hmby with h1 h2
    -- ⊢ ↑(decomposeAux f) ↑{ val := Finsupp.single m b + y, property := hmby } = ↑(D …
    have : f m = i := by
      rwa [Finsupp.support_single_ne_zero _ hb, Finset.coe_singleton, Set.singleton_subset_iff]
        at h1
    subst this
    -- ⊢ ↑(decomposeAux f) ↑{ val := Finsupp.single m b + y, property := hmby } = ↑(D …
    simp only [AlgHom.map_add, Submodule.coe_mk, decomposeAux_single f m]
    -- ⊢ ↑(DirectSum.of (fun i => { x // x ∈ gradeBy R (↑f) i }) (↑f m)) { val := Fin …
    let ih' := ih h2
    -- ⊢ ↑(DirectSum.of (fun i => { x // x ∈ gradeBy R (↑f) i }) (↑f m)) { val := Fin …
    dsimp at ih'
    -- ⊢ ↑(DirectSum.of (fun i => { x // x ∈ gradeBy R (↑f) i }) (↑f m)) { val := Fin …
    rw [ih', ← AddMonoidHom.map_add]
    -- ⊢ ↑(DirectSum.of (fun i => { x // x ∈ gradeBy R (↑f) i }) (↑f m)) ({ val := Fi …
    apply DirectSum.of_eq_of_gradedMonoid_eq
    -- ⊢ GradedMonoid.mk (↑f m) ({ val := Finsupp.single m b, property := (_ : Finsup …
    congr 2
    -- 🎉 no goals
#align add_monoid_algebra.decompose_aux_coe AddMonoidAlgebra.decomposeAux_coe

instance gradeBy.gradedAlgebra : GradedAlgebra (gradeBy R f) :=
  GradedAlgebra.ofAlgHom _ (decomposeAux f)
    (by
      ext : 2
      -- ⊢ ↑(MonoidHom.comp (↑(AlgHom.comp (coeAlgHom (gradeBy R ↑f)) (decomposeAux f)) …
      simp only [MonoidHom.coe_comp, MonoidHom.coe_coe, AlgHom.coe_comp, Function.comp_apply,
        of_apply, AlgHom.coe_id, id_eq]
      rw [decomposeAux_single, DirectSum.coeAlgHom_of, Subtype.coe_mk])
      -- 🎉 no goals
    fun i x => by rw [decomposeAux_coe f x]
                  -- 🎉 no goals
#align add_monoid_algebra.grade_by.graded_algebra AddMonoidAlgebra.gradeBy.gradedAlgebra

-- Lean can't find this later without us repeating it
instance gradeBy.decomposition : DirectSum.Decomposition (gradeBy R f) := by infer_instance
                                                                             -- 🎉 no goals
#align add_monoid_algebra.grade_by.decomposition AddMonoidAlgebra.gradeBy.decomposition

@[simp]
theorem decomposeAux_eq_decompose :
    ⇑(decomposeAux f : AddMonoidAlgebra R M →ₐ[R] ⨁ i : ι, gradeBy R f i) =
      DirectSum.decompose (gradeBy R f) :=
  rfl
#align add_monoid_algebra.decompose_aux_eq_decompose AddMonoidAlgebra.decomposeAux_eq_decompose

@[simp]
theorem GradesBy.decompose_single (m : M) (r : R) :
    DirectSum.decompose (gradeBy R f) (Finsupp.single m r : AddMonoidAlgebra R M) =
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
  -- 🎉 no goals
#align add_monoid_algebra.grade.decomposition AddMonoidAlgebra.grade.decomposition

@[simp]
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
