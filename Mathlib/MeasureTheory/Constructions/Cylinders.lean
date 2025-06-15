/-
Copyright (c) 2023 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Peter Pfaffelhuber, Yaël Dillies, Kin Yau James Wong
-/
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.PiSystem
import Mathlib.Topology.Constructions

/-!
# π-systems of cylinders and square cylinders

The instance `MeasurableSpace.pi` on `∀ i, α i`, where each `α i` has a `MeasurableSpace` `m i`,
is defined as `⨆ i, (m i).comap (fun a => a i)`.
That is, a function `g : β → ∀ i, α i` is measurable iff for all `i`, the function `b ↦ g b i`
is measurable.

We define two π-systems generating `MeasurableSpace.pi`, cylinders and square cylinders.

## Main definitions

Given a finite set `s` of indices, a cylinder is the product of a set of `∀ i : s, α i` and of
`univ` on the other indices. A square cylinder is a cylinder for which the set on `∀ i : s, α i` is
a product set.

* `cylinder s S`: cylinder with base set `S : Set (∀ i : s, α i)` where `s` is a `Finset`
* `squareCylinders C` with `C : ∀ i, Set (Set (α i))`: set of all square cylinders such that for
  all `i` in the finset defining the box, the projection to `α i` belongs to `C i`. The main
  application of this is with `C i = {s : Set (α i) | MeasurableSet s}`.
* `measurableCylinders`: set of all cylinders with measurable base sets.
* `cylinderEvents Δ`: The σ-algebra of cylinder events on `Δ`. It is the smallest σ-algebra making
  the projections on the `i`-th coordinate continuous for all `i ∈ Δ`.

## Main statements

* `generateFrom_squareCylinders`: square cylinders formed from measurable sets generate the product
  σ-algebra
* `generateFrom_measurableCylinders`: cylinders formed from measurable sets generate the
  product σ-algebra

-/

open Function Set

namespace MeasureTheory

variable {ι : Type _} {α : ι → Type _}

section squareCylinders

/-- Given a finite set `s` of indices, a square cylinder is the product of a set `S` of
`∀ i : s, α i` and of `univ` on the other indices. The set `S` is a product of sets `t i` such that
for all `i : s`, `t i ∈ C i`.
`squareCylinders` is the set of all such squareCylinders. -/
def squareCylinders (C : ∀ i, Set (Set (α i))) : Set (Set (∀ i, α i)) :=
  {S | ∃ s : Finset ι, ∃ t ∈ univ.pi C, S = (s : Set ι).pi t}

theorem squareCylinders_eq_iUnion_image (C : ∀ i, Set (Set (α i))) :
    squareCylinders C = ⋃ s : Finset ι, (fun t ↦ (s : Set ι).pi t) '' univ.pi C := by
  ext1 f
  simp only [squareCylinders, mem_iUnion, mem_image, mem_univ_pi, exists_prop, mem_setOf_eq,
    eq_comm (a := f)]

theorem isPiSystem_squareCylinders {C : ∀ i, Set (Set (α i))} (hC : ∀ i, IsPiSystem (C i))
    (hC_univ : ∀ i, univ ∈ C i) :
    IsPiSystem (squareCylinders C) := by
  rintro S₁ ⟨s₁, t₁, h₁, rfl⟩ S₂ ⟨s₂, t₂, h₂, rfl⟩ hst_nonempty
  classical
  let t₁' := s₁.piecewise t₁ (fun i ↦ univ)
  let t₂' := s₂.piecewise t₂ (fun i ↦ univ)
  have h1 : ∀ i ∈ (s₁ : Set ι), t₁ i = t₁' i :=
    fun i hi ↦ (Finset.piecewise_eq_of_mem _ _ _ hi).symm
  have h1' : ∀ i ∉ (s₁ : Set ι), t₁' i = univ :=
    fun i hi ↦ Finset.piecewise_eq_of_notMem _ _ _ hi
  have h2 : ∀ i ∈ (s₂ : Set ι), t₂ i = t₂' i :=
    fun i hi ↦ (Finset.piecewise_eq_of_mem _ _ _ hi).symm
  have h2' : ∀ i ∉ (s₂ : Set ι), t₂' i = univ :=
    fun i hi ↦ Finset.piecewise_eq_of_notMem _ _ _ hi
  rw [Set.pi_congr rfl h1, Set.pi_congr rfl h2, ← union_pi_inter h1' h2']
  refine ⟨s₁ ∪ s₂, fun i ↦ t₁' i ∩ t₂' i, ?_, ?_⟩
  · rw [mem_univ_pi]
    intro i
    have : (t₁' i ∩ t₂' i).Nonempty := by
      obtain ⟨f, hf⟩ := hst_nonempty
      rw [Set.pi_congr rfl h1, Set.pi_congr rfl h2, mem_inter_iff, mem_pi, mem_pi] at hf
      refine ⟨f i, ⟨?_, ?_⟩⟩
      · by_cases hi₁ : i ∈ s₁
        · exact hf.1 i hi₁
        · rw [h1' i hi₁]
          exact mem_univ _
      · by_cases hi₂ : i ∈ s₂
        · exact hf.2 i hi₂
        · rw [h2' i hi₂]
          exact mem_univ _
    refine hC i _ ?_ _ ?_ this
    · by_cases hi₁ : i ∈ s₁
      · rw [← h1 i hi₁]
        exact h₁ i (mem_univ _)
      · rw [h1' i hi₁]
        exact hC_univ i
    · by_cases hi₂ : i ∈ s₂
      · rw [← h2 i hi₂]
        exact h₂ i (mem_univ _)
      · rw [h2' i hi₂]
        exact hC_univ i
  · rw [Finset.coe_union]

theorem comap_eval_le_generateFrom_squareCylinders_singleton
    (α : ι → Type*) [m : ∀ i, MeasurableSpace (α i)] (i : ι) :
    MeasurableSpace.comap (Function.eval i) (m i) ≤
      MeasurableSpace.generateFrom
        ((fun t ↦ ({i} : Set ι).pi t) '' univ.pi fun i ↦ {s : Set (α i) | MeasurableSet s}) := by
  simp only [Function.eval, singleton_pi]
  rw [MeasurableSpace.comap_eq_generateFrom]
  refine MeasurableSpace.generateFrom_mono fun S ↦ ?_
  simp only [mem_setOf_eq, mem_image, mem_univ_pi, forall_exists_index, and_imp]
  intro t ht h
  classical
  refine ⟨fun j ↦ if hji : j = i then by convert t else univ, fun j ↦ ?_, ?_⟩
  · by_cases hji : j = i
    · simp only [hji, eq_self_iff_true, eq_mpr_eq_cast, dif_pos]
      convert ht
      simp only [id_eq, cast_heq]
    · simp only [hji, not_false_iff, dif_neg, MeasurableSet.univ]
  · simp only [id_eq, eq_mpr_eq_cast, ← h]
    ext1 x
    simp only [singleton_pi, Function.eval, cast_eq, dite_eq_ite, ite_true, mem_preimage]

/-- The square cylinders formed from measurable sets generate the product σ-algebra. -/
theorem generateFrom_squareCylinders [∀ i, MeasurableSpace (α i)] :
    MeasurableSpace.generateFrom (squareCylinders fun i ↦ {s : Set (α i) | MeasurableSet s}) =
      MeasurableSpace.pi := by
  apply le_antisymm
  · rw [MeasurableSpace.generateFrom_le_iff]
    rintro S ⟨s, t, h, rfl⟩
    simp only [mem_univ_pi, mem_setOf_eq] at h
    exact MeasurableSet.pi (Finset.countable_toSet _) (fun i _ ↦ h i)
  · refine iSup_le fun i ↦ ?_
    refine (comap_eval_le_generateFrom_squareCylinders_singleton α i).trans ?_
    refine MeasurableSpace.generateFrom_mono ?_
    rw [← Finset.coe_singleton, squareCylinders_eq_iUnion_image]
    exact subset_iUnion
      (fun (s : Finset ι) ↦
        (fun t : ∀ i, Set (α i) ↦ (s : Set ι).pi t) '' univ.pi (fun i ↦ setOf MeasurableSet))
      ({i} : Finset ι)

end squareCylinders

section cylinder

/-- Given a finite set `s` of indices, a cylinder is the preimage of a set `S` of `∀ i : s, α i` by
the projection from `∀ i, α i` to `∀ i : s, α i`. -/
def cylinder (s : Finset ι) (S : Set (∀ i : s, α i)) : Set (∀ i, α i) :=
  s.restrict ⁻¹' S

@[simp]
theorem mem_cylinder (s : Finset ι) (S : Set (∀ i : s, α i)) (f : ∀ i, α i) :
    f ∈ cylinder s S ↔ s.restrict f ∈ S :=
  mem_preimage

@[simp]
theorem cylinder_empty (s : Finset ι) : cylinder s (∅ : Set (∀ i : s, α i)) = ∅ := by
  rw [cylinder, preimage_empty]

@[simp]
theorem cylinder_univ (s : Finset ι) : cylinder s (univ : Set (∀ i : s, α i)) = univ := by
  rw [cylinder, preimage_univ]

@[simp]
theorem cylinder_eq_empty_iff [h_nonempty : Nonempty (∀ i, α i)] (s : Finset ι)
    (S : Set (∀ i : s, α i)) :
    cylinder s S = ∅ ↔ S = ∅ := by
  refine ⟨fun h ↦ ?_, fun h ↦ by (rw [h]; exact cylinder_empty _)⟩
  by_contra hS
  rw [← Ne, ← nonempty_iff_ne_empty] at hS
  let f := hS.some
  have hf : f ∈ S := hS.choose_spec
  classical
  let f' : ∀ i, α i := fun i ↦ if hi : i ∈ s then f ⟨i, hi⟩ else h_nonempty.some i
  have hf' : f' ∈ cylinder s S := by
    rw [mem_cylinder]
    simpa only [Finset.restrict_def, Finset.coe_mem, dif_pos, f']
  rw [h] at hf'
  exact notMem_empty _ hf'

theorem inter_cylinder (s₁ s₂ : Finset ι) (S₁ : Set (∀ i : s₁, α i)) (S₂ : Set (∀ i : s₂, α i))
    [DecidableEq ι] :
    cylinder s₁ S₁ ∩ cylinder s₂ S₂ =
      cylinder (s₁ ∪ s₂)
        (Finset.restrict₂ Finset.subset_union_left ⁻¹' S₁ ∩
          Finset.restrict₂ Finset.subset_union_right ⁻¹' S₂) := by
  ext1 f; simp only [mem_inter_iff, mem_cylinder, mem_setOf_eq]; rfl

theorem inter_cylinder_same (s : Finset ι) (S₁ : Set (∀ i : s, α i)) (S₂ : Set (∀ i : s, α i)) :
    cylinder s S₁ ∩ cylinder s S₂ = cylinder s (S₁ ∩ S₂) := by
  classical rw [inter_cylinder]; rfl

theorem union_cylinder (s₁ s₂ : Finset ι) (S₁ : Set (∀ i : s₁, α i)) (S₂ : Set (∀ i : s₂, α i))
    [DecidableEq ι] :
    cylinder s₁ S₁ ∪ cylinder s₂ S₂ =
      cylinder (s₁ ∪ s₂)
        (Finset.restrict₂ Finset.subset_union_left ⁻¹' S₁ ∪
          Finset.restrict₂ Finset.subset_union_right ⁻¹' S₂) := by
  ext1 f; simp only [mem_union, mem_cylinder, mem_setOf_eq]; rfl

theorem union_cylinder_same (s : Finset ι) (S₁ : Set (∀ i : s, α i)) (S₂ : Set (∀ i : s, α i)) :
    cylinder s S₁ ∪ cylinder s S₂ = cylinder s (S₁ ∪ S₂) := by
  classical rw [union_cylinder]; rfl

theorem compl_cylinder (s : Finset ι) (S : Set (∀ i : s, α i)) :
    (cylinder s S)ᶜ = cylinder s (Sᶜ) := by
  ext1 f; simp only [mem_compl_iff, mem_cylinder]

theorem diff_cylinder_same (s : Finset ι) (S T : Set (∀ i : s, α i)) :
    cylinder s S \ cylinder s T = cylinder s (S \ T) := by
  ext1 f; simp only [mem_diff, mem_cylinder]

theorem eq_of_cylinder_eq_of_subset [h_nonempty : Nonempty (∀ i, α i)] {I J : Finset ι}
    {S : Set (∀ i : I, α i)} {T : Set (∀ i : J, α i)} (h_eq : cylinder I S = cylinder J T)
    (hJI : J ⊆ I) :
    S = Finset.restrict₂ hJI ⁻¹' T := by
  rw [Set.ext_iff] at h_eq
  simp only [mem_cylinder] at h_eq
  ext1 f
  simp only [mem_preimage]
  classical
  specialize h_eq fun i ↦ if hi : i ∈ I then f ⟨i, hi⟩ else h_nonempty.some i
  have h_mem : ∀ j : J, ↑j ∈ I := fun j ↦ hJI j.prop
  simpa only [Finset.restrict_def, Finset.coe_mem, dite_true, h_mem] using h_eq

theorem cylinder_eq_cylinder_union [DecidableEq ι] (I : Finset ι) (S : Set (∀ i : I, α i))
    (J : Finset ι) :
    cylinder I S =
      cylinder (I ∪ J) (Finset.restrict₂ Finset.subset_union_left ⁻¹' S) := by
  ext1 f; simp only [mem_cylinder, Finset.restrict_def, Finset.restrict₂_def, mem_preimage]

theorem disjoint_cylinder_iff [Nonempty (∀ i, α i)] {s t : Finset ι} {S : Set (∀ i : s, α i)}
    {T : Set (∀ i : t, α i)} [DecidableEq ι] :
    Disjoint (cylinder s S) (cylinder t T) ↔
      Disjoint
        (Finset.restrict₂ Finset.subset_union_left ⁻¹' S)
        (Finset.restrict₂ Finset.subset_union_right ⁻¹' T) := by
  simp_rw [Set.disjoint_iff, subset_empty_iff, inter_cylinder, cylinder_eq_empty_iff]

theorem IsClosed.cylinder [∀ i, TopologicalSpace (α i)] (s : Finset ι) {S : Set (∀ i : s, α i)}
    (hs : IsClosed S) : IsClosed (cylinder s S) :=
  hs.preimage (continuous_pi fun _ ↦ continuous_apply _)

theorem _root_.MeasurableSet.cylinder [∀ i, MeasurableSpace (α i)] (s : Finset ι)
    {S : Set (∀ i : s, α i)} (hS : MeasurableSet S) :
    MeasurableSet (cylinder s S) :=
  measurable_pi_lambda _ (fun _ ↦ measurable_pi_apply _) hS

/-- The indicator of a cylinder only depends on the variables whose the cylinder depends on. -/
theorem dependsOn_cylinder_indicator_const {M : Type*} [Zero M] {I : Finset ι}
    (S : Set (Π i : I, α i)) (c : M) :
    DependsOn ((cylinder I S).indicator (fun _ ↦ c)) I :=
  fun x y hxy ↦ Set.indicator_const_eq_indicator_const (by simp [Finset.restrict_def, hxy])

end cylinder

section cylinders

/-- Given a finite set `s` of indices, a cylinder is the preimage of a set `S` of `∀ i : s, α i` by
the projection from `∀ i, α i` to `∀ i : s, α i`.
`measurableCylinders` is the set of all cylinders with measurable base `S`. -/
def measurableCylinders (α : ι → Type*) [∀ i, MeasurableSpace (α i)] : Set (Set (∀ i, α i)) :=
  ⋃ (s) (S) (_ : MeasurableSet S), {cylinder s S}

theorem empty_mem_measurableCylinders (α : ι → Type*) [∀ i, MeasurableSpace (α i)] :
    ∅ ∈ measurableCylinders α := by
  simp_rw [measurableCylinders, mem_iUnion, mem_singleton_iff]
  exact ⟨∅, ∅, MeasurableSet.empty, (cylinder_empty _).symm⟩

variable [∀ i, MeasurableSpace (α i)] {s t : Set (∀ i, α i)}

@[simp]
theorem mem_measurableCylinders (t : Set (∀ i, α i)) :
    t ∈ measurableCylinders α ↔ ∃ s S, MeasurableSet S ∧ t = cylinder s S := by
  simp_rw [measurableCylinders, mem_iUnion, exists_prop, mem_singleton_iff]

@[measurability]
theorem _root_.MeasurableSet.of_mem_measurableCylinders {s : Set (Π i, α i)}
    (hs : s ∈ measurableCylinders α) : MeasurableSet s := by
  obtain ⟨I, t, mt, rfl⟩ := (mem_measurableCylinders s).1 hs
  exact mt.cylinder

/-- A finset `s` such that `t = cylinder s S`. `S` is given by `measurableCylinders.set`. -/
noncomputable def measurableCylinders.finset (ht : t ∈ measurableCylinders α) : Finset ι :=
  ((mem_measurableCylinders t).mp ht).choose

/-- A set `S` such that `t = cylinder s S`. `s` is given by `measurableCylinders.finset`. -/
def measurableCylinders.set (ht : t ∈ measurableCylinders α) :
    Set (∀ i : measurableCylinders.finset ht, α i) :=
  ((mem_measurableCylinders t).mp ht).choose_spec.choose

theorem measurableCylinders.measurableSet (ht : t ∈ measurableCylinders α) :
    MeasurableSet (measurableCylinders.set ht) :=
  ((mem_measurableCylinders t).mp ht).choose_spec.choose_spec.left

theorem measurableCylinders.eq_cylinder (ht : t ∈ measurableCylinders α) :
    t = cylinder (measurableCylinders.finset ht) (measurableCylinders.set ht) :=
  ((mem_measurableCylinders t).mp ht).choose_spec.choose_spec.right

theorem cylinder_mem_measurableCylinders (s : Finset ι) (S : Set (∀ i : s, α i))
    (hS : MeasurableSet S) :
    cylinder s S ∈ measurableCylinders α := by
  rw [mem_measurableCylinders]; exact ⟨s, S, hS, rfl⟩

theorem inter_mem_measurableCylinders (hs : s ∈ measurableCylinders α)
    (ht : t ∈ measurableCylinders α) :
    s ∩ t ∈ measurableCylinders α := by
  rw [mem_measurableCylinders] at *
  obtain ⟨s₁, S₁, hS₁, rfl⟩ := hs
  obtain ⟨s₂, S₂, hS₂, rfl⟩ := ht
  classical
  refine ⟨s₁ ∪ s₂,
    Finset.restrict₂ Finset.subset_union_left ⁻¹' S₁ ∩
      {f | Finset.restrict₂ Finset.subset_union_right f ∈ S₂}, ?_, ?_⟩
  · refine MeasurableSet.inter ?_ ?_
    · exact measurable_pi_lambda _ (fun _ ↦ measurable_pi_apply _) hS₁
    · exact measurable_pi_lambda _ (fun _ ↦ measurable_pi_apply _) hS₂
  · exact inter_cylinder _ _ _ _

theorem isPiSystem_measurableCylinders : IsPiSystem (measurableCylinders α) :=
  fun _ hS _ hT _ ↦ inter_mem_measurableCylinders hS hT

theorem compl_mem_measurableCylinders (hs : s ∈ measurableCylinders α) :
    sᶜ ∈ measurableCylinders α := by
  rw [mem_measurableCylinders] at hs ⊢
  obtain ⟨s, S, hS, rfl⟩ := hs
  refine ⟨s, Sᶜ, hS.compl, ?_⟩
  rw [compl_cylinder]

theorem univ_mem_measurableCylinders (α : ι → Type*) [∀ i, MeasurableSpace (α i)] :
    Set.univ ∈ measurableCylinders α := by
  rw [← compl_empty]; exact compl_mem_measurableCylinders (empty_mem_measurableCylinders α)

theorem union_mem_measurableCylinders (hs : s ∈ measurableCylinders α)
    (ht : t ∈ measurableCylinders α) :
    s ∪ t ∈ measurableCylinders α := by
  rw [union_eq_compl_compl_inter_compl]
  exact compl_mem_measurableCylinders (inter_mem_measurableCylinders
    (compl_mem_measurableCylinders hs) (compl_mem_measurableCylinders ht))

theorem diff_mem_measurableCylinders (hs : s ∈ measurableCylinders α)
    (ht : t ∈ measurableCylinders α) :
    s \ t ∈ measurableCylinders α := by
  rw [diff_eq_compl_inter]
  exact inter_mem_measurableCylinders (compl_mem_measurableCylinders ht) hs

/-- The measurable cylinders generate the product σ-algebra. -/
theorem generateFrom_measurableCylinders :
    MeasurableSpace.generateFrom (measurableCylinders α) = MeasurableSpace.pi := by
  apply le_antisymm
  · refine MeasurableSpace.generateFrom_le (fun S hS ↦ ?_)
    obtain ⟨s, S, hSm, rfl⟩ := (mem_measurableCylinders _).mp hS
    exact hSm.cylinder
  · refine iSup_le fun i ↦ ?_
    refine (comap_eval_le_generateFrom_squareCylinders_singleton α i).trans ?_
    refine MeasurableSpace.generateFrom_mono (fun x ↦ ?_)
    simp only [singleton_pi, Function.eval, mem_image, mem_pi, mem_univ, mem_setOf_eq,
      forall_true_left, mem_measurableCylinders, exists_prop, forall_exists_index, and_imp]
    rintro t ht rfl
    refine ⟨{i}, {f | f ⟨i, Finset.mem_singleton_self i⟩ ∈ t i}, measurable_pi_apply _ (ht i), ?_⟩
    ext1 x
    simp only [mem_preimage, Function.eval, mem_cylinder, mem_setOf_eq, Finset.restrict]

/-- The cylinders of a product space indexed by `ℕ` can be seen as depending on the first
coordinates. -/
theorem measurableCylinders_nat {X : ℕ → Type*} [∀ n, MeasurableSpace (X n)] :
    measurableCylinders X = ⋃ (a) (S) (_ : MeasurableSet S), {cylinder (Finset.Iic a) S} := by
  ext s
  simp only [mem_measurableCylinders, exists_prop, mem_iUnion, mem_singleton]
  refine ⟨?_, fun ⟨N, S, mS, s_eq⟩ ↦ ⟨Finset.Iic N, S, mS, s_eq⟩⟩
  rintro ⟨t, S, mS, rfl⟩
  refine ⟨t.sup id, Finset.restrict₂ t.subset_Iic_sup_id ⁻¹' S,
    Finset.measurable_restrict₂ _ mS, ?_⟩
  unfold cylinder
  rw [← preimage_comp, Finset.restrict₂_comp_restrict]
  exact mem_singleton _

end cylinders

/-! ### Cylinder events as a sigma-algebra -/

section cylinderEvents

variable {α ι : Type*} {X : ι → Type*} {mα : MeasurableSpace α} [m : ∀ i, MeasurableSpace (X i)]
  {Δ Δ₁ Δ₂ : Set ι} {i : ι}

/-- The σ-algebra of cylinder events on `Δ`. It is the smallest σ-algebra making the projections
on the `i`-th coordinate measurable for all `i ∈ Δ`. -/
def cylinderEvents (Δ : Set ι) : MeasurableSpace (∀ i, X i) := ⨆ i ∈ Δ, (m i).comap fun σ ↦ σ i

@[simp] lemma cylinderEvents_univ : cylinderEvents (X := X) univ = MeasurableSpace.pi := by
  simp [cylinderEvents, MeasurableSpace.pi]

@[gcongr]
lemma cylinderEvents_mono (h : Δ₁ ⊆ Δ₂) : cylinderEvents (X := X) Δ₁ ≤ cylinderEvents Δ₂ :=
  biSup_mono h

lemma cylinderEvents_le_pi : cylinderEvents (X := X) Δ ≤ MeasurableSpace.pi := by
  simpa using cylinderEvents_mono (subset_univ _)

lemma measurable_cylinderEvents_iff {g : α → ∀ i, X i} :
    @Measurable _ _ _ (cylinderEvents Δ) g ↔ ∀ ⦃i⦄, i ∈ Δ → Measurable fun a ↦ g a i := by
  simp_rw [measurable_iff_comap_le, cylinderEvents, MeasurableSpace.comap_iSup,
    MeasurableSpace.comap_comp, Function.comp_def, iSup_le_iff]

@[fun_prop, aesop safe 100 apply (rule_sets := [Measurable])]
lemma measurable_cylinderEvent_apply (hi : i ∈ Δ) :
    Measurable[cylinderEvents Δ] fun f : ∀ i, X i => f i :=
  measurable_cylinderEvents_iff.1 measurable_id hi

@[aesop safe 100 apply (rule_sets := [Measurable])]
lemma Measurable.eval_cylinderEvents {g : α → ∀ i, X i} (hi : i ∈ Δ)
    (hg : @Measurable _ _ _ (cylinderEvents Δ) g) : Measurable fun a ↦ g a i :=
  (measurable_cylinderEvent_apply hi).comp hg

@[fun_prop, aesop safe 100 apply (rule_sets := [Measurable])]
lemma measurable_cylinderEvents_lambda (f : α → ∀ i, X i) (hf : ∀ i, Measurable fun a ↦ f a i) :
    Measurable f :=
  measurable_pi_iff.mpr hf

/-- The function `(f, x) ↦ update f a x : (Π a, X a) × X a → Π a, X a` is measurable. -/
lemma measurable_update_cylinderEvents' [DecidableEq ι] :
    @Measurable _ _ (.prod (cylinderEvents Δ) (m i)) (cylinderEvents Δ)
      (fun p : (∀ i, X i) × X i ↦ update p.1 i p.2) := by
  rw [measurable_cylinderEvents_iff]
  intro j hj
  dsimp [update]
  split_ifs with h
  · subst h
    dsimp
    exact measurable_snd
  · exact measurable_cylinderEvents_iff.1 measurable_fst hj

lemma measurable_uniqueElim_cylinderEvents [Unique ι] :
    Measurable (uniqueElim : X (default : ι) → ∀ i, X i) := by
  simp_rw [measurable_pi_iff, Unique.forall_iff, uniqueElim_default]; exact measurable_id

/-- The function `update f a : X a → Π a, X a` is always measurable.
This doesn't require `f` to be measurable.
This should not be confused with the statement that `update f a x` is measurable. -/
@[measurability]
lemma measurable_update_cylinderEvents (f : ∀ a : ι, X a) {a : ι} [DecidableEq ι] :
    @Measurable _ _ _ (cylinderEvents Δ) (update f a) :=
  measurable_update_cylinderEvents'.comp measurable_prodMk_left

lemma measurable_update_cylinderEvents_left {a : ι} [DecidableEq ι] {x : X a} :
    @Measurable _ _ (cylinderEvents Δ) (cylinderEvents Δ) (update · a x) :=
  measurable_update_cylinderEvents'.comp measurable_prodMk_right

lemma measurable_restrict_cylinderEvents (Δ : Set ι) :
    Measurable[cylinderEvents (X := X) Δ] (restrict Δ) := by
  rw [@measurable_pi_iff]; exact fun i ↦ measurable_cylinderEvent_apply i.2

end cylinderEvents
end MeasureTheory
