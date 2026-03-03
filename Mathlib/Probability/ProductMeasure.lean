/-
Copyright (c) 2025 Etienne Marion. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Etienne Marion
-/
module

public import Mathlib.Probability.Kernel.Composition.MeasureComp
public import Mathlib.Probability.Kernel.IonescuTulcea.Traj

/-!
# Infinite product of probability measures

This file provides a definition for the product measure of an arbitrary family of probability
measures. Given `μ : (i : ι) → Measure (X i)` such that each `μ i` is a probability measure,
`Measure.infinitePi μ` is the only probability measure `ν` over `Π i, X i` such that
`ν (Set.pi s t) = ∏ i ∈ s, μ i (t i)`, with `s : Finset ι` and
such that `∀ i ∈ s, MeasurableSet (t i)` (see `eq_infinitePi` and `infinitePi_pi`).
We also provide a few results regarding integration against this measure.

## Main definition

* `Measure.infinitePi μ`: The product measure of the family of probability measures `μ`.

## Main statements

* `eq_infinitePi`: Any measure which gives to a finite product of sets the mass which is the
  product of their measures is the product measure.
* `infinitePi_pi`: the product measure gives to finite products of sets a mass which is
  the product of their masses.
* `infinitePi_cylinder`: `infinitePi μ (cylinder s S) = Measure.pi (fun i : s ↦ μ i) S`

## Implementation notes

To construct the product measure we first use the kernel `traj` obtained via the Ionescu-Tulcea
theorem to construct the measure over a product indexed by `ℕ`, which is `infinitePiNat`. This
is an implementation detail and should not be used directly. Then we construct the product measure
over an arbitrary type by extending `piContent μ` thanks to Carathéodory's theorem. The key lemma
to do so is `piContent_tendsto_zero`, which states that `piContent μ (A n)` tends to zero if
`A` is a nonincreasing sequence of sets satisfying `⋂ n, A n = ∅`.
We prove this lemma by reducing to the case of an at most countable product,
in which case `piContent μ` is known to be a true measure (see `piContent_eq_measure_pi` and
`piContent_eq_infinitePiNat`).

## Tags

infinite product measure
-/

@[expose] public section

open ProbabilityTheory Finset Filter Preorder MeasurableEquiv

open scoped ENNReal Topology

namespace MeasureTheory

section Preliminaries

variable {ι : Type*} {X : ι → Type*} {mX : ∀ i, MeasurableSpace (X i)}
variable (μ : (i : ι) → Measure (X i)) [hμ : ∀ i, IsProbabilityMeasure (μ i)]

/-- Consider a family of probability measures. You can take their products for any finite
subfamily. This gives a projective family of measures. -/
lemma isProjectiveMeasureFamily_pi :
    IsProjectiveMeasureFamily (fun I : Finset ι ↦ (Measure.pi (fun i : I ↦ μ i))) := by
  refine fun I J hJI ↦ Measure.pi_eq (fun s ms ↦ ?_)
  classical
  simp_rw [Measure.map_apply (measurable_restrict₂ hJI) (.univ_pi ms), restrict₂_preimage hJI,
    Measure.pi_pi, prod_eq_prod_extend]
  refine (prod_subset_one_on_sdiff hJI (fun x hx ↦ ?_) (fun x hx ↦ ?_)).symm
  · rw [Function.extend_val_apply (mem_sdiff.1 hx).1, dif_neg (mem_sdiff.1 hx).2, measure_univ]
  · rw [Function.extend_val_apply hx, Function.extend_val_apply (hJI hx), dif_pos hx]

/-- Consider a family of probability measures. You can take their products for any finite
subfamily. This gives an additive content on the measurable cylinders. -/
noncomputable def piContent : AddContent ℝ≥0∞ (measurableCylinders X) :=
  projectiveFamilyContent (isProjectiveMeasureFamily_pi μ)

lemma piContent_cylinder {I : Finset ι} {S : Set (Π i : I, X i)} (hS : MeasurableSet S) :
    piContent μ (cylinder I S) = Measure.pi (fun i : I ↦ μ i) S :=
  projectiveFamilyContent_cylinder _ hS

theorem piContent_eq_measure_pi [Fintype ι] {s : Set (Π i, X i)} (hs : MeasurableSet s) :
    piContent μ s = Measure.pi μ s := by
  let e : @Finset.univ ι _ ≃ ι :=
    { toFun i := i
      invFun i := ⟨i, mem_univ i⟩ }
  have : s = cylinder univ (MeasurableEquiv.piCongrLeft X e ⁻¹' s) := rfl
  nth_rw 1 [this]
  dsimp [e]
  rw [piContent_cylinder _ (hs.preimage (by fun_prop)), ← Measure.pi_map_piCongrLeft e,
    ← Measure.map_apply (by fun_prop) hs]; rfl

end Preliminaries

section Nat

open Kernel

/-! ### Product of measures indexed by `ℕ` -/

variable {X : ℕ → Type*}

variable {mX : ∀ n, MeasurableSpace (X n)}
  (μ : (n : ℕ) → Measure (X n)) [hμ : ∀ n, IsProbabilityMeasure (μ n)]

namespace Measure

/-- Infinite product measure indexed by `ℕ`. This is an auxiliary construction, you should use
the generic product measure `Measure.infinitePi`. -/
noncomputable def infinitePiNat : Measure (Π n, X n) :=
  (traj (fun n ↦ const _ (μ (n + 1))) 0) ∘ₘ (Measure.pi (fun i : Iic 0 ↦ μ i))

instance : IsProbabilityMeasure (Measure.infinitePiNat μ) := by
  rw [Measure.infinitePiNat]; infer_instance

/-- Let `μ : (i : Ioc a c) → Measure (X i)` be a family of measures. Up to an equivalence,
`(⨂ i : Ioc a b, μ i) ⊗ (⨂ i : Ioc b c, μ i) = ⨂ i : Ioc a c, μ i`, where `⊗` denotes the
product of measures. -/
lemma pi_prod_map_IocProdIoc {a b c : ℕ} (hab : a ≤ b) (hbc : b ≤ c) :
    ((Measure.pi (fun i : Ioc a b ↦ μ i)).prod (Measure.pi (fun i : Ioc b c ↦ μ i))).map
      (IocProdIoc a b c) = Measure.pi (fun i : Ioc a c ↦ μ i) := by
  refine (Measure.pi_eq fun s ms ↦ ?_).symm
  simp_rw [Measure.map_apply measurable_IocProdIoc (.univ_pi ms), IocProdIoc_preimage hab hbc,
    Measure.prod_prod, Measure.pi_pi, prod_eq_prod_extend]
  nth_rw 1 [Eq.comm, ← Ioc_union_Ioc_eq_Ioc hab hbc, prod_union (Ioc_disjoint_Ioc_of_le le_rfl)]
  congr 1 <;> refine prod_congr rfl fun x hx ↦ ?_
  · rw [Function.extend_val_apply hx, Function.extend_val_apply (Ioc_subset_Ioc_right hbc hx),
      restrict₂]
  · rw [Function.extend_val_apply hx, Function.extend_val_apply (Ioc_subset_Ioc_left hab hx),
      restrict₂]

/-- Let `μ : (i : Iic b) → Measure (X i)` be a family of measures. Up to an equivalence,
`(⨂ i : Iic a, μ i) ⊗ (⨂ i : Ioc a b, μ i) = ⨂ i : Iic b, μ i`, where `⊗` denotes the
product of measures. -/
lemma pi_prod_map_IicProdIoc {a b : ℕ} :
    ((Measure.pi (fun i : Iic a ↦ μ i)).prod (Measure.pi (fun i : Ioc a b ↦ μ i))).map
      (IicProdIoc a b) = Measure.pi (fun i : Iic b ↦ μ i) := by
  obtain hab | hba := le_total a b
  · refine (Measure.pi_eq fun s ms ↦ ?_).symm
    simp_rw [Measure.map_apply measurable_IicProdIoc (.univ_pi ms), IicProdIoc_preimage hab,
      Measure.prod_prod, Measure.pi_pi, prod_eq_prod_extend]
    nth_rw 1 [Eq.comm, ← Iic_union_Ioc_eq_Iic hab, prod_union (Iic_disjoint_Ioc le_rfl)]
    congr 1 <;> refine prod_congr rfl fun x hx ↦ ?_
    · rw [Function.extend_val_apply hx, Function.extend_val_apply (Iic_subset_Iic.2 hab hx),
        frestrictLe₂, restrict₂]
    · rw [Function.extend_val_apply hx, Function.extend_val_apply (Ioc_subset_Iic_self hx),
        restrict₂]
  · rw [IicProdIoc_le hba, ← Measure.map_map, ← Measure.fst, Measure.fst_prod]
    · exact isProjectiveMeasureFamily_pi μ (Iic a) (Iic b) (Iic_subset_Iic.2 hba) |>.symm
    all_goals fun_prop

/-- Let `μ (i + 1) : Measure (X (i + 1))` be a measure. Up to an equivalence,
`μ i = ⨂ j : Ioc i (i + 1), μ i`, where `⊗` denotes the product of measures. -/
lemma map_piSingleton (μ : (n : ℕ) → Measure (X n)) [∀ n, SigmaFinite (μ n)] (n : ℕ) :
    (μ (n + 1)).map (piSingleton n) = Measure.pi (fun i : Ioc n (n + 1) ↦ μ i) := by
  refine (Measure.pi_eq fun s hs ↦ ?_).symm
  have : Subsingleton (Ioc n (n + 1)) := by rw [Nat.Ioc_succ_singleton]; infer_instance
  rw [Fintype.prod_subsingleton _ ⟨n + 1, mem_Ioc.2 (by lia)⟩,
    Measure.map_apply (by fun_prop) (.univ_pi hs)]
  congr 1 with x
  simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_const, Subtype.forall,
    Nat.Ioc_succ_singleton, mem_singleton]
  exact ⟨fun h ↦ h (n + 1) rfl, fun h a b ↦ b.symm ▸ h⟩

end Measure

/-- `partialTraj κ a b` is a kernel which up to an equivalence is equal to
`Kernel.id ×ₖ (κ a ⊗ₖ ... ⊗ₖ κ (b - 1))`. This lemma therefore states that if the kernels `κ`
are constant then their composition-product is the product measure. -/
theorem partialTraj_const_restrict₂ {a b : ℕ} :
    (partialTraj (fun n ↦ const _ (μ (n + 1))) a b).map (restrict₂ Ioc_subset_Iic_self) =
    const _ (Measure.pi (fun i : Ioc a b ↦ μ i)) := by
  obtain hab | hba := lt_or_ge a b
  · refine Nat.le_induction ?_ (fun n hn hind ↦ ?_) b (Nat.succ_le_of_lt hab) <;> ext1 x₀
    · rw [partialTraj_succ_self, ← map_comp_right, map_apply, prod_apply, map_apply, const_apply,
        const_apply, Measure.map_piSingleton, restrict₂_comp_IicProdIoc, Measure.map_snd_prod,
        measure_univ, one_smul]
      all_goals fun_prop
    · have : (restrict₂ (Ioc_subset_Iic_self (a := a))) ∘ (IicProdIoc (X := X) n (n + 1)) =
          (IocProdIoc a n (n + 1)) ∘ (Prod.map (restrict₂ Ioc_subset_Iic_self) id) := rfl
      rw [const_apply, partialTraj_succ_of_le (by lia), map_const, prod_const_comp, id_comp,
        ← map_comp_right, this, map_comp_right, ← map_prod_map, hind, Kernel.map_id, map_apply,
        prod_apply, const_apply, const_apply, Measure.map_piSingleton,
        Measure.pi_prod_map_IocProdIoc]
      any_goals fun_prop
      all_goals lia
  · have : IsEmpty (Ioc a b) := by simpa [hba] using Subtype.isEmpty_false
    ext x s ms
    by_cases hs : s.Nonempty
    · rw [Subsingleton.eq_univ_of_nonempty hs, @measure_univ .., measure_univ]
      exact (IsMarkovKernel.map _ (measurable_restrict₂ _)) |>.isProbabilityMeasure x
    · rw [Set.not_nonempty_iff_eq_empty.1 hs]
      simp

/-- `partialTraj κ a b` is a kernel which up to an equivalence is equal to
`Kernel.id ×ₖ (κ a ⊗ₖ ... ⊗ₖ κ (b - 1))`. This lemma therefore states that if the kernel `κ i`
is constant equal to `μ i` for all `i`, then up to an equivalence
`partialTraj κ a b = Kernel.id ×ₖ Kernel.const (⨂ μ i)`. -/
theorem partialTraj_const {a b : ℕ} :
    partialTraj (fun n ↦ const _ (μ (n + 1))) a b =
      (Kernel.id ×ₖ (const _ (Measure.pi (fun i : Ioc a b ↦ μ i)))).map (IicProdIoc a b) := by
  rw [partialTraj_eq_prod, partialTraj_const_restrict₂]

namespace Measure

theorem isProjectiveLimit_infinitePiNat :
    IsProjectiveLimit (infinitePiNat μ) (fun I : Finset ℕ ↦ (Measure.pi (fun i : I ↦ μ i))) := by
  intro I
  rw [isProjectiveMeasureFamily_pi μ _ _ I.subset_Iic_sup_id,
    ← restrict₂_comp_restrict I.subset_Iic_sup_id, ← map_map, ← frestrictLe, infinitePiNat,
    map_comp, traj_map_frestrictLe, partialTraj_const, ← map_comp, ← compProd_eq_comp_prod,
    compProd_const, pi_prod_map_IicProdIoc]
  all_goals fun_prop

/-- Restricting the product measure to a product indexed by a finset yields the usual
product measure. -/
lemma infinitePiNat_map_restrict (I : Finset ℕ) :
    (infinitePiNat μ).map I.restrict = Measure.pi fun i : I ↦ μ i :=
  isProjectiveLimit_infinitePiNat μ I

theorem piContent_eq_infinitePiNat {A : Set (Π n, X n)} (hA : A ∈ measurableCylinders X) :
    piContent μ A = infinitePiNat μ A := by
  obtain ⟨s, S, mS, rfl⟩ : ∃ s S, MeasurableSet S ∧ A = cylinder s S := by
    simpa [mem_measurableCylinders] using hA
  rw [piContent_cylinder _ mS, cylinder, ← map_apply (measurable_restrict _) mS,
    infinitePiNat_map_restrict]

end Measure

end Nat

section InfinitePi

open Measure

/-! ### Product of infinitely many probability measures -/

variable {ι : Type*} {X : ι → Type*} {mX : ∀ i, MeasurableSpace (X i)}
  (μ : (i : ι) → Measure (X i)) [hμ : ∀ i, IsProbabilityMeasure (μ i)]

set_option backward.isDefEq.respectTransparency false in
/-- If we push the product measure forward by a reindexing equivalence, we get a product measure
on the reindexed product in the sense that it coincides with `piContent μ` over
measurable cylinders. See `infinitePi_map_piCongrLeft` for a general version. -/
lemma Measure.infinitePiNat_map_piCongrLeft (e : ℕ ≃ ι) {s : Set (Π i, X i)}
    (hs : s ∈ measurableCylinders X) :
    (infinitePiNat (fun n ↦ μ (e n))).map (piCongrLeft X e) s = piContent μ s := by
  obtain ⟨I, S, hS, rfl⟩ := (mem_measurableCylinders s).1 hs
  rw [map_apply _ hS.cylinder, cylinder, ← Set.preimage_comp, coe_piCongrLeft,
    restrict_comp_piCongrLeft, Set.preimage_comp, ← map_apply,
    infinitePiNat_map_restrict (fun n ↦ μ (e n)), ← cylinder, piContent_cylinder μ hS,
    ← pi_map_piCongrLeft (e.restrictPreimageFinset I), map_apply _ hS, coe_piCongrLeft]
  · simp
  any_goals fun_prop
  exact hS.preimage (by fun_prop)

/-- This is the key theorem to build the product of an arbitrary family of probability measures:
the `piContent` of a decreasing sequence of cylinders with empty intersection converges to `0`.

This implies the `σ`-additivity of `piContent` (see `addContent_iUnion_eq_sum_of_tendsto_zero`),
which allows to extend it to the `σ`-algebra by Carathéodory's theorem. -/
theorem piContent_tendsto_zero {A : ℕ → Set (Π i, X i)} (A_mem : ∀ n, A n ∈ measurableCylinders X)
    (A_anti : Antitone A) (A_inter : ⋂ n, A n = ∅) :
    Tendsto (fun n ↦ piContent μ (A n)) atTop (𝓝 0) := by
  have : ∀ i, Nonempty (X i) := fun i ↦ nonempty_of_isProbabilityMeasure (μ i)
  have A_cyl n : ∃ s S, MeasurableSet S ∧ A n = cylinder s S :=
    (mem_measurableCylinders _).1 (A_mem n)
  choose s S mS A_eq using A_cyl
  -- The family `(Aₙ)` only depends on a countable set of coordinates, called `u`. Therefore our
  -- goal is to see it as a family indexed by this countable set, because on the product indexed
  -- by this countable set we can build a measure. To do so we have to pull back our cylinders
  -- along the injection from `Π i : u, X i` to `Π i, X i`.
  let u := ⋃ n, (s n : Set ι)
  -- `tₙ` will be `sₙ` seen as a subset of `u`.
  let t n : Finset u := (s n).preimage Subtype.val Subtype.val_injective.injOn
  classical
  -- The map `f` allows to pull back `Aₙ`
  let f : (Π i : u, X i) → Π i, X i :=
    fun x i ↦ if hi : i ∈ u then x ⟨i, hi⟩ else Classical.ofNonempty
  -- `aux` is the obvious equivalence between `sₙ` and `tₙ`
  let aux n : t n ≃ s n :=
    { toFun := fun i ↦ ⟨i.1.1, mem_preimage.1 i.2⟩
      invFun := fun i ↦ ⟨⟨i.1, Set.mem_iUnion.2 ⟨n, i.2⟩⟩, mem_preimage.2 i.2⟩
      left_inv := fun i ↦ by simp
      right_inv := fun i ↦ by simp }
  -- Finally `gₙ` is the equivalence between the product indexed by `tₙ` and the one indexed by `sₙ`
  let g n := (aux n).piCongrLeft (fun i : s n ↦ X i)
  -- Mapping from the product indexed by `u` by `f` and then restricting to `sₙ` is the same as
  -- first restricting to `tₙ` and then mapping by `gₙ`
  have r_comp_f n : (s n).restrict ∘ f = (g n) ∘ (fun (x : Π i : u, X i) i ↦ x i) := by
    ext x i
    simp only [Function.comp_apply, Finset.restrict,
      Equiv.piCongrLeft_apply, Equiv.coe_fn_symm_mk, f, aux, g, t]
    rw [dif_pos (Set.mem_iUnion.2 ⟨n, i.2⟩)]
  -- `Bₙ` is the same as `Aₙ` but in the product indexed by `u`
  let B n := f ⁻¹' (A n)
  -- `Tₙ` is the same as `Sₙ` but in the product indexed by `u`
  let T n := (g n) ⁻¹' (S n)
  -- We now transfer the properties of `Aₙ` and `Sₙ` to `Bₙ` and `Tₙ`
  have B_eq n : B n = cylinder (t n) (T n) := by
    simp_rw [B, A_eq, cylinder, ← Set.preimage_comp, r_comp_f]; rfl
  have mT n : MeasurableSet (T n) := (mS n).preimage (by fun_prop)
  have B_mem n : B n ∈ measurableCylinders (fun i : u ↦ X i) :=
    (mem_measurableCylinders (B n)).2 ⟨t n, T n, mT n, B_eq n⟩
  have mB n : MeasurableSet (B n) := .of_mem_measurableCylinders (B_mem n)
  have B_anti : Antitone B := fun m n hmn ↦ Set.preimage_mono <| A_anti hmn
  have B_inter : ⋂ n, B n = ∅ := by
    simp_rw [B, ← Set.preimage_iInter, A_inter, Set.preimage_empty]
  -- We now rewrite `piContent μ (A n)` as `piContent (fun i : u ↦ μ i) (B n)`. Then there are two
  -- cases: either `u` is finite and we rewrite it to the finite product measure, either
  -- it is countable and we rewrite it to the pushforward measure of `infinitePiNat`. In both cases
  -- we have an actual measure and we can conclude with `tendsto_measure_iInter_atTop`.
  conv =>
    enter [1]; ext n
    rw [A_eq, piContent_cylinder μ (mS n), ← pi_map_piCongrLeft (aux n),
      map_apply (by fun_prop) (mS n)]
    change (Measure.pi (fun i : t n ↦ μ i)) (T n)
    rw [← piContent_cylinder (fun i : u ↦ μ i) (mT n), ← B_eq n]
  obtain u_fin | u_inf := finite_or_infinite u
  · let _ := Fintype.ofFinite u
    simp_rw [fun n ↦ piContent_eq_measure_pi (fun i : u ↦ μ i) (mB n)]
    convert tendsto_measure_iInter_atTop (fun n ↦ (mB n).nullMeasurableSet) B_anti
      ⟨0, measure_ne_top _ _⟩
    · rw [B_inter, measure_empty]
    · infer_instance
  · -- If `u` is infinite, then we have an equivalence with `ℕ` so we can apply `secondLemma`.
    have count_u : Countable u := Set.countable_iUnion (fun n ↦ (s n).countable_toSet)
    obtain ⟨φ, -⟩ := Classical.exists_true_of_nonempty (α := ℕ ≃ u) nonempty_equiv_of_countable
    conv => enter [1]; ext n; rw [← infinitePiNat_map_piCongrLeft _ φ (B_mem n)]
    convert tendsto_measure_iInter_atTop (fun n ↦ (mB n).nullMeasurableSet) B_anti
      ⟨0, measure_ne_top _ _⟩
    · rw [B_inter, measure_empty]
    · infer_instance

/-- The `projectiveFamilyContent` associated to a family of probability measures is
σ-subadditive. -/
theorem isSigmaSubadditive_piContent : (piContent μ).IsSigmaSubadditive := by
  refine isSigmaSubadditive_of_addContent_iUnion_eq_tsum
    isSetRing_measurableCylinders (fun f hf hf_Union hf' ↦ ?_)
  exact addContent_iUnion_eq_sum_of_tendsto_zero isSetRing_measurableCylinders
    (piContent μ) (fun s hs ↦ projectiveFamilyContent_ne_top _)
    (fun _ ↦ piContent_tendsto_zero μ) hf hf_Union hf'

namespace Measure

open scoped Classical in
/-- The product measure of an arbitrary family of probability measures. It is defined as the unique
extension of the function which gives to cylinders the measure given by the associated product
measure.

It is defined via an `if ... then ... else` so that it can be manipulated without carrying
a proof that the measures are probability measures. -/
noncomputable def infinitePi : Measure (Π i, X i) :=
  if h : ∀ i, IsProbabilityMeasure (μ i) then
    (piContent μ).measure isSetSemiring_measurableCylinders
      generateFrom_measurableCylinders.ge (isSigmaSubadditive_piContent (hμ := h) μ)
    else 0

/-- The product measure is the projective limit of the partial product measures. This ensures
uniqueness and expresses the value of the product measure applied to cylinders. -/
theorem isProjectiveLimit_infinitePi :
    IsProjectiveLimit (infinitePi μ) (fun I : Finset ι ↦ (Measure.pi (fun i : I ↦ μ i))) := by
  intro I
  ext s hs
  rw [map_apply (measurable_restrict I) hs, infinitePi, dif_pos hμ, AddContent.measure_eq,
    ← cylinder, piContent_cylinder μ hs]
  · exact generateFrom_measurableCylinders.symm
  · exact cylinder_mem_measurableCylinders _ _ hs

/-- Restricting the product measure to a product indexed by a finset yields the usual
product measure. -/
theorem infinitePi_map_restrict {I : Finset ι} :
    (Measure.infinitePi μ).map I.restrict = Measure.pi fun i : I ↦ μ i :=
  isProjectiveLimit_infinitePi μ I

instance : IsProbabilityMeasure (infinitePi μ) := by
  constructor
  rw [← cylinder_univ ∅, cylinder, ← map_apply (measurable_restrict _) .univ,
    infinitePi_map_restrict, measure_univ]

/-- To prove that a measure is equal to the product measure it is enough to check that it
it gives the same measure to measurable boxes. -/
theorem eq_infinitePi {ν : Measure (Π i, X i)}
    (hν : ∀ s : Finset ι, ∀ t : (i : ι) → Set (X i),
      (∀ i, MeasurableSet (t i)) → ν (Set.pi s t) = ∏ i ∈ s, μ i (t i)) :
    ν = infinitePi μ := by
  refine (isProjectiveLimit_infinitePi μ).unique ?_ |>.symm
  refine fun s ↦ (pi_eq fun t ht ↦ ?_).symm
  classical
  rw [Measure.map_apply, restrict_preimage_univ, hν, ← prod_attach, univ_eq_attach]
  · congr with i
    rw [dif_pos i.2]
  any_goals fun_prop
  · rintro i
    split_ifs with hi
    · exact ht ⟨i, hi⟩
    · exact .univ
  · exact .univ_pi ht

lemma infinitePi_pi {s : Finset ι} {t : (i : ι) → Set (X i)}
    (mt : ∀ i ∈ s, MeasurableSet (t i)) :
    infinitePi μ (Set.pi s t) = ∏ i ∈ s, μ i (t i) := by
  have : Set.pi s t = cylinder s ((@Set.univ s).pi (fun i : s ↦ t i)) := by
    ext x
    simp
  rw [this, cylinder, ← map_apply, infinitePi_map_restrict, pi_pi]
  · rw [univ_eq_attach, prod_attach _ (fun i ↦ (μ i) (t i))]
  · exact measurable_restrict _
  · exact .univ_pi fun i ↦ mt i.1 i.2

theorem infinitePi_map_restrict' {I : Set ι} :
    (infinitePi μ).map I.restrict = infinitePi fun i : I ↦ μ i := by
  apply eq_infinitePi
  intro s t ht
  classical
  rw [map_apply (by fun_prop), restrict_preimage, infinitePi_pi _ (by measurability)]
  · simp
  · exact .pi s.countable_toSet (by measurability)

lemma infinitePi_pi_of_countable {s : Set ι} (hs : Countable s) {t : (i : ι) → Set (X i)}
    (mt : ∀ i ∈ s, MeasurableSet (t i)) :
    infinitePi μ (Set.pi s t) = ∏' i : s, μ i (t i) := by
  wlog s_ne : Nonempty s
  · simp [Set.not_nonempty_iff_eq_empty'.mp s_ne]
  apply tendsto_nhds_unique (f := fun s' : Finset s ↦ ∏ i ∈ s', μ i (t i)) (l := atTop)
  classical
  · conv in ∏ _ ∈ _, _ =>
      rw [← infinitePi_pi _ (by measurability), ← infinitePi_map_restrict', map_apply
        (by fun_prop) (by apply MeasurableSet.pi (countable_toSet _) (by measurability)),
        restrict_preimage]
      simp only [coe_image, dite_eq_ite]
    have : s.pi t
      = ⋂ s' : Finset s,
        (Subtype.val '' (s' : Set s)).pi (fun i ↦ if i ∈ s then t i else Set.univ) := by
      rw [← Set.pi_iUnion_eq_iInter_pi, Set.iUnion_finset_eq_set]
      grind
    rw [this]
    apply tendsto_measure_iInter_atTop
    · refine fun s' ↦ MeasurableSet.nullMeasurableSet (MeasurableSet.pi ?_ (by measurability))
      exact (Finset.countable_toSet _).image _
    · intro _ _ h
      simpa using Set.pi_mono' (by simp) (Set.image_mono h)
    · exact ⟨{Nonempty.some s_ne}, by simp⟩
  · rw [ENNReal.tprod_eq_iInf_prod (by simp [prob_le_one])]
    exact tendsto_atTop_iInf (prod_anti_set_of_le_one (by simp [prob_le_one]))

lemma infinitePi_pi_univ [Countable ι] {t : (i : ι) → Set (X i)}
    (mt : ∀ i : ι, MeasurableSet (t i)) :
    infinitePi μ (Set.univ.pi t) = ∏' i, μ i (t i) := by
  rw [infinitePi_pi_of_countable, tprod_univ (f := fun i ↦ μ i (t i))]
  · simpa [Set.countable_univ_iff]
  · measurability

@[simp]
lemma infinitePi_singleton [Countable ι] [∀ i, MeasurableSingletonClass (X i)]
    (f : ∀ i, X i) : infinitePi μ {f} = ∏' i, μ i {f i} := by
  rw [← Set.univ_pi_singleton, infinitePi_pi_univ _ (by measurability)]

lemma infinitePi_singleton_of_fintype [Fintype ι] [∀ i, MeasurableSingletonClass (X i)]
    (f : ∀ i, X i) : infinitePi μ {f} = ∏ i, μ i {f i} := by simp

@[simp] lemma infinitePi_dirac (f : ∀ i, X i) : infinitePi (fun i ↦ dirac (f i)) = dirac f :=
  .symm <| eq_infinitePi _ <| by simp +contextual [MeasurableSet.pi, Finset.countable_toSet]

lemma _root_.measurePreserving_eval_infinitePi (i : ι) :
    MeasurePreserving (Function.eval i) (infinitePi μ) (μ i) where
  measurable := by fun_prop
  map_eq := by
    ext s hs
    have : @Function.eval ι X i =
        (@Function.eval ({i} : Finset ι) (fun j ↦ X j) ⟨i, by simp⟩) ∘
        (Finset.restrict {i}) := by ext; simp
    rw [this, ← map_map, infinitePi_map_restrict, (measurePreserving_eval _ _).map_eq]
    all_goals fun_prop

lemma infinitePi_map_eval (i : ι) :
    (infinitePi μ).map (fun x ↦ x i) = μ i :=
  (measurePreserving_eval_infinitePi μ i).map_eq

lemma infinitePi_map_pi {Y : ι → Type*} [∀ i, MeasurableSpace (Y i)] {f : (i : ι) → X i → Y i}
    (hf : ∀ i, Measurable (f i)) :
    (infinitePi μ).map (fun x i ↦ f i (x i)) = infinitePi (fun i ↦ (μ i).map (f i)) := by
  have (i : ι) : IsProbabilityMeasure ((μ i).map (f i)) :=
    isProbabilityMeasure_map (hf i).aemeasurable
  refine eq_infinitePi _ fun s t ht ↦ ?_
  rw [map_apply (by fun_prop) (.pi s.countable_toSet fun _ _ ↦ ht _)]
  have : (fun (x : Π i, X i) i ↦ f i (x i)) ⁻¹' ((s : Set ι).pi t) =
      (s : Set ι).pi (fun i ↦ (f i) ⁻¹' (t i)) := by ext x; simp
  rw [this, infinitePi_pi _ (fun i _ ↦ hf i (ht i))]
  congr! with i hi
  rw [map_apply (by fun_prop) (ht i)]

/-- If we push the product measure forward by a reindexing equivalence, we get a product measure
on the reindexed product. -/
theorem infinitePi_map_piCongrLeft {α : Type*} (e : α ≃ ι) :
    (infinitePi (fun i ↦ μ (e i))).map (piCongrLeft X e) = infinitePi μ := by
  refine eq_infinitePi μ fun s t ht ↦ ?_
  conv_lhs => enter [2, 1]; rw [← e.image_preimage s, ← coe_preimage _ e.injective.injOn]
  rw [map_apply, coe_piCongrLeft, Equiv.piCongrLeft_preimage_pi, infinitePi_pi,
    prod_equiv e]
  · simp
  · simp
  · simp_all
  · fun_prop
  · exact .pi ((countable_toSet _).image e) (by simp_all)

theorem infinitePi_eq_pi [Fintype ι] : infinitePi μ = Measure.pi μ := by
  refine (pi_eq fun s hs ↦ ?_).symm
  rw [← coe_univ, infinitePi_pi]
  simpa

lemma infinitePi_cylinder {s : Finset ι} {S : Set (Π i : s, X i)} (mS : MeasurableSet S) :
    infinitePi μ (cylinder s S) = Measure.pi (fun i : s ↦ μ i) S := by
  rw [cylinder, ← Measure.map_apply (measurable_restrict _) mS, infinitePi_map_restrict]

section curry

variable {ι : Type*} {κ : ι → Type*} {X : (i : ι) → κ i → Type*}
  {mX : ∀ i, ∀ j, MeasurableSpace (X i j)} (μ : (i : ι) → (j : κ i) → Measure (X i j))
  [hμ : ∀ i j, IsProbabilityMeasure (μ i j)]

lemma infinitePi_map_piCurry_symm :
    (infinitePi fun i : ι ↦ infinitePi fun j : κ i ↦ μ i j).map (piCurry X).symm =
      infinitePi fun p : (i : ι) × κ i ↦ μ p.1 p.2 := by
  apply eq_infinitePi
  intro s t ht
  classical
  rw [map_apply (by fun_prop) (.pi (countable_toSet _) fun _ _ ↦ ht _),
    ← Finset.sigma_image_fst_preimage_mk s, coe_piCurry_symm, Finset.coe_sigma,
    Set.uncurry_preimage_sigma_pi, infinitePi_pi, Finset.prod_sigma]
  · exact Finset.prod_congr rfl (fun _ _ ↦ infinitePi_pi _ fun _ _ ↦ ht _)
  · simp only [mem_image, Sigma.exists, exists_and_right, exists_eq_right, forall_exists_index]
    exact fun i j hij ↦ MeasurableSet.pi (countable_toSet _) fun k hk ↦ by simp_all

lemma infinitePi_map_piCurry :
    (infinitePi fun p : (i : ι) × κ i ↦ μ p.1 p.2).map (piCurry X) =
      infinitePi fun i : ι ↦ infinitePi fun j : κ i ↦ μ i j := by
  rw [MeasurableEquiv.map_apply_eq_iff_map_symm_apply_eq, infinitePi_map_piCurry_symm]

variable {ι κ X : Type*} {mX : MeasurableSpace X} (μ : ι → κ → Measure X)
  [hμ : ∀ i j, IsProbabilityMeasure (μ i j)]

lemma infinitePi_map_curry_symm :
    (infinitePi fun i : ι ↦ infinitePi fun j : κ ↦ μ i j).map (curry ι κ X).symm =
      infinitePi fun p : ι × κ ↦ μ p.1 p.2 := by
  rw [← (MeasurableEquiv.piCongrLeft (fun _ ↦ X)
    (Equiv.sigmaEquivProd ι κ).symm).map_measurableEquiv_injective.eq_iff, map_map]
  · have : (MeasurableEquiv.piCongrLeft (fun _ ↦ X) (Equiv.sigmaEquivProd ι κ).symm) ∘
        (MeasurableEquiv.curry ι κ X).symm = ⇑(MeasurableEquiv.piCurry (fun _ _ ↦ X)).symm := by
      ext; simp [piCongrLeft, Equiv.piCongrLeft, Sigma.uncurry]
    rw [this, infinitePi_map_piCurry_symm]
    convert infinitePi_map_piCongrLeft (fun p ↦ μ p.1 p.2) (Equiv.sigmaEquivProd ι κ).symm |>.symm
  all_goals fun_prop

lemma infinitePi_map_curry :
    (infinitePi fun p : ι × κ ↦ μ p.1 p.2).map (curry ι κ X) =
      infinitePi fun i : ι ↦ infinitePi fun j : κ ↦ μ i j := by
  rw [MeasurableEquiv.map_apply_eq_iff_map_symm_apply_eq, infinitePi_map_curry_symm]

end curry

end Measure

section Integral

theorem integral_restrict_infinitePi {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {s : Finset ι} {f : (Π i : s, X i) → E}
    (hf : AEStronglyMeasurable f (Measure.pi (fun i : s ↦ μ i))) :
    ∫ y, f (s.restrict y) ∂infinitePi μ = ∫ y, f y ∂Measure.pi (fun i : s ↦ μ i) := by
  rw [← integral_map, infinitePi_map_restrict]
  · fun_prop
  · rwa [infinitePi_map_restrict]

theorem lintegral_restrict_infinitePi {s : Finset ι}
    {f : (Π i : s, X i) → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ y, f (s.restrict y) ∂infinitePi μ = ∫⁻ y, f y ∂Measure.pi (fun i : s ↦ μ i) := by
  rw [← lintegral_map hf (measurable_restrict _), isProjectiveLimit_infinitePi μ]

open Filtration

theorem integral_infinitePi_of_piFinset [DecidableEq ι] {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {s : Finset ι} {f : (Π i, X i) → E}
    (mf : StronglyMeasurable[piFinset s] f) (x : Π i, X i) :
    ∫ y, f y ∂infinitePi μ =
    ∫ y, f (Function.updateFinset x s y) ∂Measure.pi (fun i : s ↦ μ i) := by
  let g : (Π i : s, X i) → E := fun y ↦ f (Function.updateFinset x _ y)
  have this y : g (s.restrict y) = f y :=
    mf.dependsOn_of_piFinset fun i hi ↦ by simp_all [Function.updateFinset]
  rw [← integral_congr_ae <| ae_of_all _ this, integral_restrict_infinitePi]
  exact mf.comp_measurable (measurable_updateFinset.mono le_rfl (piFinset.le s))
    |>.aestronglyMeasurable

theorem lintegral_infinitePi_of_piFinset [DecidableEq ι] {s : Finset ι}
    {f : (Π i, X i) → ℝ≥0∞} (mf : Measurable[piFinset s] f)
    (x : Π i, X i) : ∫⁻ y, f y ∂infinitePi μ = (∫⋯∫⁻_s, f ∂μ) x := by
  let g : (Π i : s, X i) → ℝ≥0∞ := fun y ↦ f (Function.updateFinset x _ y)
  have this y : g (s.restrict y) = f y :=
    mf.dependsOn_of_piFinset fun i hi ↦ by simp_all [Function.updateFinset]
  rw [← lintegral_congr_ae <| ae_of_all _ this, lintegral_restrict_infinitePi]
  · rfl
  · exact mf.comp (measurable_updateFinset.mono le_rfl (piFinset.le s))

end Integral

end InfinitePi

end MeasureTheory
