/-
Copyright (c) 2025 Etienne Marion. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Etienne Marion
-/
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Probability.Kernel.IonescuTulcea.Traj

/-!
# Infinite product of probability measures

This files provides a definition for the product measure of an arbitrary family of probability
measures. Given `μ : (i : ι) → Measure (X i)`, `Measure.infinitePi μ` is the only probability
measure `ν` over `Π i, X i` such that `ν (Set.pi s t) = ∏ i ∈ s, μ i (t i)`, with `s : Finset ι` and
such that `∀ i ∈ s, MeasurableSet (t i)` (see `eq_infinitePi` and `infinitePi_boxes`).
We also provide a few results regarding integration against this measure.

## Main definition

* `Measure.infinitePi μ`: The product measure of the family of probability measures `μ`.

## Main statements

* `eq_infinitePi`: Any measure which gives to a finite product of sets the mass which is the
  product of their measures is the product measure.
* `infinitePi_boxes`: the product measure gives to finite products of sets a mass which is
  the product of their masses.
* `infinitePi_cylinder`: `infinitePi μ (cylinder s S) = Measure.pi (fun i : s ↦ μ i) S`

## Implementation notes

To construct the product measure we first use the kernel `traj` obtained via the Ionescu-Tulcea
theorem to construct the measure over a product indexed by `ℕ`, which is `infinitePiNat`. This
is an implementation detail and should not be used directly. Then we construct the product measure
over an arbitrary type by extending `piContent μ` thanks to Carathéodory's theorem. The key lemma
to do so is `piContent_tendsto_zero`, which states that `piContent μ (A n)` tends to zero if
`⋂ n, A n = ∅`. We prove this lemma by reducing to the case of an at most countable product,
in which case `piContent μ` is known to be a true measure (see `piContent_eq_measure_pi` and
`piContent_eq_infinitePiNat`).

## Tags

infinite product measure
-/

open MeasureTheory ProbabilityTheory Finset Filter Preorder MeasurableEquiv

open scoped ENNReal Topology

namespace MeasureTheory

section Preliminaries

variable {ι : Type*} {α : ι → Type*}

variable {X : ι → Type*} [∀ i, MeasurableSpace (X i)]
variable (μ : (i : ι) → Measure (X i)) [hμ : ∀ i, IsProbabilityMeasure (μ i)]

/-- Consider a family of probability measures. You can take their products for any finite
subfamily. This gives a projective family of measures, see `IsProjectiveMeasureFamily`. -/
lemma isProjectiveMeasureFamily_pi :
    IsProjectiveMeasureFamily (fun I : Finset ι ↦ (Measure.pi (fun i : I ↦ μ i))) := by
  refine fun I J hJI ↦ Measure.pi_eq (fun s ms ↦ ?_)
  classical
  rw [Measure.map_apply (measurable_restrict₂ hJI) (.univ_pi ms),
    preimage_restrict₂ hJI, Measure.pi_pi]
  let g := fun i ↦ (μ i) (if hi : i ∈ J then s ⟨i, hi⟩ else Set.univ)
  conv_lhs => change ∏ i : I, g i
  have h2 : univ.prod (fun i : J ↦ (μ i) (s i)) = univ.prod (fun i : J ↦ g i) :=
    Finset.prod_congr rfl (by simp [g])
  rw [h2, prod_coe_sort, prod_coe_sort, prod_subset hJI (fun _ h h' ↦ by simp [g, h, h'])]

/-- Consider a family of probability measures. You can take their products for any finite
subfamily. This gives an additive content on the measurable cylinders. -/
noncomputable def piContent : AddContent (measurableCylinders X) :=
  projectiveFamilyContent (isProjectiveMeasureFamily_pi μ)

lemma piContent_cylinder {I : Finset ι} {S : Set (Π i : I, X i)} (hS : MeasurableSet S) :
    piContent μ (cylinder I S) = Measure.pi (fun i : I ↦ μ i) S :=
  projectiveFamilyContent_cylinder _ hS

theorem piContent_eq_measure_pi [Fintype ι] {s : Set (Π i, X i)} (hs : MeasurableSet s) :
    piContent μ s = Measure.pi μ s := by
  let aux : (Π i : univ, X i) → (Π i, X i) := fun x i ↦ x ⟨i, mem_univ i⟩
  have maux : Measurable aux := measurable_pi_lambda _ (fun _ ↦ measurable_pi_apply _)
  have pi_eq : Measure.pi μ = (Measure.pi (fun i : univ ↦ μ i)).map aux := by
    refine Measure.pi_eq fun a ma ↦ ?_
    rw [Measure.map_apply maux (.univ_pi ma)]
    have : aux ⁻¹' Set.univ.pi a = Set.univ.pi (fun i : @univ ι _ ↦ a i) := by ext x; simp [aux]
    rw [this, Measure.pi_pi]
    simp
  have : s = cylinder univ (aux ⁻¹' s) := by ext x; simp [aux]
  nth_rw 1 [this]
  rw [piContent_cylinder _ (maux hs), pi_eq, Measure.map_apply maux hs]

end Preliminaries

section Nat

open Kernel

/-! ### Product of measures indexed by `ℕ` -/

variable {X : ℕ → Type*}

lemma _root_.IocProdIoc_preim {a b c : ℕ} (hab : a ≤ b) (hbc : b ≤ c)
    (s : (i : Ioc a c) → Set (X i)) :
    IocProdIoc a b c ⁻¹' (Set.univ.pi s) =
      (Set.univ.pi <| restrict₂ (π := (fun n ↦ Set (X n))) (Ioc_subset_Ioc_right hbc) s) ×ˢ
        (Set.univ.pi <| restrict₂ (π := (fun n ↦ Set (X n))) (Ioc_subset_Ioc_left hab) s) := by
  ext x
  simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, IocProdIoc, forall_const, Subtype.forall,
    mem_Ioc, Set.mem_prod, restrict₂]
  refine ⟨fun h ↦ ⟨fun i ⟨hi1, hi2⟩ ↦ ?_, fun i ⟨hi1, hi2⟩ ↦ ?_⟩, fun ⟨h1, h2⟩ i ⟨hi1, hi2⟩ ↦ ?_⟩
  · convert h i ⟨hi1, hi2.trans hbc⟩
    rw [dif_pos hi2]
  · convert h i ⟨lt_of_le_of_lt hab hi1, hi2⟩
    rw [dif_neg (not_le.2 hi1)]
  · split_ifs with hi3
    · exact h1 i ⟨hi1, hi3⟩
    · exact h2 i ⟨not_le.1 hi3, hi2⟩

lemma _root_.IicProdIoc_preim {a b : ℕ} (hab : a ≤ b) (s : (i : Iic b) → Set (X i)) :
    IicProdIoc a b ⁻¹' (Set.univ.pi s) =
      (Set.univ.pi <| frestrictLe₂ (π := (fun n ↦ Set (X n))) hab s) ×ˢ
        (Set.univ.pi <| restrict₂ (π := (fun n ↦ Set (X n))) Ioc_subset_Iic_self s) := by
  ext x
  simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, IicProdIoc_def, forall_const,
    Subtype.forall, mem_Iic, Set.mem_prod, frestrictLe₂_apply, restrict₂, mem_Ioc]
  refine ⟨fun h ↦ ⟨fun i hi ↦ ?_, fun i ⟨hi1, hi2⟩ ↦ ?_⟩, fun ⟨h1, h2⟩ i hi ↦ ?_⟩
  · convert h i (hi.trans hab)
    rw [dif_pos hi]
  · convert h i hi2
    rw [dif_neg (not_le.2 hi1)]
  · split_ifs with hi3
    · exact h1 i hi3
    · exact h2 i ⟨not_le.1 hi3, hi⟩

variable [∀ n, MeasurableSpace (X n)]
  (μ : (n : ℕ) → Measure (X n)) [hμ : ∀ n, IsProbabilityMeasure (μ n)]

/-- Infinite product measure indexed by `ℕ`. This is an auxiliary construction, you should use
the generic product measure `Measure.infinitePi`. -/
noncomputable def Measure.infinitePiNat : Measure ((n : ℕ) → X n) :=
  (traj (fun n ↦ const _ (μ (n + 1))) 0) ∘ₘ (Measure.pi (fun i : Iic 0 ↦ μ i))

instance : IsProbabilityMeasure (Measure.infinitePiNat μ) := by
  rw [Measure.infinitePiNat]; infer_instance

lemma Measure.pi_prod_map_IocProdIoc {a b c : ℕ} (hab : a ≤ b) (hbc : b ≤ c) :
    ((Measure.pi (fun i : Ioc a b ↦ μ i)).prod (Measure.pi (fun i : Ioc b c ↦ μ i))).map
      (IocProdIoc a b c) = Measure.pi (fun i : Ioc a c ↦ μ i) := by
  refine (Measure.pi_eq fun s ms ↦ ?_).symm
  simp_rw [Measure.map_apply measurable_IocProdIoc (.univ_pi ms), IocProdIoc_preim hab hbc,
    Measure.prod_prod, Measure.pi_pi, prod_eq_prod_extend]
  nth_rw 1 [Eq.comm, ← Ioc_union_Ioc_eq_Ioc hab hbc, prod_union (Ioc_disjoint_Ioc a b c)]
  congr 1 <;> refine prod_congr rfl fun x hx ↦ ?_
  · rw [Function.extend_val_apply x hx, Function.extend_val_apply x (Ioc_subset_Ioc_right hbc hx),
    restrict₂]
  · rw [Function.extend_val_apply x hx, Function.extend_val_apply x (Ioc_subset_Ioc_left hab hx),
    restrict₂]

lemma Measure.pi_prod_map_IicProdIoc {a b : ℕ} :
    ((Measure.pi (fun i : Iic a ↦ μ i)).prod (Measure.pi (fun i : Ioc a b ↦ μ i))).map
      (IicProdIoc a b) = Measure.pi (fun i : Iic b ↦ μ i) := by
  obtain hab | hba := le_total a b
  · refine (Measure.pi_eq fun s ms ↦ ?_).symm
    simp_rw [Measure.map_apply measurable_IicProdIoc (.univ_pi ms), IicProdIoc_preim hab,
      Measure.prod_prod, Measure.pi_pi, prod_eq_prod_extend]
    nth_rw 1 [Eq.comm, ← Iic_union_Ioc_eq_Iic hab, prod_union (Iic_disjoint_Ioc le_rfl)]
    congr 1 <;> refine prod_congr rfl fun x hx ↦ ?_
    · rw [Function.extend_val_apply x hx, Function.extend_val_apply x (Iic_subset_Iic.2 hab hx),
      frestrictLe₂, restrict₂]
    · rw [Function.extend_val_apply x hx, Function.extend_val_apply x (Ioc_subset_Iic_self hx),
      restrict₂]
  · rw [IicProdIoc_le hba, ← Measure.map_map, ← Measure.fst, Measure.fst_prod]
    · exact isProjectiveMeasureFamily_pi μ (Iic a) (Iic b) (Iic_subset_Iic.2 hba) |>.symm
    all_goals fun_prop

lemma Measure.map_piSingleton (μ : (n : ℕ) → Measure (X n)) [∀ n, SigmaFinite (μ n)] (n : ℕ) :
    (μ (n + 1)).map (piSingleton n) = Measure.pi (fun i : Ioc n (n + 1) ↦ μ i) := by
  refine (Measure.pi_eq fun s hs ↦ ?_).symm
  have : Subsingleton (Ioc n (n + 1)) := by
    rw [Nat.Ioc_succ_singleton]
    infer_instance
  rw [Fintype.prod_subsingleton _ ⟨n + 1, mem_Ioc.2 (by omega)⟩, Measure.map_apply]
  · congr with x
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_const, Subtype.forall,
      Nat.Ioc_succ_singleton, mem_singleton]
    exact ⟨fun h ↦ h (n + 1) rfl, fun h a b ↦ b.symm ▸ h⟩
  · exact (piSingleton n).measurable
  · exact .univ_pi hs

theorem partialTraj_const_restrict₂ {a b : ℕ} :
    (partialTraj (fun n ↦ const _ (μ (n + 1))) a b).map (restrict₂ (Ioc_subset_Iic_self (a := a))) =
    const _ (Measure.pi (fun i : Ioc a b ↦ μ i)) := by
  obtain hab | hba := lt_or_le a b
  · refine Nat.le_induction ?_ (fun n hn hind ↦ ?_) b (Nat.succ_le.2 hab) <;> ext1 x₀
    · rw [partialTraj_succ_self, ← Kernel.map_comp_right, map_apply, prod_apply, map_apply,
        const_apply, const_apply, Measure.map_piSingleton, restrict₂_comp_IicProdIoc,
        Measure.map_snd_prod, measure_univ, one_smul]
      all_goals fun_prop
    · have : (restrict₂ (Ioc_subset_Iic_self (a := a))) ∘ (IicProdIoc (X := X) n (n + 1)) =
          (IocProdIoc a n (n + 1)) ∘ (Prod.map (restrict₂ Ioc_subset_Iic_self) id) := rfl
      rw [const_apply, partialTraj_succ_of_le (by omega), map_const, prod_const_comp, id_comp,
        ← map_comp_right, this, map_comp_right, ← map_prod_map, hind, Kernel.map_id, map_apply,
        prod_apply, const_apply, const_apply, Measure.map_piSingleton,
        Measure.pi_prod_map_IocProdIoc]
      any_goals fun_prop
      all_goals omega
  · have : IsEmpty (Ioc a b) := by simpa [hba] using Subtype.isEmpty_false
    ext x s ms
    by_cases hs : s.Nonempty
    · rw [Subsingleton.eq_univ_of_nonempty hs, @measure_univ .., measure_univ]
      exact (IsMarkovKernel.map _ (measurable_restrict₂ _)) |>.isProbabilityMeasure x
    · rw [Set.not_nonempty_iff_eq_empty.1 hs]
      simp

theorem partialTraj_const {a b : ℕ} :
    partialTraj (fun n ↦ const _ (μ (n + 1))) a b =
      (Kernel.id ×ₖ (const _ (Measure.pi (fun i : Ioc a b ↦ μ i)))).map (IicProdIoc a b) := by
  rw [partialTraj_eq_prod, partialTraj_const_restrict₂]

theorem isProjectiveLimit_infinitePiNat :
    IsProjectiveLimit (Measure.infinitePiNat μ)
      (fun I : Finset ℕ ↦ (Measure.pi (fun i : I ↦ μ i))) := by
  have _ := ProbabilityMeasure.nonempty ⟨μ 0, hμ 0⟩
  intro I
  simp_rw [isProjectiveMeasureFamily_pi μ _ _ I.subset_Iic_sup_id]
  rw [← restrict₂_comp_restrict I.subset_Iic_sup_id, ← Measure.map_map, ← frestrictLe,
    Measure.infinitePiNat, Measure.map_comp, traj_map_frestrictLe, partialTraj_const,
    ← Measure.map_comp, ← Measure.compProd_eq_comp_prod, Measure.compProd_const,
    Measure.pi_prod_map_IicProdIoc]
  all_goals fun_prop

lemma infinitePiNat_map_restrict {I : Finset ℕ} :
    (Measure.infinitePiNat μ).map I.restrict = Measure.pi fun i : I ↦ μ i :=
  isProjectiveLimit_infinitePiNat μ I

theorem piContent_eq_infinitePiNat {A : Set ((n : ℕ) → X n)} (hA : A ∈ measurableCylinders X) :
    piContent μ A = Measure.infinitePiNat μ A := by
  obtain ⟨s, S, mS, rfl⟩ : ∃ s S, MeasurableSet S ∧ A = cylinder s S := by
    simpa [mem_measurableCylinders] using hA
  rw [piContent_cylinder _ mS, cylinder, ← Measure.map_apply (measurable_restrict _) mS,
    isProjectiveLimit_infinitePiNat μ]

end Nat

section InfinitePi

open Measure

/-! ### Product of infinitely many probability measures -/

variable {ι : Type*} {X : ι → Type*} [∀ i, MeasurableSpace (X i)]
  (μ : (i : ι) → Measure (X i)) [hμ : ∀ i, IsProbabilityMeasure (μ i)]

lemma infinitePiNat_map_piCongrLeft (e : ℕ ≃ ι) {s : Set (Π i, X i)}
    (hs : s ∈ measurableCylinders X) :
    (infinitePiNat (fun n ↦ μ (e n))).map (piCongrLeft X e) s = piContent μ s := by
  obtain ⟨I, S, hS, rfl⟩ := (mem_measurableCylinders s).1 hs
  rw [map_apply _ hS.cylinder, cylinder, ← Set.preimage_comp, coe_piCongrLeft,
    restrict_comp_piCongrLeft, Set.preimage_comp, ← map_apply,
    infinitePiNat_map_restrict (fun n ↦ μ (e n)), ← cylinder, piContent_cylinder μ hS,
    ← pi_map_piCongrLeft (e.frestrict I), map_apply _ hS]
  · rfl
  any_goals fun_prop
  exact hS.preimage (by fun_prop)

/-- This is the key theorem to build the product of an arbitrary family of probability measures:
the `piContent` of a decreasing sequence of cylinders with empty intersection converges to `0`.

This implies the `σ`-additivity of `piContent` (see `addContent_iUnion_eq_sum_of_tendsto_zero`),
which allows to extend it to the `σ`-algebra by Carathéodory's theorem. -/
theorem piContent_tendsto_zero {A : ℕ → Set (Π i, X i)} (A_mem : ∀ n, A n ∈ measurableCylinders X)
    (A_anti : Antitone A) (A_inter : ⋂ n, A n = ∅) :
    Tendsto (fun n ↦ piContent μ (A n)) atTop (𝓝 0) := by
  have : ∀ i, Nonempty (X i) := fun i ↦ ProbabilityMeasure.nonempty ⟨μ i, hμ i⟩
  have A_cyl n : ∃ s S, MeasurableSet S ∧ A n = cylinder s S :=
    (mem_measurableCylinders _).1 (A_mem n)
  choose s S mS A_eq using A_cyl
  -- The family `(Aₙ)` only depends on a countable set of coordinates, called `u`. Therefore our
  -- goal is to see it as a family indexed by this countable set, because on the product indexed
  -- by this countable set we can build a measure. To do so we have to pull back our cylinders
  -- along the injection from `Π i : u, X i` to `Π i, X i`.
  let u := ⋃ n, (s n).toSet
  let ν := fun i : u ↦ μ i
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
    simp only [Function.comp_apply, Finset.restrict, subset_refl, Set.coe_inclusion,
      Equiv.piCongrLeft_apply, Equiv.coe_fn_symm_mk, f, aux, g, t]
    rw [dif_pos (Set.mem_iUnion.2 ⟨n, i.2⟩)]
  -- `Bₙ` is the same as `Aₙ` but in the product indexed by `u`
  let B n := f ⁻¹' (A n)
  -- `Tₙ` is the same as `Sₙ` but in the product indexed by `u`
  let T n := (g n) ⁻¹' (S n)
  -- We now tranfer the properties of `Aₙ` and `Sₙ` to `Bₙ` and `Tₙ`
  have B_eq n : B n = cylinder (t n) (T n) := by
    simp_rw [B, A_eq, cylinder, ← Set.preimage_comp, r_comp_f]; rfl
  have mg n : Measurable (g n) := by fun_prop
  have mT n : MeasurableSet (T n) := (mS n).preimage (mg n)
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

/-- The product measure of an arbitrary family of probability measures. It is defined as the unique
extension of the function which gives to cylinders the measure given by the associated product
measure. -/
noncomputable def Measure.infinitePi : Measure (Π i, X i) :=
  (piContent μ).measure isSetSemiring_measurableCylinders
    generateFrom_measurableCylinders.ge (isSigmaSubadditive_piContent μ)

open Measure

/-- The product measure is the projective limit of the partial product measures. This ensures
uniqueness and expresses the value of the product measures applied to cylinders. -/
theorem isProjectiveLimit_infinitePi :
    IsProjectiveLimit (infinitePi μ) (fun I : Finset ι ↦ (Measure.pi (fun i : I ↦ μ i))) := by
  intro I
  ext1 s hs
  rw [map_apply (measurable_restrict I) hs, infinitePi, AddContent.measure_eq,
    ← cylinder, piContent_cylinder μ hs]
  · exact generateFrom_measurableCylinders.symm
  · exact cylinder_mem_measurableCylinders _ _ hs

instance : IsProbabilityMeasure (infinitePi μ) := by
  constructor
  rw [← cylinder_univ ∅, cylinder, ← map_apply (measurable_restrict _) .univ,
    isProjectiveLimit_infinitePi μ, measure_univ]

theorem eq_infinitePi {ν : Measure (Π i, X i)}
    (hν : ∀ s : Finset ι, ∀ t : (i : ι) → Set (X i),
      (∀ i ∈ s, MeasurableSet (t i)) → ν (Set.pi s t) = ∏ i ∈ s, μ i (t i)) :
    ν = infinitePi μ := by
  refine (isProjectiveLimit_infinitePi μ).unique ?_ |>.symm
  refine fun s ↦ (pi_eq fun t ht ↦ ?_).symm
  classical
  rw [Measure.map_apply, preimage_restrict, hν, ← prod_attach, univ_eq_attach]
  · congr with i
    rw [dif_pos i.2]
  any_goals fun_prop
  · exact fun i hi ↦ dif_pos hi ▸ ht ⟨i, hi⟩
  · exact .univ_pi ht

-- TODO: add a version for an infinite product
lemma infinitePi_boxes {s : Finset ι} {t : (i : ι) → Set (X i)}
    (mt : ∀ i ∈ s, MeasurableSet (t i)) :
    infinitePi μ (Set.pi s t) = ∏ i ∈ s, (μ i) (t i) := by
  have : Set.pi s t = cylinder s ((@Set.univ s).pi (fun i : s ↦ t i)) := by
    ext x
    simp
  rw [this, cylinder, ← map_apply, isProjectiveLimit_infinitePi μ, pi_pi]
  · rw [Finset.univ_eq_attach, Finset.prod_attach _ (fun i ↦ (μ i) (t i))]
  · exact measurable_restrict _
  · exact .univ_pi fun i ↦ mt i.1 i.2

theorem infinitePi_eq_pi [Fintype ι] : infinitePi μ = Measure.pi μ := by
  refine (pi_eq fun s hs ↦ ?_).symm
  rw [← coe_univ, infinitePi_boxes]
  simpa

lemma infinitePi_cylinder {s : Finset ι} {S : Set (Π i : s, X i)} (mS : MeasurableSet S) :
    infinitePi μ (cylinder s S) = Measure.pi (fun i : s ↦ μ i) S := by
  rw [cylinder, ← Measure.map_apply (measurable_restrict _) mS, isProjectiveLimit_infinitePi μ]

theorem integral_dep_infinitePi {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {s : Finset ι} {f : (Π i : s, X i) → E}
    (hf : AEStronglyMeasurable f (Measure.pi (fun i : s ↦ μ i))) :
    ∫ y, f (s.restrict y) ∂infinitePi μ = ∫ y, f y ∂Measure.pi (fun i : s ↦ μ i) := by
  rw [← integral_map, isProjectiveLimit_infinitePi μ]
  · fun_prop
  · rwa [isProjectiveLimit_infinitePi μ]

open Filtration

/-- If a function is strongly measurable with respect to the σ-algebra generated by
the finite set of coordinates `s`, then it only depends on those coordinates. -/
theorem dependsOn_of_stronglyMeasurable' {E : Type*} [NormedAddCommGroup E]
    {s : Finset ι} {f : (Π i, X i) → E}
    (mf : StronglyMeasurable[piFinset s] f) : DependsOn f s :=
  dependsOn_iff_factorsThrough.2 mf.factorsThrough

theorem integral_stronglyMeasurable [DecidableEq ι] {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {s : Finset ι} {f : (Π i, X i) → E}
    (mf : StronglyMeasurable[piFinset s] f) (x : Π i, X i) :
    ∫ y, f y ∂infinitePi μ =
    ∫ y, f (Function.updateFinset x s y) ∂Measure.pi (fun i : s ↦ μ i) := by
  let g : (Π i : s, X i) → E := fun y ↦ f (Function.updateFinset x _ y)
  have this y : g (s.restrict y) = f y := by
    apply dependsOn_of_stronglyMeasurable' mf
    intro i hi
    simp only [Function.updateFinset, Finset.restrict, dite_eq_ite, ite_eq_left_iff]
    exact fun h ↦ (h hi).elim
  rw [← integral_congr_ae <| Eventually.of_forall this, integral_dep_infinitePi]
  exact mf.comp_measurable (measurable_updateFinset.mono le_rfl (piFinset.le s))
    |>.aestronglyMeasurable

theorem lintegral_dep {s : Finset ι} {f : (Π i : s, X i) → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ y, f (s.restrict y) ∂infinitePi μ = ∫⁻ y, f y ∂Measure.pi (fun i : s ↦ μ i) := by
  rw [← lintegral_map hf (measurable_restrict _), isProjectiveLimit_infinitePi μ]

theorem lintegral_measurable_piFinset [DecidableEq ι] {s : Finset ι}
    {f : (Π i, X i) → ℝ≥0∞} (mf : Measurable[piFinset s] f)
    (x : Π i, X i) : ∫⁻ y, f y ∂infinitePi μ = (∫⋯∫⁻_s, f ∂μ) x := by
  let g : (Π i : s, X i) → ℝ≥0∞ := fun y ↦ f (Function.updateFinset x _ y)
  have this y : g (s.restrict y) = f y := by
    refine mf.dependsOn_of_piFinset fun i hi ↦ ?_
    simp only [Function.updateFinset, Finset.restrict, dite_eq_ite, ite_eq_left_iff]
    exact fun h ↦ (h hi).elim
  simp_rw [← this]
  rw [lintegral_dep]
  · rfl
  · exact mf.comp (measurable_updateFinset.mono le_rfl (piFinset.le s))

end InfinitePi

end MeasureTheory
