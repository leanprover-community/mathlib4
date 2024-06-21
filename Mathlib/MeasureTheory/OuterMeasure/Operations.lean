/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
import Mathlib.MeasureTheory.OuterMeasure.Basic

/-!
# Operations on outer measures

In this file we define algebraic operations (addition, scalar multiplication)
on the type of outer measures on a type.
We also show that outer measures on a type `α` form a complete lattice.

## References

* <https://en.wikipedia.org/wiki/Outer_measure>

## Tags

outer measure

-/

#align_import measure_theory.measure.outer_measure from "leanprover-community/mathlib"@"343e80208d29d2d15f8050b929aa50fe4ce71b55"

noncomputable section

open Set Function Filter
open scoped Classical NNReal Topology ENNReal

namespace MeasureTheory
namespace OuterMeasure

section Basic

variable {α β : Type*} {m : OuterMeasure α}

instance instZero : Zero (OuterMeasure α) :=
  ⟨{  measureOf := fun _ => 0
      empty := rfl
      mono := by intro _ _ _; exact le_refl 0
      iUnion_nat := fun s _ => zero_le _ }⟩
#align measure_theory.outer_measure.has_zero MeasureTheory.OuterMeasure.instZero

@[simp]
theorem coe_zero : ⇑(0 : OuterMeasure α) = 0 :=
  rfl
#align measure_theory.outer_measure.coe_zero MeasureTheory.OuterMeasure.coe_zero

instance instInhabited : Inhabited (OuterMeasure α) :=
  ⟨0⟩
#align measure_theory.outer_measure.inhabited MeasureTheory.OuterMeasure.instInhabited

instance instAdd : Add (OuterMeasure α) :=
  ⟨fun m₁ m₂ =>
    { measureOf := fun s => m₁ s + m₂ s
      empty := show m₁ ∅ + m₂ ∅ = 0 by simp [OuterMeasure.empty]
      mono := fun {s₁ s₂} h => add_le_add (m₁.mono h) (m₂.mono h)
      iUnion_nat := fun s _ =>
        calc
          m₁ (⋃ i, s i) + m₂ (⋃ i, s i) ≤ (∑' i, m₁ (s i)) + ∑' i, m₂ (s i) :=
            add_le_add (measure_iUnion_le s) (measure_iUnion_le s)
          _ = _ := ENNReal.tsum_add.symm }⟩
#align measure_theory.outer_measure.has_add MeasureTheory.OuterMeasure.instAdd

@[simp]
theorem coe_add (m₁ m₂ : OuterMeasure α) : ⇑(m₁ + m₂) = m₁ + m₂ :=
  rfl
#align measure_theory.outer_measure.coe_add MeasureTheory.OuterMeasure.coe_add

theorem add_apply (m₁ m₂ : OuterMeasure α) (s : Set α) : (m₁ + m₂) s = m₁ s + m₂ s :=
  rfl
#align measure_theory.outer_measure.add_apply MeasureTheory.OuterMeasure.add_apply

section SMul

variable {R : Type*} [SMul R ℝ≥0∞] [IsScalarTower R ℝ≥0∞ ℝ≥0∞]
variable {R' : Type*} [SMul R' ℝ≥0∞] [IsScalarTower R' ℝ≥0∞ ℝ≥0∞]

instance instSMul : SMul R (OuterMeasure α) :=
  ⟨fun c m =>
    { measureOf := fun s => c • m s
      empty := by simp; rw [← smul_one_mul c]; simp
      mono := fun {s t} h => by
        simp only
        rw [← smul_one_mul c, ← smul_one_mul c (m t)]
        exact ENNReal.mul_left_mono (m.mono h)
      iUnion_nat := fun s _ => by
        simp_rw [← smul_one_mul c (m _), ENNReal.tsum_mul_left]
        exact ENNReal.mul_left_mono (measure_iUnion_le _) }⟩

@[simp]
theorem coe_smul (c : R) (m : OuterMeasure α) : ⇑(c • m) = c • ⇑m :=
  rfl
#align measure_theory.outer_measure.coe_smul MeasureTheory.OuterMeasure.coe_smul

theorem smul_apply (c : R) (m : OuterMeasure α) (s : Set α) : (c • m) s = c • m s :=
  rfl
#align measure_theory.outer_measure.smul_apply MeasureTheory.OuterMeasure.smul_apply

instance instSMulCommClass [SMulCommClass R R' ℝ≥0∞] : SMulCommClass R R' (OuterMeasure α) :=
  ⟨fun _ _ _ => ext fun _ => smul_comm _ _ _⟩
#align measure_theory.outer_measure.smul_comm_class MeasureTheory.OuterMeasure.instSMulCommClass

instance instIsScalarTower [SMul R R'] [IsScalarTower R R' ℝ≥0∞] :
    IsScalarTower R R' (OuterMeasure α) :=
  ⟨fun _ _ _ => ext fun _ => smul_assoc _ _ _⟩
#align measure_theory.outer_measure.is_scalar_tower MeasureTheory.OuterMeasure.instIsScalarTower

instance instIsCentralScalar [SMul Rᵐᵒᵖ ℝ≥0∞] [IsCentralScalar R ℝ≥0∞] :
    IsCentralScalar R (OuterMeasure α) :=
  ⟨fun _ _ => ext fun _ => op_smul_eq_smul _ _⟩
#align measure_theory.outer_measure.is_central_scalar MeasureTheory.OuterMeasure.instIsCentralScalar

end SMul

instance instMulAction {R : Type*} [Monoid R] [MulAction R ℝ≥0∞] [IsScalarTower R ℝ≥0∞ ℝ≥0∞] :
    MulAction R (OuterMeasure α) :=
  Injective.mulAction _ coe_fn_injective coe_smul
#align measure_theory.outer_measure.mul_action MeasureTheory.OuterMeasure.instMulAction

instance addCommMonoid : AddCommMonoid (OuterMeasure α) :=
  Injective.addCommMonoid (show OuterMeasure α → Set α → ℝ≥0∞ from _) coe_fn_injective rfl
    (fun _ _ => rfl) fun _ _ => rfl
#align measure_theory.outer_measure.add_comm_monoid MeasureTheory.OuterMeasure.addCommMonoid

/-- `(⇑)` as an `AddMonoidHom`. -/
@[simps]
def coeFnAddMonoidHom : OuterMeasure α →+ Set α → ℝ≥0∞ where
  toFun := (⇑)
  map_zero' := coe_zero
  map_add' := coe_add
#align measure_theory.outer_measure.coe_fn_add_monoid_hom MeasureTheory.OuterMeasure.coeFnAddMonoidHom

instance instDistribMulAction {R : Type*} [Monoid R] [DistribMulAction R ℝ≥0∞]
    [IsScalarTower R ℝ≥0∞ ℝ≥0∞] :
    DistribMulAction R (OuterMeasure α) :=
  Injective.distribMulAction coeFnAddMonoidHom coe_fn_injective coe_smul
#align measure_theory.outer_measure.distrib_mul_action MeasureTheory.OuterMeasure.instDistribMulAction

instance instModule {R : Type*} [Semiring R] [Module R ℝ≥0∞] [IsScalarTower R ℝ≥0∞ ℝ≥0∞] :
    Module R (OuterMeasure α) :=
  Injective.module R coeFnAddMonoidHom coe_fn_injective coe_smul
#align measure_theory.outer_measure.module MeasureTheory.OuterMeasure.instModule

instance instBot : Bot (OuterMeasure α) :=
  ⟨0⟩
#align measure_theory.outer_measure.has_bot MeasureTheory.OuterMeasure.instBot

@[simp]
theorem coe_bot : (⊥ : OuterMeasure α) = 0 :=
  rfl
#align measure_theory.outer_measure.coe_bot MeasureTheory.OuterMeasure.coe_bot

instance instPartialOrder : PartialOrder (OuterMeasure α) where
  le m₁ m₂ := ∀ s, m₁ s ≤ m₂ s
  le_refl a s := le_rfl
  le_trans a b c hab hbc s := le_trans (hab s) (hbc s)
  le_antisymm a b hab hba := ext fun s => le_antisymm (hab s) (hba s)
#align measure_theory.outer_measure.outer_measure.partial_order MeasureTheory.OuterMeasure.instPartialOrder

instance orderBot : OrderBot (OuterMeasure α) :=
  { bot := 0,
    bot_le := fun a s => by simp only [coe_zero, Pi.zero_apply, coe_bot, zero_le] }
#align measure_theory.outer_measure.outer_measure.order_bot MeasureTheory.OuterMeasure.orderBot

theorem univ_eq_zero_iff (m : OuterMeasure α) : m univ = 0 ↔ m = 0 :=
  ⟨fun h => bot_unique fun s => (measure_mono <| subset_univ s).trans_eq h, fun h => h.symm ▸ rfl⟩
#align measure_theory.outer_measure.univ_eq_zero_iff MeasureTheory.OuterMeasure.univ_eq_zero_iff

section Supremum

instance instSupSet : SupSet (OuterMeasure α) :=
  ⟨fun ms =>
    { measureOf := fun s => ⨆ m ∈ ms, (m : OuterMeasure α) s
      empty := nonpos_iff_eq_zero.1 <| iSup₂_le fun m _ => le_of_eq m.empty
      mono := fun {s₁ s₂} hs => iSup₂_mono fun m _ => m.mono hs
      iUnion_nat := fun f _ =>
        iSup₂_le fun m hm =>
          calc
            m (⋃ i, f i) ≤ ∑' i : ℕ, m (f i) := measure_iUnion_le _
            _ ≤ ∑' i, ⨆ m ∈ ms, (m : OuterMeasure α) (f i) :=
               ENNReal.tsum_le_tsum fun i => by apply le_iSup₂ m hm
             }⟩
#align measure_theory.outer_measure.has_Sup MeasureTheory.OuterMeasure.instSupSet

instance instCompleteLattice : CompleteLattice (OuterMeasure α) :=
  { OuterMeasure.orderBot,
    completeLatticeOfSup (OuterMeasure α) fun ms =>
      ⟨fun m hm s => by apply le_iSup₂ m hm, fun m hm s => iSup₂_le fun m' hm' => hm hm' s⟩ with }
#align measure_theory.outer_measure.complete_lattice MeasureTheory.OuterMeasure.instCompleteLattice

@[simp]
theorem sSup_apply (ms : Set (OuterMeasure α)) (s : Set α) :
    (sSup ms) s = ⨆ m ∈ ms, (m : OuterMeasure α) s :=
  rfl
#align measure_theory.outer_measure.Sup_apply MeasureTheory.OuterMeasure.sSup_apply

@[simp]
theorem iSup_apply {ι} (f : ι → OuterMeasure α) (s : Set α) : (⨆ i : ι, f i) s = ⨆ i, f i s := by
  rw [iSup, sSup_apply, iSup_range]
#align measure_theory.outer_measure.supr_apply MeasureTheory.OuterMeasure.iSup_apply

@[norm_cast]
theorem coe_iSup {ι} (f : ι → OuterMeasure α) : ⇑(⨆ i, f i) = ⨆ i, ⇑(f i) :=
  funext fun s => by simp
#align measure_theory.outer_measure.coe_supr MeasureTheory.OuterMeasure.coe_iSup

@[simp]
theorem sup_apply (m₁ m₂ : OuterMeasure α) (s : Set α) : (m₁ ⊔ m₂) s = m₁ s ⊔ m₂ s := by
  have := iSup_apply (fun b => cond b m₁ m₂) s; rwa [iSup_bool_eq, iSup_bool_eq] at this
#align measure_theory.outer_measure.sup_apply MeasureTheory.OuterMeasure.sup_apply

theorem smul_iSup {R : Type*} [SMul R ℝ≥0∞] [IsScalarTower R ℝ≥0∞ ℝ≥0∞]
    {ι : Sort*} (f : ι → OuterMeasure α) (c : R) :
    (c • ⨆ i, f i) = ⨆ i, c • f i :=
  ext fun s => by simp only [smul_apply, iSup_apply, ENNReal.smul_iSup]
#align measure_theory.outer_measure.smul_supr MeasureTheory.OuterMeasure.smul_iSup

end Supremum

@[mono, gcongr]
theorem mono'' {m₁ m₂ : OuterMeasure α} {s₁ s₂ : Set α} (hm : m₁ ≤ m₂) (hs : s₁ ⊆ s₂) :
    m₁ s₁ ≤ m₂ s₂ :=
  (hm s₁).trans (m₂.mono hs)
#align measure_theory.outer_measure.mono'' MeasureTheory.OuterMeasure.mono''

/-- The pushforward of `m` along `f`. The outer measure on `s` is defined to be `m (f ⁻¹' s)`. -/
def map {β} (f : α → β) : OuterMeasure α →ₗ[ℝ≥0∞] OuterMeasure β where
  toFun m :=
    { measureOf := fun s => m (f ⁻¹' s)
      empty := m.empty
      mono := fun {s t} h => m.mono (preimage_mono h)
      iUnion_nat := fun s _ => by simpa using measure_iUnion_le fun i => f ⁻¹' s i }
  map_add' m₁ m₂ := coe_fn_injective rfl
  map_smul' c m := coe_fn_injective rfl
#align measure_theory.outer_measure.map MeasureTheory.OuterMeasure.map

@[simp]
theorem map_apply {β} (f : α → β) (m : OuterMeasure α) (s : Set β) : map f m s = m (f ⁻¹' s) :=
  rfl
#align measure_theory.outer_measure.map_apply MeasureTheory.OuterMeasure.map_apply

@[simp]
theorem map_id (m : OuterMeasure α) : map id m = m :=
  ext fun _ => rfl
#align measure_theory.outer_measure.map_id MeasureTheory.OuterMeasure.map_id

@[simp]
theorem map_map {β γ} (f : α → β) (g : β → γ) (m : OuterMeasure α) :
    map g (map f m) = map (g ∘ f) m :=
  ext fun _ => rfl
#align measure_theory.outer_measure.map_map MeasureTheory.OuterMeasure.map_map

@[mono]
theorem map_mono {β} (f : α → β) : Monotone (map f) := fun _ _ h _ => h _
#align measure_theory.outer_measure.map_mono MeasureTheory.OuterMeasure.map_mono

@[simp]
theorem map_sup {β} (f : α → β) (m m' : OuterMeasure α) : map f (m ⊔ m') = map f m ⊔ map f m' :=
  ext fun s => by simp only [map_apply, sup_apply]
#align measure_theory.outer_measure.map_sup MeasureTheory.OuterMeasure.map_sup

@[simp]
theorem map_iSup {β ι} (f : α → β) (m : ι → OuterMeasure α) : map f (⨆ i, m i) = ⨆ i, map f (m i) :=
  ext fun s => by simp only [map_apply, iSup_apply]
#align measure_theory.outer_measure.map_supr MeasureTheory.OuterMeasure.map_iSup

instance instFunctor : Functor OuterMeasure where map {_ _} f := map f
#align measure_theory.outer_measure.functor MeasureTheory.OuterMeasure.instFunctor

instance instLawfulFunctor : LawfulFunctor OuterMeasure := by constructor <;> intros <;> rfl
#align measure_theory.outer_measure.is_lawful_functor MeasureTheory.OuterMeasure.instLawfulFunctor

/-- The dirac outer measure. -/
def dirac (a : α) : OuterMeasure α where
  measureOf s := indicator s (fun _ => 1) a
  empty := by simp
  mono {s t} h := indicator_le_indicator_of_subset h (fun _ => zero_le _) a
  iUnion_nat s _ := calc
    indicator (⋃ n, s n) 1 a = ⨆ n, indicator (s n) 1 a :=
      indicator_iUnion_apply (M := ℝ≥0∞) rfl _ _ _
    _ ≤ ∑' n, indicator (s n) 1 a := iSup_le fun _ ↦ ENNReal.le_tsum _
#align measure_theory.outer_measure.dirac MeasureTheory.OuterMeasure.dirac

@[simp]
theorem dirac_apply (a : α) (s : Set α) : dirac a s = indicator s (fun _ => 1) a :=
  rfl
#align measure_theory.outer_measure.dirac_apply MeasureTheory.OuterMeasure.dirac_apply

/-- The sum of an (arbitrary) collection of outer measures. -/
def sum {ι} (f : ι → OuterMeasure α) : OuterMeasure α where
  measureOf s := ∑' i, f i s
  empty := by simp
  mono {s t} h := ENNReal.tsum_le_tsum fun i => measure_mono h
  iUnion_nat s _ := by
    rw [ENNReal.tsum_comm]; exact ENNReal.tsum_le_tsum fun i => measure_iUnion_le _
#align measure_theory.outer_measure.sum MeasureTheory.OuterMeasure.sum

@[simp]
theorem sum_apply {ι} (f : ι → OuterMeasure α) (s : Set α) : sum f s = ∑' i, f i s :=
  rfl
#align measure_theory.outer_measure.sum_apply MeasureTheory.OuterMeasure.sum_apply

theorem smul_dirac_apply (a : ℝ≥0∞) (b : α) (s : Set α) :
    (a • dirac b) s = indicator s (fun _ => a) b := by
  simp only [smul_apply, smul_eq_mul, dirac_apply, ← indicator_mul_right _ fun _ => a, mul_one]
#align measure_theory.outer_measure.smul_dirac_apply MeasureTheory.OuterMeasure.smul_dirac_apply

/-- Pullback of an `OuterMeasure`: `comap f μ s = μ (f '' s)`. -/
def comap {β} (f : α → β) : OuterMeasure β →ₗ[ℝ≥0∞] OuterMeasure α where
  toFun m :=
    { measureOf := fun s => m (f '' s)
      empty := by simp
      mono := fun {s t} h => m.mono <| image_subset f h
      iUnion_nat := fun s _ => by simpa only [image_iUnion] using measure_iUnion_le _ }
  map_add' m₁ m₂ := rfl
  map_smul' c m := rfl
#align measure_theory.outer_measure.comap MeasureTheory.OuterMeasure.comap

@[simp]
theorem comap_apply {β} (f : α → β) (m : OuterMeasure β) (s : Set α) : comap f m s = m (f '' s) :=
  rfl
#align measure_theory.outer_measure.comap_apply MeasureTheory.OuterMeasure.comap_apply

@[mono]
theorem comap_mono {β} (f : α → β) : Monotone (comap f) := fun _ _ h _ => h _
#align measure_theory.outer_measure.comap_mono MeasureTheory.OuterMeasure.comap_mono

@[simp]
theorem comap_iSup {β ι} (f : α → β) (m : ι → OuterMeasure β) :
    comap f (⨆ i, m i) = ⨆ i, comap f (m i) :=
  ext fun s => by simp only [comap_apply, iSup_apply]
#align measure_theory.outer_measure.comap_supr MeasureTheory.OuterMeasure.comap_iSup

/-- Restrict an `OuterMeasure` to a set. -/
def restrict (s : Set α) : OuterMeasure α →ₗ[ℝ≥0∞] OuterMeasure α :=
  (map (↑)).comp (comap ((↑) : s → α))
#align measure_theory.outer_measure.restrict MeasureTheory.OuterMeasure.restrict

-- TODO (kmill): change `m (t ∩ s)` to `m (s ∩ t)`
@[simp]
theorem restrict_apply (s t : Set α) (m : OuterMeasure α) : restrict s m t = m (t ∩ s) := by
  simp [restrict, inter_comm t]
#align measure_theory.outer_measure.restrict_apply MeasureTheory.OuterMeasure.restrict_apply

@[mono]
theorem restrict_mono {s t : Set α} (h : s ⊆ t) {m m' : OuterMeasure α} (hm : m ≤ m') :
    restrict s m ≤ restrict t m' := fun u => by
  simp only [restrict_apply]
  exact (hm _).trans (m'.mono <| inter_subset_inter_right _ h)
#align measure_theory.outer_measure.restrict_mono MeasureTheory.OuterMeasure.restrict_mono

@[simp]
theorem restrict_univ (m : OuterMeasure α) : restrict univ m = m :=
  ext fun s => by simp
#align measure_theory.outer_measure.restrict_univ MeasureTheory.OuterMeasure.restrict_univ

@[simp]
theorem restrict_empty (m : OuterMeasure α) : restrict ∅ m = 0 :=
  ext fun s => by simp
#align measure_theory.outer_measure.restrict_empty MeasureTheory.OuterMeasure.restrict_empty

@[simp]
theorem restrict_iSup {ι} (s : Set α) (m : ι → OuterMeasure α) :
    restrict s (⨆ i, m i) = ⨆ i, restrict s (m i) := by simp [restrict]
#align measure_theory.outer_measure.restrict_supr MeasureTheory.OuterMeasure.restrict_iSup

theorem map_comap {β} (f : α → β) (m : OuterMeasure β) : map f (comap f m) = restrict (range f) m :=
  ext fun s => congr_arg m <| by simp only [image_preimage_eq_inter_range, Subtype.range_coe]
#align measure_theory.outer_measure.map_comap MeasureTheory.OuterMeasure.map_comap

theorem map_comap_le {β} (f : α → β) (m : OuterMeasure β) : map f (comap f m) ≤ m := fun _ =>
  m.mono <| image_preimage_subset _ _
#align measure_theory.outer_measure.map_comap_le MeasureTheory.OuterMeasure.map_comap_le

theorem restrict_le_self (m : OuterMeasure α) (s : Set α) : restrict s m ≤ m :=
  map_comap_le _ _
#align measure_theory.outer_measure.restrict_le_self MeasureTheory.OuterMeasure.restrict_le_self

@[simp]
theorem map_le_restrict_range {β} {ma : OuterMeasure α} {mb : OuterMeasure β} {f : α → β} :
    map f ma ≤ restrict (range f) mb ↔ map f ma ≤ mb :=
  ⟨fun h => h.trans (restrict_le_self _ _), fun h s => by simpa using h (s ∩ range f)⟩
#align measure_theory.outer_measure.map_le_restrict_range MeasureTheory.OuterMeasure.map_le_restrict_range

theorem map_comap_of_surjective {β} {f : α → β} (hf : Surjective f) (m : OuterMeasure β) :
    map f (comap f m) = m :=
  ext fun s => by rw [map_apply, comap_apply, hf.image_preimage]
#align measure_theory.outer_measure.map_comap_of_surjective MeasureTheory.OuterMeasure.map_comap_of_surjective

theorem le_comap_map {β} (f : α → β) (m : OuterMeasure α) : m ≤ comap f (map f m) := fun _ =>
  m.mono <| subset_preimage_image _ _
#align measure_theory.outer_measure.le_comap_map MeasureTheory.OuterMeasure.le_comap_map

theorem comap_map {β} {f : α → β} (hf : Injective f) (m : OuterMeasure α) : comap f (map f m) = m :=
  ext fun s => by rw [comap_apply, map_apply, hf.preimage_image]
#align measure_theory.outer_measure.comap_map MeasureTheory.OuterMeasure.comap_map

@[simp]
theorem top_apply {s : Set α} (h : s.Nonempty) : (⊤ : OuterMeasure α) s = ∞ :=
  let ⟨a, as⟩ := h
  top_unique <| le_trans (by simp [smul_dirac_apply, as]) (le_iSup₂ (∞ • dirac a) trivial)
#align measure_theory.outer_measure.top_apply MeasureTheory.OuterMeasure.top_apply

theorem top_apply' (s : Set α) : (⊤ : OuterMeasure α) s = ⨅ h : s = ∅, 0 :=
  s.eq_empty_or_nonempty.elim (fun h => by simp [h]) fun h => by simp [h, h.ne_empty]
#align measure_theory.outer_measure.top_apply' MeasureTheory.OuterMeasure.top_apply'

@[simp]
theorem comap_top (f : α → β) : comap f ⊤ = ⊤ :=
  ext_nonempty fun s hs => by rw [comap_apply, top_apply hs, top_apply (hs.image _)]
#align measure_theory.outer_measure.comap_top MeasureTheory.OuterMeasure.comap_top

theorem map_top (f : α → β) : map f ⊤ = restrict (range f) ⊤ :=
  ext fun s => by
    rw [map_apply, restrict_apply, ← image_preimage_eq_inter_range, top_apply', top_apply',
      Set.image_eq_empty]
#align measure_theory.outer_measure.map_top MeasureTheory.OuterMeasure.map_top

@[simp]
theorem map_top_of_surjective (f : α → β) (hf : Surjective f) : map f ⊤ = ⊤ := by
  rw [map_top, hf.range_eq, restrict_univ]
#align measure_theory.outer_measure.map_top_of_surjective MeasureTheory.OuterMeasure.map_top_of_surjective

end Basic

end OuterMeasure
