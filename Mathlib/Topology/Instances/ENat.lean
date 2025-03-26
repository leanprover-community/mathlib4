/-
Copyright (c) 2022 Peter Nelson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Nelson, Kalle Kytölä
-/
import Mathlib.Data.ENat.Basic
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Instances.Discrete
import Mathlib.Order.Interval.Set.WithBotTop
import Mathlib.Topology.Order.T5

/-!
# Topology on the extended natural numbers
-/

noncomputable section

open Set Filter Function Topology
open scoped ENat

variable {α : Type*} {β : Type*} {γ : Type*}

namespace ENat

variable {a b c d : ℕ∞} {r p q : ℕ} {x y z : ℕ∞} {s : Set ℕ∞}

open TopologicalSpace

/-- Topology on `ℕ∞`.

Note: this is different from the `EMetricSpace` topology. The `EMetricSpace` topology has
`IsOpen {∞}`, while all neighborhoods of `∞` in `ℕ∞` contain infinite intervals. -/
instance : TopologicalSpace ℕ∞ := Preorder.topology ℕ∞

instance : OrderTopology ℕ∞ := ⟨rfl⟩

example : OrderClosedTopology ℕ∞ := by infer_instance

-- short-circuit type class inference
instance : T2Space ℕ∞ := inferInstance
instance : T5Space ℕ∞ := inferInstance
instance : T4Space ℕ∞ := inferInstance

theorem isEmbedding_natCast : IsEmbedding ((↑) : ℕ → ℕ∞) :=
  Nat.strictMono_cast.isEmbedding_of_ordConnected <| range_natCast ▸ ordConnected_Iio

@[deprecated (since := "2024-10-26")]
alias embedding_natCast := isEmbedding_natCast

theorem isOpenEmbedding_natCast : IsOpenEmbedding ((↑) : ℕ → ℕ∞) :=
  ⟨isEmbedding_natCast, range_natCast ▸ isOpen_Iio⟩

@[deprecated (since := "2024-10-18")]
alias openEmbedding_natCast := isOpenEmbedding_natCast

theorem nhds_natCast (n : ℕ) : 𝓝 (n : ℕ∞) = pure (n : ℕ∞) := by
  simp [← isOpenEmbedding_natCast.map_nhds_eq]

@[simp]
protected theorem nhds_eq_pure {n : ℕ∞} (h : n ≠ ⊤) : 𝓝 n = pure n := by
  lift n to ℕ using h
  simp [nhds_natCast]

theorem isOpen_singleton {x : ℕ∞} (hx : x ≠ ⊤) : IsOpen {x} := by
  rw [isOpen_singleton_iff_nhds_eq_pure, ENat.nhds_eq_pure hx]

theorem mem_nhds_iff {x : ℕ∞} {s : Set ℕ∞} (hx : x ≠ ⊤) : s ∈ 𝓝 x ↔ x ∈ s := by
  simp [hx]

theorem mem_nhds_natCast_iff (n : ℕ) {s : Set ℕ∞} : s ∈ 𝓝 (n : ℕ∞) ↔ (n : ℕ∞) ∈ s :=
  mem_nhds_iff (coe_ne_top _)

theorem tendsto_nhds_top_iff_natCast_lt {α : Type*} {l : Filter α} {f : α → ℕ∞} :
    Tendsto f l (𝓝 ⊤) ↔ ∀ n : ℕ, ∀ᶠ a in l, n < f a := by
  simp_rw [nhds_top_order, lt_top_iff_ne_top, tendsto_iInf, tendsto_principal]
  exact Option.ball_ne_none

instance : ContinuousAdd ℕ∞ := by
  refine ⟨continuous_iff_continuousAt.2 fun (a, b) ↦ ?_⟩
  match a, b with
  | ⊤, _ => exact tendsto_nhds_top_mono' continuousAt_fst fun p ↦ le_add_right le_rfl
  | (a : ℕ), ⊤ => exact tendsto_nhds_top_mono' continuousAt_snd fun p ↦ le_add_left le_rfl
  | (a : ℕ), (b : ℕ) => simp [ContinuousAt, nhds_prod_eq, tendsto_pure_nhds]

instance : ContinuousMul ℕ∞ where
  continuous_mul :=
    have key (a : ℕ∞) : ContinuousAt (· * ·).uncurry (a, ⊤) := by
      rcases (zero_le a).eq_or_gt with rfl | ha
      · simp [ContinuousAt, nhds_prod_eq]
      · simp only [ContinuousAt, Function.uncurry, mul_top ha.ne']
        refine tendsto_nhds_top_mono continuousAt_snd ?_
        filter_upwards [continuousAt_fst (lt_mem_nhds ha)] with (x, y) (hx : 0 < x)
        exact le_mul_of_one_le_left (zero_le y) (Order.one_le_iff_pos.2 hx)
    continuous_iff_continuousAt.2 <| Prod.forall.2 fun
      | (a : ℕ∞), ⊤ => key a
      | ⊤, (b : ℕ∞) =>
        ((key b).comp_of_eq (continuous_swap.tendsto (⊤, b)) rfl).congr <|
          .of_forall fun _ ↦ mul_comm ..
      | (a : ℕ), (b : ℕ) => by
        simp [ContinuousAt, nhds_prod_eq, tendsto_pure_nhds]

protected theorem continuousAt_sub {a b : ℕ∞} (h : a ≠ ⊤ ∨ b ≠ ⊤) :
    ContinuousAt (· - ·).uncurry (a, b) := by
  match a, b, h with
  | (a : ℕ), (b : ℕ), _ => simp [ContinuousAt, nhds_prod_eq]
  | (a : ℕ), ⊤, _ =>
    suffices ∀ᶠ b in 𝓝 ⊤, (a - b : ℕ∞) = 0 by
      simpa [ContinuousAt, nhds_prod_eq, tsub_eq_zero_of_le]
    filter_upwards [le_mem_nhds (WithTop.coe_lt_top a)] with b using tsub_eq_zero_of_le
  | ⊤, (b : ℕ), _ =>
    suffices ∀ n : ℕ, ∀ᶠ a : ℕ∞ in 𝓝 ⊤, b + n < a by
      simpa [ContinuousAt, nhds_prod_eq, (· ∘ ·), lt_tsub_iff_left, tendsto_nhds_top_iff_natCast_lt]
    exact fun n ↦ lt_mem_nhds <| WithTop.coe_lt_top (b + n)

theorem isOpen_ne_top : IsOpen {a : ℕ∞ | a ≠ ⊤} := isOpen_ne

theorem isOpen_Ico_zero : IsOpen (Ico 0 b) := by rw [ENat.Ico_eq_Iio]; exact isOpen_Iio

theorem continuous_coe_iff {α} [TopologicalSpace α] {f : α → ℕ} :
    (Continuous fun a ↦ (f a : ℕ∞)) ↔ Continuous f :=
  isEmbedding_natCast.continuous_iff.symm

theorem nhds_coe {r : ℕ} : 𝓝 (r : ℕ∞) = (𝓝 r).map (↑) :=
  (isOpenEmbedding_natCast.map_nhds_eq r).symm

theorem nhds_top : 𝓝 (⊤ : ℕ∞) = ⨅ (a) (_ : a ≠ ⊤), 𝓟 (Ioi a) :=
  nhds_top_order.trans <| by simp [lt_top_iff_ne_top, Ioi]

theorem nhds_top_hasBasis : (𝓝 (⊤ : ℕ∞)).HasBasis (fun a ↦ a < ⊤) fun a ↦ Ioi a :=
  _root_.nhds_top_basis

lemma isOpen_Ico : IsOpen (Ico a b) := by
  by_cases a_zero : a = 0
  · simpa [a_zero, ENat.Ico_eq_Iio] using isOpen_Iio
  · simpa [ENat.Ico_eq_Ioo a_zero b] using isOpen_Ioo

lemma isOpen_Ioc : IsOpen (Ioc a b) := by
  by_cases b_top : b = ⊤
  · simpa [b_top, ENat.Ioc_eq_Ioi] using isOpen_Ioi
  · simpa [ENat.Ioc_eq_Ioo a b_top] using isOpen_Ioo

lemma isOpen_Icc (h : a ≠ ⊤ ∨ b ≠ ⊤) : IsOpen (Icc a b) := by
  by_cases b_top : b = ⊤
  · simp only [ne_eq, b_top, not_true_eq_false, or_false, Icc_top] at h ⊢
    by_cases a_zero : a = 0
    · convert isOpen_univ
      ext x
      simp [a_zero]
    · simpa [ENat.Ici_eq_Ioi a_zero h] using isOpen_Ioi
  · simpa [ENat.Icc_eq_Ico _ b_top] using isOpen_Ico

@[simp] lemma mem_nhds_iff_of_ne_top {n : ℕ∞} (n_ne_top : n ≠ ⊤) (s : Set ℕ∞) :
    s ∈ 𝓝 n ↔ n ∈ s := by
  refine ⟨fun h ↦ mem_of_mem_nhds h, fun h ↦ ?_⟩
  apply mem_of_superset ((ENat.isOpen_singleton n_ne_top).mem_nhds rfl)
  exact singleton_subset_iff.mpr h

theorem tendsto_nhds_coe_iff {α : Type*} {l : Filter α} {x : ℕ} {f : ℕ∞ → α} :
    Tendsto f (𝓝 ↑x) l ↔ Tendsto (f ∘ (↑) : ℕ → α) (𝓝 x) l := by
  rw [nhds_coe, tendsto_map'_iff]

theorem continuousAt_coe_iff {α : Type*} [TopologicalSpace α] {x : ℕ} {f : ℕ∞ → α} :
    ContinuousAt f ↑x ↔ ContinuousAt (f ∘ (↑) : ℕ → α) x :=
  tendsto_nhds_coe_iff

theorem nhds_coe_coe {r p : ℕ} :
    𝓝 ((r : ℕ∞), (p : ℕ∞)) = (𝓝 (r, p)).map fun p : ℕ × ℕ => (↑p.1, ↑p.2) :=
  ((isOpenEmbedding_natCast.prodMap isOpenEmbedding_natCast).map_nhds_eq (r, p)).symm

theorem tendsto_toNat {a : ℕ∞} (ha : a ≠ ⊤) :
    Tendsto ENat.toNat (𝓝 a) (𝓝 a.toNat) := by
  lift a to ℕ using ha
  rw [nhds_coe, tendsto_map'_iff]
  exact tendsto_id

theorem eventuallyEq_of_toNat_eventuallyEq {l : Filter α} {f g : α → ℕ∞}
    (hfi : ∀ᶠ x in l, f x ≠ ⊤) (hgi : ∀ᶠ x in l, g x ≠ ⊤)
    (hfg : (fun x => (f x).toNat) =ᶠ[l] fun x => (g x).toNat) : f =ᶠ[l] g := by
  filter_upwards [hfi, hgi, hfg] with _ hfx hgx _
  rwa [← ENat.toNat_eq_toNat hfx hgx]

theorem continuousOn_toNat : ContinuousOn ENat.toNat {a | a ≠ ⊤} := fun _a ha =>
  ContinuousAt.continuousWithinAt (tendsto_toNat ha)

lemma continuousAt_toNat (hx : x ≠ ⊤) : ContinuousAt ENat.toNat x :=
  continuousOn_toNat.continuousAt (isOpen_ne_top.mem_nhds_iff.mpr hx)

theorem tendsto_nhds_top_iff_nat {m : α → ℕ∞} {f : Filter α} :
    Tendsto m f (𝓝 ⊤) ↔ ∀ n : ℕ, ∀ᶠ i in f, n < m i := by
  simp only [nhds_top, ne_eq, tendsto_iInf, tendsto_principal, mem_Ioi]
  exact ⟨fun h k ↦ h k (coe_ne_top k), fun h n n_ne_top ↦ (coe_toNat n_ne_top).symm ▸ h n.toNat⟩

end ENat

theorem Filter.Tendsto.enatSub {α : Type*} {l : Filter α} {f g : α → ℕ∞} {a b : ℕ∞}
    (hf : Tendsto f l (𝓝 a)) (hg : Tendsto g l (𝓝 b)) (h : a ≠ ⊤ ∨ b ≠ ⊤) :
    Tendsto (fun x ↦ f x - g x) l (𝓝 (a - b)) :=
  (ENat.continuousAt_sub h).tendsto.comp (hf.prodMk_nhds hg)

variable {X : Type*} [TopologicalSpace X] {f g : X → ℕ∞} {s : Set X} {x : X}

nonrec theorem ContinuousWithinAt.enatSub
    (hf : ContinuousWithinAt f s x) (hg : ContinuousWithinAt g s x) (h : f x ≠ ⊤ ∨ g x ≠ ⊤) :
    ContinuousWithinAt (fun x ↦ f x - g x) s x :=
  hf.enatSub hg h

nonrec theorem ContinuousAt.enatSub
    (hf : ContinuousAt f x) (hg : ContinuousAt g x) (h : f x ≠ ⊤ ∨ g x ≠ ⊤) :
    ContinuousAt (fun x ↦ f x - g x) x :=
  hf.enatSub hg h

nonrec theorem ContinuousOn.enatSub
    (hf : ContinuousOn f s) (hg : ContinuousOn g s) (h : ∀ x ∈ s, f x ≠ ⊤ ∨ g x ≠ ⊤) :
    ContinuousOn (fun x ↦ f x - g x) s := fun x hx ↦
  (hf x hx).enatSub (hg x hx) (h x hx)

nonrec theorem Continuous.enatSub
    (hf : Continuous f) (hg : Continuous g) (h : ∀ x, f x ≠ ⊤ ∨ g x ≠ ⊤) :
    Continuous (fun x ↦ f x - g x) :=
  continuous_iff_continuousAt.2 fun x ↦ hf.continuousAt.enatSub hg.continuousAt (h x)
