/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Yury Kudryashov
-/
import Mathlib.Order.Filter.Interval
import Mathlib.Order.Interval.Set.Pi
import Mathlib.Tactic.TFAE
import Mathlib.Tactic.NormNum
import Mathlib.Topology.Order.LeftRight
import Mathlib.Topology.Order.OrderClosed

/-!
# Theory of topology on ordered spaces

## Main definitions

The order topology on an ordered space is the topology generated by all open intervals (or
equivalently by those of the form `(-∞, a)` and `(b, +∞)`). We define it as `Preorder.topology α`.
However, we do *not* register it as an instance (as many existing ordered types already have
topologies, which would be equal but not definitionally equal to `Preorder.topology α`). Instead,
we introduce a class `OrderTopology α` (which is a `Prop`, also known as a mixin) saying that on
the type `α` having already a topological space structure and a preorder structure, the topological
structure is equal to the order topology.

We prove many basic properties of such topologies.

## Main statements

This file contains the proofs of the following facts. For exact requirements
(`OrderClosedTopology` vs `OrderTopology`, `Preorder` vs `PartialOrder` vs `LinearOrder` etc)
see their statements.

* `exists_Ioc_subset_of_mem_nhds`, `exists_Ico_subset_of_mem_nhds` : if `x < y`, then any
  neighborhood of `x` includes an interval `[x, z)` for some `z ∈ (x, y]`, and any neighborhood
  of `y` includes an interval `(z, y]` for some `z ∈ [x, y)`.
* `tendsto_of_tendsto_of_tendsto_of_le_of_le` : theorem known as squeeze theorem,
  sandwich theorem, theorem of Carabinieri, and two policemen (and a drunk) theorem; if `g` and `h`
  both converge to `a`, and eventually `g x ≤ f x ≤ h x`, then `f` converges to `a`.

## Implementation notes

We do _not_ register the order topology as an instance on a preorder (or even on a linear order).
Indeed, on many such spaces, a topology has already been constructed in a different way (think
of the discrete spaces `ℕ` or `ℤ`, or `ℝ` that could inherit a topology as the completion of `ℚ`),
and is in general not defeq to the one generated by the intervals. We make it available as a
definition `Preorder.topology α` though, that can be registered as an instance when necessary, or
for specific types.
-/


open Set Filter TopologicalSpace Topology Function

open OrderDual (toDual ofDual)

universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}

-- Porting note (https://github.com/leanprover-community/mathlib4/issues/11215): TODO: define `Preorder.topology` before `OrderTopology` and reuse the def
/-- The order topology on an ordered type is the topology generated by open intervals. We register
it on a preorder, but it is mostly interesting in linear orders, where it is also order-closed.
We define it as a mixin. If you want to introduce the order topology on a preorder, use
`Preorder.topology`. -/
class OrderTopology (α : Type*) [t : TopologicalSpace α] [Preorder α] : Prop where
  /-- The topology is generated by open intervals `Set.Ioi _` and `Set.Iio _`. -/
  topology_eq_generate_intervals : t = generateFrom { s | ∃ a, s = Ioi a ∨ s = Iio a }

/-- (Order) topology on a partial order `α` generated by the subbase of open intervals
`(a, ∞) = { x ∣ a < x }, (-∞ , b) = {x ∣ x < b}` for all `a, b` in `α`. We do not register it as an
instance as many ordered sets are already endowed with the same topology, most often in a non-defeq
way though. Register as a local instance when necessary. -/
def Preorder.topology (α : Type*) [Preorder α] : TopologicalSpace α :=
  generateFrom { s : Set α | ∃ a : α, s = { b : α | a < b } ∨ s = { b : α | b < a } }

section OrderTopology

section Preorder

variable [TopologicalSpace α] [Preorder α]

instance [t : OrderTopology α] : OrderTopology αᵒᵈ :=
  ⟨by
    convert OrderTopology.topology_eq_generate_intervals (α := α) using 6
    apply or_comm⟩

theorem isOpen_iff_generate_intervals [t : OrderTopology α] {s : Set α} :
    IsOpen s ↔ GenerateOpen { s | ∃ a, s = Ioi a ∨ s = Iio a } s := by
  rw [t.topology_eq_generate_intervals]; rfl

theorem isOpen_lt' [OrderTopology α] (a : α) : IsOpen { b : α | a < b } :=
  isOpen_iff_generate_intervals.2 <| .basic _ ⟨a, .inl rfl⟩

theorem isOpen_gt' [OrderTopology α] (a : α) : IsOpen { b : α | b < a } :=
  isOpen_iff_generate_intervals.2 <| .basic _ ⟨a, .inr rfl⟩

theorem lt_mem_nhds [OrderTopology α] {a b : α} (h : a < b) : ∀ᶠ x in 𝓝 b, a < x :=
  (isOpen_lt' _).mem_nhds h

theorem le_mem_nhds [OrderTopology α] {a b : α} (h : a < b) : ∀ᶠ x in 𝓝 b, a ≤ x :=
  (lt_mem_nhds h).mono fun _ => le_of_lt

theorem gt_mem_nhds [OrderTopology α] {a b : α} (h : a < b) : ∀ᶠ x in 𝓝 a, x < b :=
  (isOpen_gt' _).mem_nhds h

theorem ge_mem_nhds [OrderTopology α] {a b : α} (h : a < b) : ∀ᶠ x in 𝓝 a, x ≤ b :=
  (gt_mem_nhds h).mono fun _ => le_of_lt

theorem nhds_eq_order [OrderTopology α] (a : α) :
    𝓝 a = (⨅ b ∈ Iio a, 𝓟 (Ioi b)) ⊓ ⨅ b ∈ Ioi a, 𝓟 (Iio b) := by
  rw [OrderTopology.topology_eq_generate_intervals (α := α), nhds_generateFrom]
  simp_rw [mem_setOf_eq, @and_comm (a ∈ _), exists_or, or_and_right, iInf_or, iInf_and,
    iInf_exists, iInf_inf_eq, iInf_comm (ι := Set α), iInf_iInf_eq_left, mem_Ioi, mem_Iio]

theorem tendsto_order [OrderTopology α] {f : β → α} {a : α} {x : Filter β} :
    Tendsto f x (𝓝 a) ↔ (∀ a' < a, ∀ᶠ b in x, a' < f b) ∧ ∀ a' > a, ∀ᶠ b in x, f b < a' := by
  simp only [nhds_eq_order a, tendsto_inf, tendsto_iInf, tendsto_principal]; rfl
instance tendstoIccClassNhds [OrderTopology α] (a : α) : TendstoIxxClass Icc (𝓝 a) (𝓝 a) := by
  simp only [nhds_eq_order, iInf_subtype']
  refine
    ((hasBasis_iInf_principal_finite _).inf (hasBasis_iInf_principal_finite _)).tendstoIxxClass
      fun s _ => ?_
  refine ((ordConnected_biInter ?_).inter (ordConnected_biInter ?_)).out <;> intro _ _
  exacts [ordConnected_Ioi, ordConnected_Iio]

instance tendstoIcoClassNhds [OrderTopology α] (a : α) : TendstoIxxClass Ico (𝓝 a) (𝓝 a) :=
  tendstoIxxClass_of_subset fun _ _ => Ico_subset_Icc_self

instance tendstoIocClassNhds [OrderTopology α] (a : α) : TendstoIxxClass Ioc (𝓝 a) (𝓝 a) :=
  tendstoIxxClass_of_subset fun _ _ => Ioc_subset_Icc_self

instance tendstoIooClassNhds [OrderTopology α] (a : α) : TendstoIxxClass Ioo (𝓝 a) (𝓝 a) :=
  tendstoIxxClass_of_subset fun _ _ => Ioo_subset_Icc_self

/-- **Squeeze theorem** (also known as **sandwich theorem**). This version assumes that inequalities
hold eventually for the filter. -/
theorem tendsto_of_tendsto_of_tendsto_of_le_of_le' [OrderTopology α] {f g h : β → α} {b : Filter β}
    {a : α} (hg : Tendsto g b (𝓝 a)) (hh : Tendsto h b (𝓝 a)) (hgf : ∀ᶠ b in b, g b ≤ f b)
    (hfh : ∀ᶠ b in b, f b ≤ h b) : Tendsto f b (𝓝 a) :=
  (hg.Icc hh).of_smallSets <| hgf.and hfh

/-- **Squeeze theorem** (also known as **sandwich theorem**). This version assumes that inequalities
hold everywhere. -/
theorem tendsto_of_tendsto_of_tendsto_of_le_of_le [OrderTopology α] {f g h : β → α} {b : Filter β}
    {a : α} (hg : Tendsto g b (𝓝 a)) (hh : Tendsto h b (𝓝 a)) (hgf : g ≤ f) (hfh : f ≤ h) :
    Tendsto f b (𝓝 a) :=
  tendsto_of_tendsto_of_tendsto_of_le_of_le' hg hh (Eventually.of_forall hgf)
    (Eventually.of_forall hfh)

theorem nhds_order_unbounded [OrderTopology α] {a : α} (hu : ∃ u, a < u) (hl : ∃ l, l < a) :
    𝓝 a = ⨅ (l) (_ : l < a) (u) (_ : a < u), 𝓟 (Ioo l u) := by
  simp only [nhds_eq_order, ← inf_biInf, ← biInf_inf, *, ← inf_principal, ← Ioi_inter_Iio]; rfl

theorem tendsto_order_unbounded [OrderTopology α] {f : β → α} {a : α} {x : Filter β}
    (hu : ∃ u, a < u) (hl : ∃ l, l < a) (h : ∀ l u, l < a → a < u → ∀ᶠ b in x, l < f b ∧ f b < u) :
    Tendsto f x (𝓝 a) := by
  simp only [nhds_order_unbounded hu hl, tendsto_iInf, tendsto_principal]
  exact fun l hl u => h l u hl

end Preorder

instance tendstoIxxNhdsWithin {α : Type*} [TopologicalSpace α] (a : α) {s t : Set α}
    {Ixx} [TendstoIxxClass Ixx (𝓝 a) (𝓝 a)] [TendstoIxxClass Ixx (𝓟 s) (𝓟 t)] :
    TendstoIxxClass Ixx (𝓝[s] a) (𝓝[t] a) :=
  Filter.tendstoIxxClass_inf

instance tendstoIccClassNhdsPi {ι : Type*} {α : ι → Type*} [∀ i, Preorder (α i)]
    [∀ i, TopologicalSpace (α i)] [∀ i, OrderTopology (α i)] (f : ∀ i, α i) :
    TendstoIxxClass Icc (𝓝 f) (𝓝 f) := by
  constructor
  conv in (𝓝 f).smallSets => rw [nhds_pi, Filter.pi]
  simp only [smallSets_iInf, smallSets_comap_eq_comap_image, tendsto_iInf, tendsto_comap_iff]
  intro i
  have : Tendsto (fun g : ∀ i, α i => g i) (𝓝 f) (𝓝 (f i)) := (continuous_apply i).tendsto f
  refine (this.comp tendsto_fst).Icc (this.comp tendsto_snd) |>.smallSets_mono ?_
  filter_upwards [] using fun ⟨f, g⟩ ↦ image_subset_iff.mpr fun p hp ↦ ⟨hp.1 i, hp.2 i⟩

theorem induced_topology_le_preorder [Preorder α] [Preorder β] [TopologicalSpace β]
    [OrderTopology β] {f : α → β} (hf : ∀ {x y}, f x < f y ↔ x < y) :
    induced f ‹TopologicalSpace β› ≤ Preorder.topology α := by
  let _ := Preorder.topology α; have : OrderTopology α := ⟨rfl⟩
  refine le_of_nhds_le_nhds fun x => ?_
  simp only [nhds_eq_order, nhds_induced, comap_inf, comap_iInf, comap_principal, Ioi, Iio, ← hf]
  refine inf_le_inf (le_iInf₂ fun a ha => ?_) (le_iInf₂ fun a ha => ?_)
  exacts [iInf₂_le (f a) ha, iInf₂_le (f a) ha]

theorem induced_topology_eq_preorder [Preorder α] [Preorder β] [TopologicalSpace β]
    [OrderTopology β] {f : α → β} (hf : ∀ {x y}, f x < f y ↔ x < y)
    (H₁ : ∀ {a b x}, b < f a → ¬(b < f x) → ∃ y, y < a ∧ b ≤ f y)
    (H₂ : ∀ {a b x}, f a < b → ¬(f x < b) → ∃ y, a < y ∧ f y ≤ b) :
    induced f ‹TopologicalSpace β› = Preorder.topology α := by
  let _ := Preorder.topology α; have : OrderTopology α := ⟨rfl⟩
  refine le_antisymm (induced_topology_le_preorder hf) ?_
  refine le_of_nhds_le_nhds fun a => ?_
  simp only [nhds_eq_order, nhds_induced, comap_inf, comap_iInf, comap_principal]
  refine inf_le_inf (le_iInf₂ fun b hb => ?_) (le_iInf₂ fun b hb => ?_)
  · rcases em (∃ x, ¬(b < f x)) with (⟨x, hx⟩ | hb)
    · rcases H₁ hb hx with ⟨y, hya, hyb⟩
      exact iInf₂_le_of_le y hya (principal_mono.2 fun z hz => hyb.trans_lt (hf.2 hz))
    · push_neg at hb
      exact le_principal_iff.2 (univ_mem' hb)
  · rcases em (∃ x, ¬(f x < b)) with (⟨x, hx⟩ | hb)
    · rcases H₂ hb hx with ⟨y, hya, hyb⟩
      exact iInf₂_le_of_le y hya (principal_mono.2 fun z hz => (hf.2 hz).trans_le hyb)
    · push_neg at hb
      exact le_principal_iff.2 (univ_mem' hb)

theorem induced_orderTopology' {α : Type u} {β : Type v} [Preorder α] [ta : TopologicalSpace β]
    [Preorder β] [OrderTopology β] (f : α → β) (hf : ∀ {x y}, f x < f y ↔ x < y)
    (H₁ : ∀ {a x}, x < f a → ∃ b < a, x ≤ f b) (H₂ : ∀ {a x}, f a < x → ∃ b > a, f b ≤ x) :
    @OrderTopology _ (induced f ta) _ :=
  let _ := induced f ta
  ⟨induced_topology_eq_preorder hf (fun h _ => H₁ h) (fun h _ => H₂ h)⟩

theorem induced_orderTopology {α : Type u} {β : Type v} [Preorder α] [ta : TopologicalSpace β]
    [Preorder β] [OrderTopology β] (f : α → β) (hf : ∀ {x y}, f x < f y ↔ x < y)
    (H : ∀ {x y}, x < y → ∃ a, x < f a ∧ f a < y) : @OrderTopology _ (induced f ta) _ :=
  induced_orderTopology' f (hf)
    (fun xa => let ⟨b, xb, ba⟩ := H xa; ⟨b, hf.1 ba, le_of_lt xb⟩)
    fun ax => let ⟨b, ab, bx⟩ := H ax; ⟨b, hf.1 ab, le_of_lt bx⟩

/-- The topology induced by a strictly monotone function with order-connected range is the preorder
topology. -/
nonrec theorem StrictMono.induced_topology_eq_preorder {α β : Type*} [LinearOrder α]
    [LinearOrder β] [t : TopologicalSpace β] [OrderTopology β] {f : α → β}
    (hf : StrictMono f) (hc : OrdConnected (range f)) : t.induced f = Preorder.topology α := by
  refine induced_topology_eq_preorder hf.lt_iff_lt (fun h₁ h₂ => ?_) fun h₁ h₂ => ?_
  · rcases hc.out (mem_range_self _) (mem_range_self _) ⟨not_lt.1 h₂, h₁.le⟩ with ⟨y, rfl⟩
    exact ⟨y, hf.lt_iff_lt.1 h₁, le_rfl⟩
  · rcases hc.out (mem_range_self _) (mem_range_self _) ⟨h₁.le, not_lt.1 h₂⟩ with ⟨y, rfl⟩
    exact ⟨y, hf.lt_iff_lt.1 h₁, le_rfl⟩

/-- A strictly monotone function between linear orders with order topology is a topological
embedding provided that the range of `f` is order-connected. -/
theorem StrictMono.isEmbedding_of_ordConnected {α β : Type*} [LinearOrder α] [LinearOrder β]
    [TopologicalSpace α] [h : OrderTopology α] [TopologicalSpace β] [OrderTopology β] {f : α → β}
    (hf : StrictMono f) (hc : OrdConnected (range f)) : IsEmbedding f :=
  ⟨⟨h.1.trans <| Eq.symm <| hf.induced_topology_eq_preorder hc⟩, hf.injective⟩

@[deprecated (since := "2024-10-26")]
alias StrictMono.embedding_of_ordConnected := StrictMono.isEmbedding_of_ordConnected

/-- On a `Set.OrdConnected` subset of a linear order, the order topology for the restriction of the
order is the same as the restriction to the subset of the order topology. -/
instance orderTopology_of_ordConnected {α : Type u} [TopologicalSpace α] [LinearOrder α]
    [OrderTopology α] {t : Set α} [ht : OrdConnected t] : OrderTopology t :=
  ⟨(Subtype.strictMono_coe t).induced_topology_eq_preorder <| by
    rwa [← @Subtype.range_val _ t] at ht⟩

theorem nhdsGE_eq'' [TopologicalSpace α] [Preorder α] [OrderTopology α] (a : α) :
    𝓝[≥] a = (⨅ (u) (_ : a < u), 𝓟 (Iio u)) ⊓ 𝓟 (Ici a) := by
  rw [nhdsWithin, nhds_eq_order]
  refine le_antisymm (inf_le_inf_right _ inf_le_right) (le_inf (le_inf ?_ inf_le_left) inf_le_right)
  exact inf_le_right.trans (le_iInf₂ fun l hl => principal_mono.2 <| Ici_subset_Ioi.2 hl)

@[deprecated (since := "2024-12-22")] alias nhdsWithin_Ici_eq'' := nhdsGE_eq''

theorem nhdsLE_eq'' [TopologicalSpace α] [Preorder α] [OrderTopology α] (a : α) :
    𝓝[≤] a = (⨅ l < a, 𝓟 (Ioi l)) ⊓ 𝓟 (Iic a) :=
  nhdsGE_eq'' (toDual a)

@[deprecated (since := "2024-12-22")] alias nhdsWithin_Iic_eq'' := nhdsLE_eq''

theorem nhdsGE_eq' [TopologicalSpace α] [Preorder α] [OrderTopology α] {a : α} (ha : ∃ u, a < u) :
    𝓝[≥] a = ⨅ (u) (_ : a < u), 𝓟 (Ico a u) := by
  simp only [nhdsGE_eq'', biInf_inf ha, inf_principal, Iio_inter_Ici]

@[deprecated (since := "2024-12-22")]
alias nhdsWithin_Ici_eq' := nhdsGE_eq'

theorem nhdsLE_eq' [TopologicalSpace α] [Preorder α] [OrderTopology α] {a : α} (ha : ∃ l, l < a) :
    𝓝[≤] a = ⨅ l < a, 𝓟 (Ioc l a) := by
  simp only [nhdsLE_eq'', biInf_inf ha, inf_principal, Ioi_inter_Iic]

@[deprecated (since := "2024-12-22")] alias nhdsWithin_Iic_eq' := nhdsLE_eq'

theorem nhdsGE_basis' [TopologicalSpace α] [LinearOrder α] [OrderTopology α] {a : α}
    (ha : ∃ u, a < u) : (𝓝[≥] a).HasBasis (fun u => a < u) fun u => Ico a u :=
  (nhdsGE_eq' ha).symm ▸
    hasBasis_biInf_principal
      (fun b hb c hc => ⟨min b c, lt_min hb hc, Ico_subset_Ico_right (min_le_left _ _),
        Ico_subset_Ico_right (min_le_right _ _)⟩)
      ha

@[deprecated (since := "2024-12-22")] alias nhdsWithin_Ici_basis' := nhdsGE_basis'

theorem nhdsLE_basis' [TopologicalSpace α] [LinearOrder α] [OrderTopology α] {a : α}
    (ha : ∃ l, l < a) : (𝓝[≤] a).HasBasis (fun l => l < a) fun l => Ioc l a := by
  convert nhdsGE_basis' (α := αᵒᵈ) ha using 2
  exact dual_Ico.symm

@[deprecated (since := "2024-12-22")] alias nhdsWithin_Iic_basis' := nhdsLE_basis'

theorem nhdsGE_basis [TopologicalSpace α] [LinearOrder α] [OrderTopology α] [NoMaxOrder α] (a : α) :
    (𝓝[≥] a).HasBasis (fun u => a < u) fun u => Ico a u :=
  nhdsGE_basis' (exists_gt a)

@[deprecated (since := "2024-12-22")] alias nhdsWithin_Ici_basis := nhdsGE_basis

theorem nhdsLE_basis [TopologicalSpace α] [LinearOrder α] [OrderTopology α] [NoMinOrder α] (a : α) :
    (𝓝[≤] a).HasBasis (fun l => l < a) fun l => Ioc l a :=
  nhdsLE_basis' (exists_lt a)

@[deprecated (since := "2024-12-22")] alias nhdsWithin_Iic_basis := nhdsLE_basis

theorem nhds_top_order [TopologicalSpace α] [Preorder α] [OrderTop α] [OrderTopology α] :
    𝓝 (⊤ : α) = ⨅ (l) (_ : l < ⊤), 𝓟 (Ioi l) := by simp [nhds_eq_order (⊤ : α)]

theorem nhds_bot_order [TopologicalSpace α] [Preorder α] [OrderBot α] [OrderTopology α] :
    𝓝 (⊥ : α) = ⨅ (l) (_ : ⊥ < l), 𝓟 (Iio l) := by simp [nhds_eq_order (⊥ : α)]

theorem nhds_top_basis [TopologicalSpace α] [LinearOrder α] [OrderTop α] [OrderTopology α]
    [Nontrivial α] : (𝓝 ⊤).HasBasis (fun a : α => a < ⊤) fun a : α => Ioi a := by
  have : ∃ x : α, x < ⊤ := (exists_ne ⊤).imp fun x hx => hx.lt_top
  simpa only [Iic_top, nhdsWithin_univ, Ioc_top] using nhdsLE_basis' this

theorem nhds_bot_basis [TopologicalSpace α] [LinearOrder α] [OrderBot α] [OrderTopology α]
    [Nontrivial α] : (𝓝 ⊥).HasBasis (fun a : α => ⊥ < a) fun a : α => Iio a :=
  nhds_top_basis (α := αᵒᵈ)

theorem nhds_top_basis_Ici [TopologicalSpace α] [LinearOrder α] [OrderTop α] [OrderTopology α]
    [Nontrivial α] [DenselyOrdered α] : (𝓝 ⊤).HasBasis (fun a : α => a < ⊤) Ici :=
  nhds_top_basis.to_hasBasis
    (fun _a ha => let ⟨b, hab, hb⟩ := exists_between ha; ⟨b, hb, Ici_subset_Ioi.mpr hab⟩)
    fun a ha => ⟨a, ha, Ioi_subset_Ici_self⟩

theorem nhds_bot_basis_Iic [TopologicalSpace α] [LinearOrder α] [OrderBot α] [OrderTopology α]
    [Nontrivial α] [DenselyOrdered α] : (𝓝 ⊥).HasBasis (fun a : α => ⊥ < a) Iic :=
  nhds_top_basis_Ici (α := αᵒᵈ)

theorem tendsto_nhds_top_mono [TopologicalSpace β] [Preorder β] [OrderTop β] [OrderTopology β]
    {l : Filter α} {f g : α → β} (hf : Tendsto f l (𝓝 ⊤)) (hg : f ≤ᶠ[l] g) : Tendsto g l (𝓝 ⊤) := by
  simp only [nhds_top_order, tendsto_iInf, tendsto_principal] at hf ⊢
  intro x hx
  filter_upwards [hf x hx, hg] with _ using lt_of_lt_of_le

theorem tendsto_nhds_bot_mono [TopologicalSpace β] [Preorder β] [OrderBot β] [OrderTopology β]
    {l : Filter α} {f g : α → β} (hf : Tendsto f l (𝓝 ⊥)) (hg : g ≤ᶠ[l] f) : Tendsto g l (𝓝 ⊥) :=
  tendsto_nhds_top_mono (β := βᵒᵈ) hf hg

theorem tendsto_nhds_top_mono' [TopologicalSpace β] [Preorder β] [OrderTop β] [OrderTopology β]
    {l : Filter α} {f g : α → β} (hf : Tendsto f l (𝓝 ⊤)) (hg : f ≤ g) : Tendsto g l (𝓝 ⊤) :=
  tendsto_nhds_top_mono hf (Eventually.of_forall hg)

theorem tendsto_nhds_bot_mono' [TopologicalSpace β] [Preorder β] [OrderBot β] [OrderTopology β]
    {l : Filter α} {f g : α → β} (hf : Tendsto f l (𝓝 ⊥)) (hg : g ≤ f) : Tendsto g l (𝓝 ⊥) :=
  tendsto_nhds_bot_mono hf (Eventually.of_forall hg)

section LinearOrder

variable [TopologicalSpace α] [LinearOrder α]

section OrderTopology

theorem order_separated [OrderTopology α] {a₁ a₂ : α} (h : a₁ < a₂) :
    ∃ u v : Set α, IsOpen u ∧ IsOpen v ∧ a₁ ∈ u ∧ a₂ ∈ v ∧ ∀ b₁ ∈ u, ∀ b₂ ∈ v, b₁ < b₂ :=
  let ⟨x, hx, y, hy, h⟩ := h.exists_disjoint_Iio_Ioi
  ⟨Iio x, Ioi y, isOpen_gt' _, isOpen_lt' _, hx, hy, h⟩

-- see Note [lower instance priority]
instance (priority := 100) OrderTopology.to_orderClosedTopology [OrderTopology α] :
    OrderClosedTopology α where
  isClosed_le' := isOpen_compl_iff.1 <| isOpen_prod_iff.mpr fun a₁ a₂ (h : ¬a₁ ≤ a₂) =>
    have h : a₂ < a₁ := lt_of_not_ge h
    let ⟨u, v, hu, hv, ha₁, ha₂, h⟩ := order_separated h
    ⟨v, u, hv, hu, ha₂, ha₁, fun ⟨b₁, b₂⟩ ⟨h₁, h₂⟩ => not_le_of_gt <| h b₂ h₂ b₁ h₁⟩

theorem exists_Ioc_subset_of_mem_nhds [OrderTopology α] {a : α} {s : Set α} (hs : s ∈ 𝓝 a)
    (h : ∃ l, l < a) : ∃ l < a, Ioc l a ⊆ s :=
  (nhdsLE_basis' h).mem_iff.mp (nhdsWithin_le_nhds hs)

theorem exists_Ioc_subset_of_mem_nhds' [OrderTopology α] {a : α} {s : Set α} (hs : s ∈ 𝓝 a) {l : α}
    (hl : l < a) : ∃ l' ∈ Ico l a, Ioc l' a ⊆ s :=
  let ⟨l', hl'a, hl's⟩ := exists_Ioc_subset_of_mem_nhds hs ⟨l, hl⟩
  ⟨max l l', ⟨le_max_left _ _, max_lt hl hl'a⟩,
    (Ioc_subset_Ioc_left <| le_max_right _ _).trans hl's⟩

theorem exists_Ico_subset_of_mem_nhds' [OrderTopology α] {a : α} {s : Set α} (hs : s ∈ 𝓝 a) {u : α}
    (hu : a < u) : ∃ u' ∈ Ioc a u, Ico a u' ⊆ s := by
  simpa only [OrderDual.exists, exists_prop, dual_Ico, dual_Ioc] using
    exists_Ioc_subset_of_mem_nhds' (show ofDual ⁻¹' s ∈ 𝓝 (toDual a) from hs) hu.dual

theorem exists_Ico_subset_of_mem_nhds [OrderTopology α] {a : α} {s : Set α} (hs : s ∈ 𝓝 a)
    (h : ∃ u, a < u) : ∃ u, a < u ∧ Ico a u ⊆ s :=
  let ⟨_l', hl'⟩ := h
  let ⟨l, hl⟩ := exists_Ico_subset_of_mem_nhds' hs hl'
  ⟨l, hl.1.1, hl.2⟩

theorem exists_Icc_mem_subset_of_mem_nhdsWithin_Ici [OrderTopology α] {a : α} {s : Set α}
    (hs : s ∈ 𝓝[≥] a) : ∃ b, a ≤ b ∧ Icc a b ∈ 𝓝[≥] a ∧ Icc a b ⊆ s := by
  rcases (em (IsMax a)).imp_right not_isMax_iff.mp with (ha | ha)
  · use a
    simpa [ha.Ici_eq] using hs
  · rcases (nhdsGE_basis' ha).mem_iff.mp hs with ⟨b, hab, hbs⟩
    rcases eq_empty_or_nonempty (Ioo a b) with (H | ⟨c, hac, hcb⟩)
    · have : Ico a b = Icc a a := by rw [← Icc_union_Ioo_eq_Ico le_rfl hab, H, union_empty]
      exact ⟨a, le_rfl, this ▸ ⟨Ico_mem_nhdsGE hab, hbs⟩⟩
    · refine ⟨c, hac.le, Icc_mem_nhdsGE hac, ?_⟩
      exact (Icc_subset_Ico_right hcb).trans hbs

theorem exists_Icc_mem_subset_of_mem_nhdsWithin_Iic [OrderTopology α] {a : α} {s : Set α}
    (hs : s ∈ 𝓝[≤] a) : ∃ b ≤ a, Icc b a ∈ 𝓝[≤] a ∧ Icc b a ⊆ s := by
  simpa only [dual_Icc, toDual.surjective.exists] using
    exists_Icc_mem_subset_of_mem_nhdsWithin_Ici (α := αᵒᵈ) (a := toDual a) hs

theorem exists_Icc_mem_subset_of_mem_nhds [OrderTopology α] {a : α} {s : Set α} (hs : s ∈ 𝓝 a) :
    ∃ b c, a ∈ Icc b c ∧ Icc b c ∈ 𝓝 a ∧ Icc b c ⊆ s := by
  rcases exists_Icc_mem_subset_of_mem_nhdsWithin_Iic (nhdsWithin_le_nhds hs) with
    ⟨b, hba, hb_nhds, hbs⟩
  rcases exists_Icc_mem_subset_of_mem_nhdsWithin_Ici (nhdsWithin_le_nhds hs) with
    ⟨c, hac, hc_nhds, hcs⟩
  refine ⟨b, c, ⟨hba, hac⟩, ?_⟩
  rw [← Icc_union_Icc_eq_Icc hba hac, ← nhdsLE_sup_nhdsGE]
  exact ⟨union_mem_sup hb_nhds hc_nhds, union_subset hbs hcs⟩

theorem IsOpen.exists_Ioo_subset [OrderTopology α] [Nontrivial α] {s : Set α} (hs : IsOpen s)
    (h : s.Nonempty) : ∃ a b, a < b ∧ Ioo a b ⊆ s := by
  obtain ⟨x, hx⟩ : ∃ x, x ∈ s := h
  obtain ⟨y, hy⟩ : ∃ y, y ≠ x := exists_ne x
  rcases lt_trichotomy x y with (H | rfl | H)
  · obtain ⟨u, xu, hu⟩ : ∃ u, x < u ∧ Ico x u ⊆ s :=
      exists_Ico_subset_of_mem_nhds (hs.mem_nhds hx) ⟨y, H⟩
    exact ⟨x, u, xu, Ioo_subset_Ico_self.trans hu⟩
  · exact (hy rfl).elim
  · obtain ⟨l, lx, hl⟩ : ∃ l, l < x ∧ Ioc l x ⊆ s :=
      exists_Ioc_subset_of_mem_nhds (hs.mem_nhds hx) ⟨y, H⟩
    exact ⟨l, x, lx, Ioo_subset_Ioc_self.trans hl⟩

theorem dense_of_exists_between [OrderTopology α] [Nontrivial α] {s : Set α}
    (h : ∀ ⦃a b⦄, a < b → ∃ c ∈ s, a < c ∧ c < b) : Dense s := by
  refine dense_iff_inter_open.2 fun U U_open U_nonempty => ?_
  obtain ⟨a, b, hab, H⟩ : ∃ a b : α, a < b ∧ Ioo a b ⊆ U := U_open.exists_Ioo_subset U_nonempty
  obtain ⟨x, xs, hx⟩ : ∃ x ∈ s, a < x ∧ x < b := h hab
  exact ⟨x, ⟨H hx, xs⟩⟩

/-- A set in a nontrivial densely linear ordered type is dense in the sense of topology if and only
if for any `a < b` there exists `c ∈ s`, `a < c < b`. Each implication requires less typeclass
assumptions. -/
theorem dense_iff_exists_between [OrderTopology α] [DenselyOrdered α] [Nontrivial α] {s : Set α} :
    Dense s ↔ ∀ a b, a < b → ∃ c ∈ s, a < c ∧ c < b :=
  ⟨fun h _ _ hab => h.exists_between hab, dense_of_exists_between⟩

/-- A set is a neighborhood of `a` if and only if it contains an interval `(l, u)` containing `a`,
provided `a` is neither a bottom element nor a top element. -/
theorem mem_nhds_iff_exists_Ioo_subset' [OrderTopology α] {a : α} {s : Set α} (hl : ∃ l, l < a)
    (hu : ∃ u, a < u) : s ∈ 𝓝 a ↔ ∃ l u, a ∈ Ioo l u ∧ Ioo l u ⊆ s := by
  constructor
  · intro h
    rcases exists_Ico_subset_of_mem_nhds h hu with ⟨u, au, hu⟩
    rcases exists_Ioc_subset_of_mem_nhds h hl with ⟨l, la, hl⟩
    exact ⟨l, u, ⟨la, au⟩, Ioc_union_Ico_eq_Ioo la au ▸ union_subset hl hu⟩
  · rintro ⟨l, u, ha, h⟩
    apply mem_of_superset (Ioo_mem_nhds ha.1 ha.2) h

/-- A set is a neighborhood of `a` if and only if it contains an interval `(l, u)` containing `a`.
-/
theorem mem_nhds_iff_exists_Ioo_subset [OrderTopology α] [NoMaxOrder α] [NoMinOrder α] {a : α}
    {s : Set α} : s ∈ 𝓝 a ↔ ∃ l u, a ∈ Ioo l u ∧ Ioo l u ⊆ s :=
  mem_nhds_iff_exists_Ioo_subset' (exists_lt a) (exists_gt a)

theorem nhds_basis_Ioo' [OrderTopology α] {a : α} (hl : ∃ l, l < a) (hu : ∃ u, a < u) :
    (𝓝 a).HasBasis (fun b : α × α => b.1 < a ∧ a < b.2) fun b => Ioo b.1 b.2 :=
  ⟨fun s => (mem_nhds_iff_exists_Ioo_subset' hl hu).trans <| by simp⟩

theorem nhds_basis_Ioo [OrderTopology α] [NoMaxOrder α] [NoMinOrder α] (a : α) :
    (𝓝 a).HasBasis (fun b : α × α => b.1 < a ∧ a < b.2) fun b => Ioo b.1 b.2 :=
  nhds_basis_Ioo' (exists_lt a) (exists_gt a)

theorem Filter.Eventually.exists_Ioo_subset [OrderTopology α] [NoMaxOrder α] [NoMinOrder α] {a : α}
    {p : α → Prop} (hp : ∀ᶠ x in 𝓝 a, p x) : ∃ l u, a ∈ Ioo l u ∧ Ioo l u ⊆ { x | p x } :=
  mem_nhds_iff_exists_Ioo_subset.1 hp

theorem Dense.topology_eq_generateFrom [OrderTopology α] [DenselyOrdered α] {s : Set α}
    (hs : Dense s) : ‹TopologicalSpace α› = .generateFrom (Ioi '' s ∪ Iio '' s) := by
  refine (OrderTopology.topology_eq_generate_intervals (α := α)).trans ?_
  refine le_antisymm (generateFrom_anti ?_) (le_generateFrom ?_)
  · simp only [union_subset_iff, image_subset_iff]
    exact ⟨fun a _ ↦ ⟨a, .inl rfl⟩, fun a _ ↦ ⟨a, .inr rfl⟩⟩
  · rintro _ ⟨a, rfl | rfl⟩
    · rw [hs.Ioi_eq_biUnion]
      let _ := generateFrom (Ioi '' s ∪ Iio '' s)
      exact isOpen_iUnion fun x ↦ isOpen_iUnion fun h ↦ .basic _ <| .inl <| mem_image_of_mem _ h.1
    · rw [hs.Iio_eq_biUnion]
      let _ := generateFrom (Ioi '' s ∪ Iio '' s)
      exact isOpen_iUnion fun x ↦ isOpen_iUnion fun h ↦ .basic _ <| .inr <| mem_image_of_mem _ h.1

@[deprecated OrderBot.atBot_eq (since := "2024-02-14")]
theorem atBot_le_nhds_bot [OrderBot α] : (atBot : Filter α) ≤ 𝓝 ⊥ := by
  rw [OrderBot.atBot_eq]
  apply pure_le_nhds

set_option linter.deprecated false in
@[deprecated OrderTop.atTop_eq (since := "2024-02-14")]
theorem atTop_le_nhds_top [OrderTop α] : (atTop : Filter α) ≤ 𝓝 ⊤ :=
  @atBot_le_nhds_bot αᵒᵈ _ _ _

variable (α)

/-- Let `α` be a densely ordered linear order with order topology. If `α` is a separable space, then
it has second countable topology. Note that the "densely ordered" assumption cannot be dropped, see
[double arrow space](https://topology.pi-base.org/spaces/S000093) for a counterexample. -/
theorem SecondCountableTopology.of_separableSpace_orderTopology [OrderTopology α] [DenselyOrdered α]
    [SeparableSpace α] : SecondCountableTopology α := by
  rcases exists_countable_dense α with ⟨s, hc, hd⟩
  refine ⟨⟨_, ?_, hd.topology_eq_generateFrom⟩⟩
  exact (hc.image _).union (hc.image _)

variable {α}

/-- The set of points which are isolated on the right is countable when the space is
second-countable. -/
theorem countable_setOf_covBy_right [OrderTopology α] [SecondCountableTopology α] :
    Set.Countable { x : α | ∃ y, x ⋖ y } := by
  nontriviality α
  let s := { x : α | ∃ y, x ⋖ y }
  have : ∀ x ∈ s, ∃ y, x ⋖ y := fun x => id
  choose! y hy using this
  have Hy : ∀ x z, x ∈ s → z < y x → z ≤ x := fun x z hx => (hy x hx).le_of_lt
  suffices H : ∀ a : Set α, IsOpen a → Set.Countable { x | x ∈ s ∧ x ∈ a ∧ y x ∉ a } by
    have : s ⊆ ⋃ a ∈ countableBasis α, { x | x ∈ s ∧ x ∈ a ∧ y x ∉ a } := fun x hx => by
      rcases (isBasis_countableBasis α).exists_mem_of_ne (hy x hx).ne with ⟨a, ab, xa, ya⟩
      exact mem_iUnion₂.2 ⟨a, ab, hx, xa, ya⟩
    refine Set.Countable.mono this ?_
    refine Countable.biUnion (countable_countableBasis α) fun a ha => H _ ?_
    exact isOpen_of_mem_countableBasis ha
  intro a ha
  suffices H : Set.Countable { x | (x ∈ s ∧ x ∈ a ∧ y x ∉ a) ∧ ¬IsBot x } from
    H.of_diff (subsingleton_isBot α).countable
  simp only [and_assoc]
  let t := { x | x ∈ s ∧ x ∈ a ∧ y x ∉ a ∧ ¬IsBot x }
  have : ∀ x ∈ t, ∃ z < x, Ioc z x ⊆ a := by
    intro x hx
    apply exists_Ioc_subset_of_mem_nhds (ha.mem_nhds hx.2.1)
    simpa only [IsBot, not_forall, not_le] using hx.right.right.right
  choose! z hz h'z using this
  have : PairwiseDisjoint t fun x => Ioc (z x) x := fun x xt x' x't hxx' => by
    rcases hxx'.lt_or_lt with (h' | h')
    · refine disjoint_left.2 fun u ux ux' => xt.2.2.1 ?_
      refine h'z x' x't ⟨ux'.1.trans_le (ux.2.trans (hy x xt.1).le), ?_⟩
      by_contra! H
      exact lt_irrefl _ ((Hy _ _ xt.1 H).trans_lt h')
    · refine disjoint_left.2 fun u ux ux' => x't.2.2.1 ?_
      refine h'z x xt ⟨ux.1.trans_le (ux'.2.trans (hy x' x't.1).le), ?_⟩
      by_contra! H
      exact lt_irrefl _ ((Hy _ _ x't.1 H).trans_lt h')
  refine this.countable_of_isOpen (fun x hx => ?_) fun x hx => ⟨x, hz x hx, le_rfl⟩
  suffices H : Ioc (z x) x = Ioo (z x) (y x) by
    rw [H]
    exact isOpen_Ioo
  exact Subset.antisymm (Ioc_subset_Ioo_right (hy x hx.1).lt) fun u hu => ⟨hu.1, Hy _ _ hx.1 hu.2⟩

/-- The set of points which are isolated on the left is countable when the space is
second-countable. -/
theorem countable_setOf_covBy_left [OrderTopology α] [SecondCountableTopology α] :
    Set.Countable { x : α | ∃ y, y ⋖ x } := by
  convert countable_setOf_covBy_right (α := αᵒᵈ) using 5
  exact toDual_covBy_toDual_iff.symm

/-- The set of points which are isolated on the left is countable when the space is
second-countable. -/
theorem countable_of_isolated_left' [OrderTopology α] [SecondCountableTopology α] :
    Set.Countable { x : α | ∃ y, y < x ∧ Ioo y x = ∅ } := by
  simpa only [← covBy_iff_Ioo_eq] using countable_setOf_covBy_left

/-- Consider a disjoint family of intervals `(x, y)` with `x < y` in a second-countable space.
Then the family is countable.
This is not a straightforward consequence of second-countability as some of these intervals might be
empty (but in fact this can happen only for countably many of them). -/
theorem Set.PairwiseDisjoint.countable_of_Ioo [OrderTopology α] [SecondCountableTopology α]
    {y : α → α} {s : Set α} (h : PairwiseDisjoint s fun x => Ioo x (y x))
    (h' : ∀ x ∈ s, x < y x) : s.Countable :=
  have : (s \ { x | ∃ y, x ⋖ y }).Countable :=
    (h.subset diff_subset).countable_of_isOpen (fun _ _ => isOpen_Ioo)
      fun x hx => (h' _ hx.1).exists_lt_lt (mt (Exists.intro (y x)) hx.2)
  this.of_diff countable_setOf_covBy_right

/-- For a function taking values in a second countable space, the set of points `x` for
which the image under `f` of `(x, ∞)` is separated above from `f x` is countable. -/
theorem countable_image_lt_image_Ioi [OrderTopology α] [LinearOrder β] (f : β → α)
    [SecondCountableTopology α] : Set.Countable {x | ∃ z, f x < z ∧ ∀ y, x < y → z ≤ f y} := by
  /- If the values of `f` are separated above on the right of `x`, there is an interval `(f x, z x)`
    which is not reached by `f`. This gives a family of disjoint open intervals in `α`. Such a
    family can only be countable as `α` is second-countable. -/
  nontriviality β
  have : Nonempty α := Nonempty.map f (by infer_instance)
  let s := {x | ∃ z, f x < z ∧ ∀ y, x < y → z ≤ f y}
  have : ∀ x, x ∈ s → ∃ z, f x < z ∧ ∀ y, x < y → z ≤ f y := fun x hx ↦ hx
  -- choose `z x` such that `f` does not take the values in `(f x, z x)`.
  choose! z hz using this
  have I : InjOn f s := by
    apply StrictMonoOn.injOn
    intro x hx y _ hxy
    calc
      f x < z x := (hz x hx).1
      _ ≤ f y := (hz x hx).2 y hxy
  -- show that `f s` is countable by arguing that a disjoint family of disjoint open intervals
  -- (the intervals `(f x, z x)`) is at most countable.
  have fs_count : (f '' s).Countable := by
    have A : (f '' s).PairwiseDisjoint fun x => Ioo x (z (invFunOn f s x)) := by
      rintro _ ⟨u, us, rfl⟩ _ ⟨v, vs, rfl⟩ huv
      wlog hle : u ≤ v generalizing u v
      · exact (this v vs u us huv.symm (le_of_not_le hle)).symm
      have hlt : u < v := hle.lt_of_ne (ne_of_apply_ne _ huv)
      apply disjoint_iff_forall_ne.2
      rintro a ha b hb rfl
      simp only [I.leftInvOn_invFunOn us, I.leftInvOn_invFunOn vs] at ha hb
      exact lt_irrefl _ ((ha.2.trans_le ((hz u us).2 v hlt)).trans hb.1)
    apply Set.PairwiseDisjoint.countable_of_Ioo A
    rintro _ ⟨y, ys, rfl⟩
    simpa only [I.leftInvOn_invFunOn ys] using (hz y ys).1
  exact MapsTo.countable_of_injOn (mapsTo_image f s) I fs_count

/-- For a function taking values in a second countable space, the set of points `x` for
which the image under `f` of `(x, ∞)` is separated below from `f x` is countable. -/
theorem countable_image_gt_image_Ioi [OrderTopology α] [LinearOrder β] (f : β → α)
    [SecondCountableTopology α] : Set.Countable {x | ∃ z, z < f x ∧ ∀ y, x < y → f y ≤ z} :=
  countable_image_lt_image_Ioi (α := αᵒᵈ) f

/-- For a function taking values in a second countable space, the set of points `x` for
which the image under `f` of `(-∞, x)` is separated above from `f x` is countable. -/
theorem countable_image_lt_image_Iio [OrderTopology α] [LinearOrder β] (f : β → α)
    [SecondCountableTopology α] : Set.Countable {x | ∃ z, f x < z ∧ ∀ y, y < x → z ≤ f y} :=
  countable_image_lt_image_Ioi (β := βᵒᵈ) f

/-- For a function taking values in a second countable space, the set of points `x` for
which the image under `f` of `(-∞, x)` is separated below from `f x` is countable. -/
theorem countable_image_gt_image_Iio [OrderTopology α] [LinearOrder β] (f : β → α)
    [SecondCountableTopology α] : Set.Countable {x | ∃ z, z < f x ∧ ∀ y, y < x → f y ≤ z} :=
  countable_image_lt_image_Ioi (α := αᵒᵈ) (β := βᵒᵈ) f

instance instIsCountablyGenerated_atTop [OrderTopology α] [SecondCountableTopology α] :
    IsCountablyGenerated (atTop : Filter α) := by
  by_cases h : ∃ (x : α), IsTop x
  · rcases h with ⟨x, hx⟩
    rw [atTop_eq_pure_of_isTop hx]
    exact isCountablyGenerated_pure x
  · rcases exists_countable_basis α with ⟨b, b_count, b_ne, hb⟩
    have : Countable b := by exact Iff.mpr countable_coe_iff b_count
    have A : ∀ (s : b), ∃ (x : α), x ∈ (s : Set α) := by
      intro s
      have : (s : Set α) ≠ ∅ := by
        intro H
        apply b_ne
        convert s.2
        exact H.symm
      exact Iff.mp nmem_singleton_empty this
    choose a ha using A
    have : (atTop : Filter α) = (generate (Ici '' (range a))) := by
      apply atTop_eq_generate_of_not_bddAbove
      intro ⟨x, hx⟩
      simp only [IsTop, not_exists, not_forall, not_le] at h
      rcases h x with ⟨y, hy⟩
      obtain ⟨s, sb, -, hs⟩ : ∃ s, s ∈ b ∧ y ∈ s ∧ s ⊆ Ioi x :=
        hb.exists_subset_of_mem_open hy isOpen_Ioi
      have I : a ⟨s, sb⟩ ≤ x := hx (mem_range_self _)
      have J : x < a ⟨s, sb⟩ := hs (ha ⟨s, sb⟩)
      exact lt_irrefl _ (I.trans_lt J)
    rw [this]
    exact ⟨_, (countable_range _).image _, rfl⟩

instance instIsCountablyGenerated_atBot [OrderTopology α] [SecondCountableTopology α] :
    IsCountablyGenerated (atBot : Filter α) :=
  @instIsCountablyGenerated_atTop αᵒᵈ _ _ _ _

section Pi

/-!
### Intervals in `Π i, π i` belong to `𝓝 x`

For each lemma `pi_Ixx_mem_nhds` we add a non-dependent version `pi_Ixx_mem_nhds'` because
sometimes Lean fails to unify different instances while trying to apply the dependent version to,
e.g., `ι → ℝ`.
-/

variable [OrderTopology α] {ι : Type*} {π : ι → Type*} [Finite ι] [∀ i, LinearOrder (π i)]
  [∀ i, TopologicalSpace (π i)] [∀ i, OrderTopology (π i)] {a b x : ∀ i, π i} {a' b' x' : ι → α}

theorem pi_Iic_mem_nhds (ha : ∀ i, x i < a i) : Iic a ∈ 𝓝 x :=
  pi_univ_Iic a ▸ set_pi_mem_nhds (Set.toFinite _) fun _ _ => Iic_mem_nhds (ha _)

theorem pi_Iic_mem_nhds' (ha : ∀ i, x' i < a' i) : Iic a' ∈ 𝓝 x' :=
  pi_Iic_mem_nhds ha

theorem pi_Ici_mem_nhds (ha : ∀ i, a i < x i) : Ici a ∈ 𝓝 x :=
  pi_univ_Ici a ▸ set_pi_mem_nhds (Set.toFinite _) fun _ _ => Ici_mem_nhds (ha _)

theorem pi_Ici_mem_nhds' (ha : ∀ i, a' i < x' i) : Ici a' ∈ 𝓝 x' :=
  pi_Ici_mem_nhds ha

theorem pi_Icc_mem_nhds (ha : ∀ i, a i < x i) (hb : ∀ i, x i < b i) : Icc a b ∈ 𝓝 x :=
  pi_univ_Icc a b ▸ set_pi_mem_nhds finite_univ fun _ _ => Icc_mem_nhds (ha _) (hb _)

theorem pi_Icc_mem_nhds' (ha : ∀ i, a' i < x' i) (hb : ∀ i, x' i < b' i) : Icc a' b' ∈ 𝓝 x' :=
  pi_Icc_mem_nhds ha hb

variable [Nonempty ι]

theorem pi_Iio_mem_nhds (ha : ∀ i, x i < a i) : Iio a ∈ 𝓝 x := mem_of_superset
  (set_pi_mem_nhds finite_univ fun i _ ↦ Iio_mem_nhds (ha i)) (pi_univ_Iio_subset a)

theorem pi_Iio_mem_nhds' (ha : ∀ i, x' i < a' i) : Iio a' ∈ 𝓝 x' :=
  pi_Iio_mem_nhds ha

theorem pi_Ioi_mem_nhds (ha : ∀ i, a i < x i) : Ioi a ∈ 𝓝 x :=
  pi_Iio_mem_nhds (π := fun i => (π i)ᵒᵈ) ha

theorem pi_Ioi_mem_nhds' (ha : ∀ i, a' i < x' i) : Ioi a' ∈ 𝓝 x' :=
  pi_Ioi_mem_nhds ha

theorem pi_Ioc_mem_nhds (ha : ∀ i, a i < x i) (hb : ∀ i, x i < b i) : Ioc a b ∈ 𝓝 x := by
  refine mem_of_superset (set_pi_mem_nhds Set.finite_univ fun i _ => ?_) (pi_univ_Ioc_subset a b)
  exact Ioc_mem_nhds (ha i) (hb i)

theorem pi_Ioc_mem_nhds' (ha : ∀ i, a' i < x' i) (hb : ∀ i, x' i < b' i) : Ioc a' b' ∈ 𝓝 x' :=
  pi_Ioc_mem_nhds ha hb

theorem pi_Ico_mem_nhds (ha : ∀ i, a i < x i) (hb : ∀ i, x i < b i) : Ico a b ∈ 𝓝 x := by
  refine mem_of_superset (set_pi_mem_nhds Set.finite_univ fun i _ => ?_) (pi_univ_Ico_subset a b)
  exact Ico_mem_nhds (ha i) (hb i)

theorem pi_Ico_mem_nhds' (ha : ∀ i, a' i < x' i) (hb : ∀ i, x' i < b' i) : Ico a' b' ∈ 𝓝 x' :=
  pi_Ico_mem_nhds ha hb

theorem pi_Ioo_mem_nhds (ha : ∀ i, a i < x i) (hb : ∀ i, x i < b i) : Ioo a b ∈ 𝓝 x := by
  refine mem_of_superset (set_pi_mem_nhds Set.finite_univ fun i _ => ?_) (pi_univ_Ioo_subset a b)
  exact Ioo_mem_nhds (ha i) (hb i)

theorem pi_Ioo_mem_nhds' (ha : ∀ i, a' i < x' i) (hb : ∀ i, x' i < b' i) : Ioo a' b' ∈ 𝓝 x' :=
  pi_Ioo_mem_nhds ha hb

end Pi

end OrderTopology

end LinearOrder

end OrderTopology
