/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Topology.Order.Basic
public import Mathlib.Order.SuccPred.Limit
import Mathlib.Topology.Order.IsLUB

/-!
# `Filter.atTop` and `Filter.atBot` for intervals in a linear order topology

Let `X` be a linear order with order topology.
Let `a` be a point that is either the bottom element of `X` or is not isolated on the left,
see `Order.IsSuccPrelimit`.
Then the `Filter.atTop` filter on `Set.Iio a` and `𝓝[<] a` are related by the coercion map
via pushforward and pullback, see `map_coe_Iio_atTop` and `comap_coe_Iio_nhdsLT`.

We prove several versions of this statement for `Set.Iio`, `Set.Ioi`, and `Set.Ioo`,
as well as `Filter.atTop` and `Filter.atBot`.

The assumption on `a` is automatically satisfied for densely ordered types,
see `Order.IsSuccPrelimit.of_dense`.
-/

public section

open Set Filter Order OrderDual
open scoped Topology

variable {X : Type*} [LinearOrder X] [TopologicalSpace X] [OrderTopology X]
  {s : Set X} {a b : X}

theorem comap_coe_nhdsLT_eq_atTop_iff :
    comap ((↑) : s → X) (𝓝[<] b) = atTop ↔
      s ⊆ Iio b ∧ (s.Nonempty → ∀ a < b, (s ∩ Ioo a b).Nonempty) := by
  rcases s.eq_empty_or_nonempty with rfl | hsne
  · simp [eq_iff_true_of_subsingleton]
  have := hsne.to_subtype
  simp only [hsne, true_imp_iff]
  by_cases hsub : s ⊆ Iio b
  · simp only [hsub, true_and]
    constructor
    · intro h a ha
      have := preimage_mem_comap (m := ((↑) : s → X)) (Ioo_mem_nhdsLT ha)
      rw [h] at this
      rcases Filter.nonempty_of_mem this with ⟨⟨c, hcs⟩, hc⟩
      exact ⟨c, hcs, hc⟩
    · intro h
      refine (nhdsLT_basis_of_exists_lt (hsne.mono hsub)).comap _ |>.ext atTop_basis ?_ ?_
      · intro a hab
        rcases h a hab with ⟨c, hcs, hc⟩
        use ⟨c, hcs⟩
        simp_all [subset_def, hc.1.trans_le]
      · rintro ⟨a, has⟩ -
        use a, hsub has
        simp_all [subset_def, le_of_lt]
  · suffices ¬Tendsto (↑) (atTop : Filter s) (𝓝[<] b) by
      contrapose this
      simp_all [tendsto_iff_comap]
    intro h
    rcases not_subset_iff_exists_mem_notMem.mp hsub with ⟨a, has, ha⟩
    rcases h.eventually eventually_mem_nhdsWithin |>.and (eventually_ge_atTop ⟨a, has⟩) |>.exists
      with ⟨⟨c, hcs⟩, hcb, hac⟩
    apply lt_irrefl a
    calc
      a ≤ c := by simpa using hac
      _ < b := by simpa using hcb
      _ ≤ a := by simpa using ha

theorem comap_coe_nhdsGT_eq_atBot_iff :
    comap ((↑) : s → X) (𝓝[>] b) = atBot ↔
      s ⊆ Ioi b ∧ (s.Nonempty → ∀ a > b, (s ∩ Ioo b a).Nonempty) := by
  refine comap_coe_nhdsLT_eq_atTop_iff (s := OrderDual.ofDual ⁻¹' s) (b := OrderDual.toDual b)
    |>.trans <| .and .rfl <| forall₃_congr fun hne a ha ↦ ?_
  rw [← a.toDual_ofDual, Ioo_toDual]
  rfl

theorem comap_coe_nhdsLT_of_Ioo_subset (hsb : s ⊆ Iio b) (hs : s.Nonempty → ∃ a < b, Ioo a b ⊆ s)
    (hb : IsSuccPrelimit b := by exact .of_dense _) :
    comap ((↑) : s → X) (𝓝[<] b) = atTop := by
  rw [comap_coe_nhdsLT_eq_atTop_iff]
  refine ⟨hsb, fun hsne a ha ↦ ?_⟩
  rcases hs hsne with ⟨c, hcb, hcs⟩
  rcases hb.lt_iff_exists_lt.mp (max_lt ha hcb) with ⟨x, hxb, hacx⟩
  rw [max_lt_iff] at hacx
  exact ⟨x, hcs ⟨hacx.2, hxb⟩, hacx.1, hxb⟩

theorem comap_coe_nhdsGT_of_Ioo_subset (hsa : s ⊆ Ioi a) (hs : s.Nonempty → ∃ b > a, Ioo a b ⊆ s)
    (ha : IsPredPrelimit a := by exact .of_dense _) :
    comap ((↑) : s → X) (𝓝[>] a) = atBot := by
  refine comap_coe_nhdsLT_of_Ioo_subset (show ofDual ⁻¹' s ⊆ Iio (toDual a) from hsa) ?_ ha.dual
  simpa only [OrderDual.exists, Ioo_toDual]

theorem map_coe_atTop_of_Ioo_subset (hsb : s ⊆ Iio b) (hs : ∀ a' < b, ∃ a < b, Ioo a b ⊆ s)
    (hb : IsSuccPrelimit b := by exact .of_dense _) :
    map ((↑) : s → X) atTop = 𝓝[<] b := by
  rcases eq_empty_or_nonempty (Iio b) with (hb' | ⟨a, ha⟩)
  · have : IsEmpty s := ⟨fun x => hb'.subset (hsb x.2)⟩
    rw [filter_eq_bot_of_isEmpty atTop, Filter.map_bot, hb', nhdsWithin_empty]
  · rw [← comap_coe_nhdsLT_of_Ioo_subset hsb (fun _ => hs a ha) hb, map_comap_of_mem]
    rw [Subtype.range_val]
    exact (mem_nhdsLT_iff_exists_Ioo_subset' ha).2 (hs a ha)

theorem map_coe_atBot_of_Ioo_subset (hsa : s ⊆ Ioi a) (hs : ∀ b' > a, ∃ b > a, Ioo a b ⊆ s)
    (ha : IsPredPrelimit a := by exact .of_dense _) :
    map ((↑) : s → X) atBot = 𝓝[>] a := by
  refine map_coe_atTop_of_Ioo_subset (s := ofDual ⁻¹' s) (b := toDual a) hsa ?_ ha.dual
  intro b' hb'
  simpa [OrderDual.exists] using hs (ofDual b') hb'

/-- The `atTop` filter for an open interval `Ioo a b` comes from the left-neighbourhoods filter at
the right endpoint in the ambient order. -/
@[simp]
theorem comap_coe_Ioo_nhdsLT (a b : X) (hb : IsSuccPrelimit b := by exact .of_dense _) :
    comap ((↑) : Ioo a b → X) (𝓝[<] b) = atTop :=
  comap_coe_nhdsLT_of_Ioo_subset Ioo_subset_Iio_self
    (fun h => ⟨a, h.elim fun _x hx ↦ hx.1.trans hx.2, Subset.rfl⟩) hb

/-- The `atBot` filter for an open interval `Ioo a b` comes from the right-neighbourhoods filter at
the left endpoint in the ambient order. -/
@[simp]
theorem comap_coe_Ioo_nhdsGT (a b : X) (ha : IsPredPrelimit a := by exact .of_dense _) :
    comap ((↑) : Ioo a b → X) (𝓝[>] a) = atBot :=
  comap_coe_nhdsGT_of_Ioo_subset Ioo_subset_Ioi_self
    (fun h => ⟨b, h.elim fun _x hx ↦ hx.1.trans hx.2, Subset.rfl⟩) ha

@[simp]
theorem comap_coe_Ioi_nhdsGT (a : X) (ha : IsPredPrelimit a := by exact .of_dense _) :
    comap ((↑) : Ioi a → X) (𝓝[>] a) = atBot :=
  comap_coe_nhdsGT_of_Ioo_subset Subset.rfl (fun ⟨x, hx⟩ => ⟨x, hx, Ioo_subset_Ioi_self⟩) ha

@[simp]
theorem comap_coe_Iio_nhdsLT (a : X) (ha : IsSuccPrelimit a := by exact .of_dense _) :
    comap ((↑) : Iio a → X) (𝓝[<] a) = atTop :=
  comap_coe_Ioi_nhdsGT (toDual a) ha.dual

@[simp]
theorem map_coe_Ioo_atTop (h : a < b) (hb : IsSuccPrelimit b := by exact .of_dense _) :
    map ((↑) : Ioo a b → X) atTop = 𝓝[<] b :=
  map_coe_atTop_of_Ioo_subset Ioo_subset_Iio_self (fun _ _ => ⟨_, h, Subset.rfl⟩) hb

@[simp]
theorem map_coe_Ioo_atBot (h : a < b) (ha : IsPredPrelimit a := by exact .of_dense _) :
    map ((↑) : Ioo a b → X) atBot = 𝓝[>] a :=
  map_coe_atBot_of_Ioo_subset Ioo_subset_Ioi_self (fun _ _ => ⟨_, h, Subset.rfl⟩) ha

@[simp]
theorem map_coe_Ioi_atBot (a : X) (ha : IsPredPrelimit a := by exact .of_dense _) :
    map ((↑) : Ioi a → X) atBot = 𝓝[>] a :=
  map_coe_atBot_of_Ioo_subset Subset.rfl (fun b hb => ⟨b, hb, Ioo_subset_Ioi_self⟩) ha

@[simp]
theorem map_coe_Iio_atTop (a : X) (ha : IsSuccPrelimit a := by exact .of_dense _) :
    map ((↑) : Iio a → X) atTop = 𝓝[<] a :=
  map_coe_Ioi_atBot (toDual a) ha.dual

variable {α : Type*} {l : Filter α} {f : X → α}

@[simp]
theorem tendsto_comp_coe_Ioo_atTop (h : a < b) (hb : IsSuccPrelimit b := by exact .of_dense _) :
    Tendsto (fun x : Ioo a b => f x) atTop l ↔ Tendsto f (𝓝[<] b) l := by
  rw [← map_coe_Ioo_atTop h hb, tendsto_map'_iff, Function.comp_def]

@[simp]
theorem tendsto_comp_coe_Ioo_atBot (h : a < b) (ha : IsPredPrelimit a := by exact .of_dense _) :
    Tendsto (fun x : Ioo a b => f x) atBot l ↔ Tendsto f (𝓝[>] a) l := by
  rw [← map_coe_Ioo_atBot h ha, tendsto_map'_iff, Function.comp_def]

@[simp]
theorem tendsto_comp_coe_Ioi_atBot (ha : IsPredPrelimit a := by exact .of_dense _) :
    Tendsto (fun x : Ioi a => f x) atBot l ↔ Tendsto f (𝓝[>] a) l := by
  rw [← map_coe_Ioi_atBot a ha, tendsto_map'_iff, Function.comp_def]

@[simp]
theorem tendsto_comp_coe_Iio_atTop (ha : IsSuccPrelimit a := by exact .of_dense _) :
    Tendsto (fun x : Iio a => f x) atTop l ↔ Tendsto f (𝓝[<] a) l := by
  rw [← map_coe_Iio_atTop a ha, tendsto_map'_iff, Function.comp_def]

@[simp]
theorem tendsto_Ioo_atTop {f : α → Ioo a b} (hb : IsSuccPrelimit b := by exact .of_dense _) :
    Tendsto f l atTop ↔ Tendsto (fun x => (f x : X)) l (𝓝[<] b) := by
  rw [← comap_coe_Ioo_nhdsLT a b hb, tendsto_comap_iff, Function.comp_def]

@[simp]
theorem tendsto_Ioo_atBot {f : α → Ioo a b} (ha : IsPredPrelimit a := by exact .of_dense _) :
    Tendsto f l atBot ↔ Tendsto (fun x => (f x : X)) l (𝓝[>] a) := by
  rw [← comap_coe_Ioo_nhdsGT a b ha, tendsto_comap_iff, Function.comp_def]

@[simp]
theorem tendsto_Ioi_atBot {f : α → Ioi a} (ha : IsPredPrelimit a := by exact .of_dense _) :
    Tendsto f l atBot ↔ Tendsto (fun x => (f x : X)) l (𝓝[>] a) := by
  rw [← comap_coe_Ioi_nhdsGT a ha, tendsto_comap_iff, Function.comp_def]

@[simp]
theorem tendsto_Iio_atTop {f : α → Iio a} (ha : IsSuccPrelimit a := by exact .of_dense _) :
    Tendsto f l atTop ↔ Tendsto (fun x => (f x : X)) l (𝓝[<] a) := by
  rw [← comap_coe_Iio_nhdsLT a ha, tendsto_comap_iff, Function.comp_def]
