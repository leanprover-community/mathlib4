/-
Copyright (c) 2024 Vincent Beffara. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Beffara
-/
import Mathlib.Topology.Algebra.Order.Compact
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.Order.ProjIcc

/-!
# Continuous bundled maps on intervals

In this file we prove a few results about `ContinuousMap` when the domain is an interval.
-/

open Set ContinuousMap Filter Topology

namespace ContinuousMap

variable {α : Type*} [LinearOrder α] [TopologicalSpace α] [OrderTopology α] {a b c : α}
variable {E F : Type*} [TopologicalSpace E] [TopologicalSpace F]

/-- The embedding into an interval from a sub-interval lying on the left, as a `ContinuousMap`. -/
def subinterval_left (h : b ∈ Icc a c) : C(Icc a b, Icc a c) where
  toFun x := ⟨x, x.2.1, x.2.2.trans h.2⟩

/-- The embedding into an interval from a sub-interval lying on the right, as a `ContinuousMap`. -/
def subinterval_right (h : b ∈ Icc a c) : C(Icc b c, Icc a c) where
  toFun x := ⟨x, h.1.trans x.2.1, x.2.2⟩

/-- The value of a `ContinuousMap` defined on an interval at the left extremity of the interval. -/
def leftval (hab : a ≤ b) (f : C(Icc a b, E)) : E :=
  f ⟨a, le_rfl, hab⟩

/-- The value of a `ContinuousMap` defined on an interval at the right extremity of the interval. -/
def rightval (hbc : b ≤ c) (f : C(Icc b c, E)) : E :=
  f ⟨c, hbc, le_rfl⟩

/-- The map `leftval` as a `ContinuousMap`. -/
def leftvalCM (hab : a ≤ b) : C(C(Icc a b, E), E) :=
  ⟨leftval hab, continuous_eval_const _⟩

/-- The map `rightval` as a `ContinuousMap`. -/
def rightvalCM (hbc : b ≤ c) : C(C(Icc b c, E), E) :=
  ⟨rightval hbc, continuous_eval_const _⟩

omit [OrderTopology α] in
@[simp]
theorem firstval_comp {hab : a ≤ b} {γ : C(Icc a b, E)} {f : C(E, F)} :
    leftval hab (f.comp γ) = f (leftval hab γ) :=
  rfl

omit [OrderTopology α] in
@[simp]
theorem lastval_comp {hab : a ≤ b} {γ : C(Icc a b, E)} {f : C(E, F)} :
    rightval hab (f.comp γ) = f (rightval hab γ) :=
  rfl

/-- The map `projIcc` from `α` onto an interval in `α`, as a `ContinuousMap`. -/
def projIccCM (hab : a ≤ b) : C(α, Icc a b) :=
  ⟨projIcc a b hab, continuous_projIcc⟩

/-- The extension operation from continuous maps on an interval to continuous maps on the whole
  type, as a `ContinuousMap`. -/
def IccExtendCM (hab : a ≤ b) : C(C(Icc a b, E), C(α, E)) where
  toFun f := f.comp (projIccCM hab)
  continuous_toFun := continuous_comp_left _

@[simp]
theorem IccExtendCM_of_mem {hab : a ≤ b} {f : C(Icc a b, E)} {x : α} (hx : x ∈ Icc a b) :
    IccExtendCM hab f x = f ⟨x, hx⟩ := by
  simp [IccExtendCM, projIccCM, projIcc, hx.1, hx.2]

/-- The concatenation of two continuous maps defined on adjacent intervals. If the values of the
  functions on the common bound do not agree, this is defined as an arbitrarily chosen constant
  map. See `transCM` for the corresponding map on the subtype of compatible function pairs. -/
noncomputable def trans (h : b ∈ Icc a c) (f : C(Icc a b, E)) (g : C(Icc b c, E)) :
    C(Icc a c, E) := by
  by_cases hb : rightval h.1 f = leftval h.2 g
  · let h (t : α) : E := if t ≤ b then IccExtendCM h.1 f t else IccExtendCM h.2 g t
    suffices Continuous h from ⟨fun t => h t, by fun_prop⟩
    apply Continuous.if_le (by fun_prop) (by fun_prop) continuous_id continuous_const
    rintro x rfl
    simpa [IccExtendCM, projIccCM]
  · exact .const _ (leftval h.1 f) -- junk value

variable {f : C(Icc a b, E)} {g : C(Icc b c, E)}

theorem trans_comp_left (h : b ∈ Icc a c) (hb : rightval h.1 f = leftval h.2 g) :
    f = (trans h f g).comp (subinterval_left h) := by
  ext x
  simp [trans, IccExtendCM, hb, subinterval_left, projIccCM, x.2.2]

theorem trans_comp_right (h : b ∈ Icc a c) (hb : rightval h.1 f = leftval h.2 g) :
    g = (trans h f g).comp (subinterval_right h) := by
  ext ⟨x, hx⟩
  by_cases hxb : x = b
  · subst x
    symm at hb
    simpa [trans, subinterval_right, IccExtendCM, projIccCM, hb]
  · have : ¬ x ≤ b := lt_of_le_of_ne hx.1 (Ne.symm hxb) |>.not_le
    simp [trans, hb, subinterval_right, this, IccExtendCM, projIccCM, projIcc, hx.2, hx.1]

@[simp]
theorem trans_left (h : b ∈ Icc a c) (hb : rightval h.1 f = leftval h.2 g)
    {t : Icc a c} (ht : t ≤ b) : trans h f g t = f ⟨t, t.2.1, ht⟩ := by
  nth_rewrite 2 [trans_comp_left h hb]
  rfl

@[simp]
theorem trans_right (h : b ∈ Icc a c) (hb : rightval h.1 f = leftval h.2 g)
    {t : Icc a c} (ht : b ≤ t) : trans h f g t = g ⟨t, ht, t.2.2⟩ := by
  nth_rewrite 2 [trans_comp_right h hb]
  rfl

variable {ι : Type*} {p : Filter ι} {F : ι → C(Icc a b, E)} {G : ι → C(Icc b c, E)}

theorem tendsto_trans (h : b ∈ Icc a c) (hfg : ∀ᶠ i in p, rightval h.1 (F i) = leftval h.2 (G i))
    (hfg' : rightval h.1 f = leftval h.2 g) (hf : Tendsto F p (𝓝 f)) (hg : Tendsto G p (𝓝 g)) :
    Tendsto (fun i => trans h (F i) (G i)) p (𝓝 (trans h f g)) := by
  rw [tendsto_nhds_compactOpen] at hf hg ⊢
  rintro K hK U hU hfgU
  let K₁ : Set (Icc a b) := projIccCM h.1 '' (Subtype.val '' (K ∩ Iic ⟨b, h⟩))
  let K₂ : Set (Icc b c) := projIccCM h.2 '' (Subtype.val '' (K ∩ Ici ⟨b, h⟩))
  have hK₁ : IsCompact K₁ :=
    hK.inter_right isClosed_Iic |>.image continuous_subtype_val |>.image (projIccCM h.1).continuous
  have hK₂ : IsCompact K₂ :=
    hK.inter_right isClosed_Ici |>.image continuous_subtype_val |>.image (projIccCM h.2).continuous
  have hfU : MapsTo f K₁ U := by
    rw [trans_comp_left h hfg']
    apply hfgU.comp
    rintro x ⟨y, ⟨⟨z, hz⟩, ⟨h1, (h2 : z ≤ b)⟩, rfl⟩, rfl⟩
    simpa [projIccCM, projIcc, h2, hz.1] using h1
  have hgU : MapsTo g K₂ U := by
    rw [trans_comp_right h hfg']
    apply hfgU.comp
    rintro x ⟨y, ⟨⟨z, hz⟩, ⟨h1, (h2 : b ≤ z)⟩, rfl⟩, rfl⟩
    simpa [projIccCM, projIcc, h2, hz.2] using h1
  filter_upwards [hf K₁ hK₁ U hU hfU, hg K₂ hK₂ U hU hgU, hfg] with i hf hg hfg x hx
  by_cases hxb : x ≤ b
  · rw [trans_left h hfg hxb]
    refine hf ⟨x, ⟨x, ⟨hx, hxb⟩, rfl⟩, ?_⟩
    simp [projIccCM, projIcc, hxb, x.2.1]
  · replace hxb : b ≤ x := lt_of_not_le hxb |>.le
    rw [trans_right h hfg hxb]
    refine hg ⟨x, ⟨x, ⟨hx, hxb⟩, rfl⟩, ?_⟩
    simp [projIccCM, projIcc, hxb, x.2.2]

/-- The concatenation of compatible pairs of continuous maps on adjacent intrevals, defined as a
  `ContinuousMap` on a subtype of the product. -/
noncomputable def transCM (h : b ∈ Icc a c) :
    C({fg : C(Icc a b, E) × C(Icc b c, E) // rightval h.1 fg.1 = leftval h.2 fg.2}, C(Icc a c, E))
    where
  toFun fg := trans h fg.val.1 fg.val.2
  continuous_toFun := by
    let Φ : C(Icc a b, E) × C(Icc b c, E) → C(Icc a c, E) := (trans h).uncurry
    let S : Set (C(Icc a b, E) × C(Icc b c, E)) := {fg | rightval h.1 fg.1 = leftval h.2 fg.2}
    change Continuous (S.restrict Φ)
    refine continuousOn_iff_continuous_restrict.mp (fun fg hfg => ?_)
    refine tendsto_trans h ?_ hfg ?_ ?_
    · exact eventually_nhdsWithin_of_forall (fun _ => id)
    · exact tendsto_nhdsWithin_of_tendsto_nhds continuousAt_fst
    · exact tendsto_nhdsWithin_of_tendsto_nhds continuousAt_snd

@[simp]
theorem transCM_left {h : b ∈ Icc a c} {x : Icc a c} (hx : x ≤ b)
    {fg : {fg : C(Icc a b, E) × C(Icc b c, E) // rightval h.1 fg.1 = leftval h.2 fg.2}} :
    transCM h fg x = fg.1.1 ⟨x.1, x.2.1, hx⟩ :=
  trans_left h fg.2 hx

@[simp]
theorem transCM_right {h : b ∈ Icc a c} {x : Icc a c} (hx : b ≤ x)
    {fg : {fg : C(Icc a b, E) × C(Icc b c, E) // rightval h.1 fg.1 = leftval h.2 fg.2}} :
    transCM h fg x = fg.1.2 ⟨x.1, hx, x.2.2⟩ :=
  trans_right h fg.2 hx

end ContinuousMap
