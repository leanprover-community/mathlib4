/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Heather Macbeth
-/
module

public import Mathlib.Topology.Homeomorph.Defs
public import Mathlib.Topology.Order.LeftRightNhds

/-!
# Continuity of monotone functions

In this file we prove the following fact: if `f` is a monotone function on a neighborhood of `a`
and the image of this neighborhood is a neighborhood of `f a`, then `f` is continuous at `a`, see
`continuousWithinAt_of_monotoneOn_of_image_mem_nhds`, as well as several similar facts.

We also prove that an `OrderIso` is continuous.

## Tags

continuous, monotone
-/

public section


open Set Filter

open Topology

section LinearOrder

variable {α β : Type*} [LinearOrder α] [TopologicalSpace α] [OrderTopology α]
variable [LinearOrder β] [TopologicalSpace β] [OrderTopology β]

/-- If `f` is a function strictly monotone on a right neighborhood of `a` and the
image of this neighborhood under `f` meets every interval `(f a, b]`, `b > f a`, then `f` is
continuous at `a` from the right.

The assumption `hfs : ∀ b > f a, ∃ c ∈ s, f c ∈ Ioc (f a) b` is required because otherwise the
function `f : ℝ → ℝ` given by `f x = if x ≤ 0 then x else x + 1` would be a counter-example at
`a = 0`. -/
theorem StrictMonoOn.continuousWithinAt_right_of_exists_between {f : α → β} {s : Set α} {a : α}
    (h_mono : StrictMonoOn f s) (hs : s ∈ 𝓝[≥] a) (hfs : ∀ b > f a, ∃ c ∈ s, f c ∈ Ioc (f a) b) :
    ContinuousWithinAt f (Ici a) a := by
  have has : a ∈ s := mem_of_mem_nhdsWithin self_mem_Ici hs
  refine tendsto_order.2 ⟨fun b hb => ?_, fun b hb => ?_⟩
  · filter_upwards [hs, @self_mem_nhdsWithin _ _ a (Ici a)] with _ hxs hxa using hb.trans_le
      ((h_mono.le_iff_le has hxs).2 hxa)
  · rcases hfs b hb with ⟨c, hcs, hac, hcb⟩
    rw [h_mono.lt_iff_lt has hcs] at hac
    filter_upwards [hs, Ico_mem_nhdsGE hac]
    rintro x hx ⟨_, hxc⟩
    exact ((h_mono.lt_iff_lt hx hcs).2 hxc).trans_le hcb

/-- If `f` is a monotone function on a right neighborhood of `a` and the image of this neighborhood
under `f` meets every interval `(f a, b)`, `b > f a`, then `f` is continuous at `a` from the right.

The assumption `hfs : ∀ b > f a, ∃ c ∈ s, f c ∈ Ioo (f a) b` cannot be replaced by the weaker
assumption `hfs : ∀ b > f a, ∃ c ∈ s, f c ∈ Ioc (f a) b` we use for strictly monotone functions
because otherwise the function `ceil : ℝ → ℤ` would be a counter-example at `a = 0`. -/
theorem continuousWithinAt_right_of_monotoneOn_of_exists_between {f : α → β} {s : Set α} {a : α}
    (h_mono : MonotoneOn f s) (hs : s ∈ 𝓝[≥] a) (hfs : ∀ b > f a, ∃ c ∈ s, f c ∈ Ioo (f a) b) :
    ContinuousWithinAt f (Ici a) a := by
  have has : a ∈ s := mem_of_mem_nhdsWithin self_mem_Ici hs
  refine tendsto_order.2 ⟨fun b hb => ?_, fun b hb => ?_⟩
  · filter_upwards [hs, @self_mem_nhdsWithin _ _ a (Ici a)] with _ hxs hxa using hb.trans_le
      (h_mono has hxs hxa)
  · rcases hfs b hb with ⟨c, hcs, hac, hcb⟩
    have : a < c := not_le.1 fun h => hac.not_ge <| h_mono hcs has h
    filter_upwards [hs, Ico_mem_nhdsGE this]
    rintro x hx ⟨_, hxc⟩
    exact (h_mono hx hcs hxc.le).trans_lt hcb

/-- If a function `f` with a densely ordered codomain is monotone on a right neighborhood of `a` and
the closure of the image of this neighborhood under `f` is a right neighborhood of `f a`, then `f`
is continuous at `a` from the right. -/
theorem continuousWithinAt_right_of_monotoneOn_of_closure_image_mem_nhdsWithin [DenselyOrdered β]
    {f : α → β} {s : Set α} {a : α} (h_mono : MonotoneOn f s) (hs : s ∈ 𝓝[≥] a)
    (hfs : closure (f '' s) ∈ 𝓝[≥] f a) : ContinuousWithinAt f (Ici a) a := by
  refine continuousWithinAt_right_of_monotoneOn_of_exists_between h_mono hs fun b hb => ?_
  rcases (mem_nhdsGE_iff_exists_mem_Ioc_Ico_subset hb).1 hfs with ⟨b', ⟨hab', hbb'⟩, hb'⟩
  rcases exists_between hab' with ⟨c', hc'⟩
  rcases mem_closure_iff.1 (hb' ⟨hc'.1.le, hc'.2⟩) (Ioo (f a) b') isOpen_Ioo hc' with
    ⟨_, hc, ⟨c, hcs, rfl⟩⟩
  exact ⟨c, hcs, hc.1, hc.2.trans_le hbb'⟩

/-- If a function `f` with a densely ordered codomain is monotone on a right neighborhood of `a` and
the image of this neighborhood under `f` is a right neighborhood of `f a`, then `f` is continuous at
`a` from the right. -/
theorem continuousWithinAt_right_of_monotoneOn_of_image_mem_nhdsWithin [DenselyOrdered β]
    {f : α → β} {s : Set α} {a : α} (h_mono : MonotoneOn f s) (hs : s ∈ 𝓝[≥] a)
    (hfs : f '' s ∈ 𝓝[≥] f a) : ContinuousWithinAt f (Ici a) a :=
  continuousWithinAt_right_of_monotoneOn_of_closure_image_mem_nhdsWithin h_mono hs <|
    mem_of_superset hfs subset_closure

/-- If a function `f` with a densely ordered codomain is strictly monotone on a right neighborhood
of `a` and the closure of the image of this neighborhood under `f` is a right neighborhood of `f a`,
then `f` is continuous at `a` from the right. -/
theorem StrictMonoOn.continuousWithinAt_right_of_closure_image_mem_nhdsWithin [DenselyOrdered β]
    {f : α → β} {s : Set α} {a : α} (h_mono : StrictMonoOn f s) (hs : s ∈ 𝓝[≥] a)
    (hfs : closure (f '' s) ∈ 𝓝[≥] f a) : ContinuousWithinAt f (Ici a) a :=
  continuousWithinAt_right_of_monotoneOn_of_closure_image_mem_nhdsWithin
    (fun _ hx _ hy => (h_mono.le_iff_le hx hy).2) hs hfs

/-- If a function `f` with a densely ordered codomain is strictly monotone on a right neighborhood
of `a` and the image of this neighborhood under `f` is a right neighborhood of `f a`, then `f` is
continuous at `a` from the right. -/
theorem StrictMonoOn.continuousWithinAt_right_of_image_mem_nhdsWithin [DenselyOrdered β] {f : α → β}
    {s : Set α} {a : α} (h_mono : StrictMonoOn f s) (hs : s ∈ 𝓝[≥] a) (hfs : f '' s ∈ 𝓝[≥] f a) :
    ContinuousWithinAt f (Ici a) a :=
  h_mono.continuousWithinAt_right_of_closure_image_mem_nhdsWithin hs
    (mem_of_superset hfs subset_closure)

/-- If a function `f` is strictly monotone on a right neighborhood of `a` and the image of this
neighborhood under `f` includes `Ioi (f a)`, then `f` is continuous at `a` from the right. -/
theorem StrictMonoOn.continuousWithinAt_right_of_surjOn {f : α → β} {s : Set α} {a : α}
    (h_mono : StrictMonoOn f s) (hs : s ∈ 𝓝[≥] a) (hfs : SurjOn f s (Ioi (f a))) :
    ContinuousWithinAt f (Ici a) a :=
  h_mono.continuousWithinAt_right_of_exists_between hs fun _ hb =>
    let ⟨c, hcs, hcb⟩ := hfs hb
    ⟨c, hcs, hcb.symm ▸ hb, hcb.le⟩

/-- If `f` is a strictly monotone function on a left neighborhood of `a` and the image of this
neighborhood under `f` meets every interval `[b, f a)`, `b < f a`, then `f` is continuous at `a`
from the left.

The assumption `hfs : ∀ b < f a, ∃ c ∈ s, f c ∈ Ico b (f a)` is required because otherwise the
function `f : ℝ → ℝ` given by `f x = if x < 0 then x else x + 1` would be a counter-example at
`a = 0`. -/
theorem StrictMonoOn.continuousWithinAt_left_of_exists_between {f : α → β} {s : Set α} {a : α}
    (h_mono : StrictMonoOn f s) (hs : s ∈ 𝓝[≤] a) (hfs : ∀ b < f a, ∃ c ∈ s, f c ∈ Ico b (f a)) :
    ContinuousWithinAt f (Iic a) a :=
  h_mono.dual.continuousWithinAt_right_of_exists_between hs fun b hb =>
    let ⟨c, hcs, hcb, hca⟩ := hfs b hb
    ⟨c, hcs, hca, hcb⟩

/-- If `f` is a monotone function on a left neighborhood of `a` and the image of this neighborhood
under `f` meets every interval `(b, f a)`, `b < f a`, then `f` is continuous at `a` from the left.

The assumption `hfs : ∀ b < f a, ∃ c ∈ s, f c ∈ Ioo b (f a)` cannot be replaced by the weaker
assumption `hfs : ∀ b < f a, ∃ c ∈ s, f c ∈ Ico b (f a)` we use for strictly monotone functions
because otherwise the function `floor : ℝ → ℤ` would be a counter-example at `a = 0`. -/
theorem continuousWithinAt_left_of_monotoneOn_of_exists_between {f : α → β} {s : Set α} {a : α}
    (hf : MonotoneOn f s) (hs : s ∈ 𝓝[≤] a) (hfs : ∀ b < f a, ∃ c ∈ s, f c ∈ Ioo b (f a)) :
    ContinuousWithinAt f (Iic a) a :=
  @continuousWithinAt_right_of_monotoneOn_of_exists_between αᵒᵈ βᵒᵈ _ _ _ _ _ _ f s a hf.dual hs
    fun b hb =>
    let ⟨c, hcs, hcb, hca⟩ := hfs b hb
    ⟨c, hcs, hca, hcb⟩

/-- If a function `f` with a densely ordered codomain is monotone on a left neighborhood of `a` and
the closure of the image of this neighborhood under `f` is a left neighborhood of `f a`, then `f` is
continuous at `a` from the left -/
theorem continuousWithinAt_left_of_monotoneOn_of_closure_image_mem_nhdsWithin [DenselyOrdered β]
    {f : α → β} {s : Set α} {a : α} (hf : MonotoneOn f s) (hs : s ∈ 𝓝[≤] a)
    (hfs : closure (f '' s) ∈ 𝓝[≤] f a) : ContinuousWithinAt f (Iic a) a :=
  @continuousWithinAt_right_of_monotoneOn_of_closure_image_mem_nhdsWithin αᵒᵈ βᵒᵈ _ _ _ _ _ _ _ f s
    a hf.dual hs hfs

/-- If a function `f` with a densely ordered codomain is monotone on a left neighborhood of `a` and
the image of this neighborhood under `f` is a left neighborhood of `f a`, then `f` is continuous at
`a` from the left. -/
theorem continuousWithinAt_left_of_monotoneOn_of_image_mem_nhdsWithin [DenselyOrdered β] {f : α → β}
    {s : Set α} {a : α} (h_mono : MonotoneOn f s) (hs : s ∈ 𝓝[≤] a) (hfs : f '' s ∈ 𝓝[≤] f a) :
    ContinuousWithinAt f (Iic a) a :=
  continuousWithinAt_left_of_monotoneOn_of_closure_image_mem_nhdsWithin h_mono hs
    (mem_of_superset hfs subset_closure)

/-- If a function `f` with a densely ordered codomain is strictly monotone on a left neighborhood of
`a` and the closure of the image of this neighborhood under `f` is a left neighborhood of `f a`,
then `f` is continuous at `a` from the left. -/
theorem StrictMonoOn.continuousWithinAt_left_of_closure_image_mem_nhdsWithin [DenselyOrdered β]
    {f : α → β} {s : Set α} {a : α} (h_mono : StrictMonoOn f s) (hs : s ∈ 𝓝[≤] a)
    (hfs : closure (f '' s) ∈ 𝓝[≤] f a) : ContinuousWithinAt f (Iic a) a :=
  h_mono.dual.continuousWithinAt_right_of_closure_image_mem_nhdsWithin hs hfs

/-- If a function `f` with a densely ordered codomain is strictly monotone on a left neighborhood of
`a` and the image of this neighborhood under `f` is a left neighborhood of `f a`, then `f` is
continuous at `a` from the left. -/
theorem StrictMonoOn.continuousWithinAt_left_of_image_mem_nhdsWithin [DenselyOrdered β] {f : α → β}
    {s : Set α} {a : α} (h_mono : StrictMonoOn f s) (hs : s ∈ 𝓝[≤] a) (hfs : f '' s ∈ 𝓝[≤] f a) :
    ContinuousWithinAt f (Iic a) a :=
  h_mono.dual.continuousWithinAt_right_of_image_mem_nhdsWithin hs hfs

/-- If a function `f` is strictly monotone on a left neighborhood of `a` and the image of this
neighborhood under `f` includes `Iio (f a)`, then `f` is continuous at `a` from the left. -/
theorem StrictMonoOn.continuousWithinAt_left_of_surjOn {f : α → β} {s : Set α} {a : α}
    (h_mono : StrictMonoOn f s) (hs : s ∈ 𝓝[≤] a) (hfs : SurjOn f s (Iio (f a))) :
    ContinuousWithinAt f (Iic a) a :=
  h_mono.dual.continuousWithinAt_right_of_surjOn hs hfs

/-- If a function `f` is strictly monotone on a neighborhood of `a` and the image of this
neighborhood under `f` meets every interval `[b, f a)`, `b < f a`, and every interval
`(f a, b]`, `b > f a`, then `f` is continuous at `a`. -/
theorem StrictMonoOn.continuousAt_of_exists_between {f : α → β} {s : Set α} {a : α}
    (h_mono : StrictMonoOn f s) (hs : s ∈ 𝓝 a) (hfs_l : ∀ b < f a, ∃ c ∈ s, f c ∈ Ico b (f a))
    (hfs_r : ∀ b > f a, ∃ c ∈ s, f c ∈ Ioc (f a) b) : ContinuousAt f a :=
  continuousAt_iff_continuous_left_right.2
    ⟨h_mono.continuousWithinAt_left_of_exists_between (mem_nhdsWithin_of_mem_nhds hs) hfs_l,
      h_mono.continuousWithinAt_right_of_exists_between (mem_nhdsWithin_of_mem_nhds hs) hfs_r⟩

/-- If a function `f` with a densely ordered codomain is strictly monotone on a neighborhood of `a`
and the closure of the image of this neighborhood under `f` is a neighborhood of `f a`, then `f` is
continuous at `a`. -/
theorem StrictMonoOn.continuousAt_of_closure_image_mem_nhds [DenselyOrdered β] {f : α → β}
    {s : Set α} {a : α} (h_mono : StrictMonoOn f s) (hs : s ∈ 𝓝 a)
    (hfs : closure (f '' s) ∈ 𝓝 (f a)) : ContinuousAt f a :=
  continuousAt_iff_continuous_left_right.2
    ⟨h_mono.continuousWithinAt_left_of_closure_image_mem_nhdsWithin (mem_nhdsWithin_of_mem_nhds hs)
        (mem_nhdsWithin_of_mem_nhds hfs),
      h_mono.continuousWithinAt_right_of_closure_image_mem_nhdsWithin
        (mem_nhdsWithin_of_mem_nhds hs) (mem_nhdsWithin_of_mem_nhds hfs)⟩

/-- If a function `f` with a densely ordered codomain is strictly monotone on a neighborhood of `a`
and the image of this set under `f` is a neighborhood of `f a`, then `f` is continuous at `a`. -/
theorem StrictMonoOn.continuousAt_of_image_mem_nhds [DenselyOrdered β] {f : α → β} {s : Set α}
    {a : α} (h_mono : StrictMonoOn f s) (hs : s ∈ 𝓝 a) (hfs : f '' s ∈ 𝓝 (f a)) :
    ContinuousAt f a :=
  h_mono.continuousAt_of_closure_image_mem_nhds hs (mem_of_superset hfs subset_closure)

/-- If `f` is a monotone function on a neighborhood of `a` and the image of this neighborhood under
`f` meets every interval `(b, f a)`, `b < f a`, and every interval `(f a, b)`, `b > f a`, then `f`
is continuous at `a`. -/
theorem continuousAt_of_monotoneOn_of_exists_between {f : α → β} {s : Set α} {a : α}
    (h_mono : MonotoneOn f s) (hs : s ∈ 𝓝 a) (hfs_l : ∀ b < f a, ∃ c ∈ s, f c ∈ Ioo b (f a))
    (hfs_r : ∀ b > f a, ∃ c ∈ s, f c ∈ Ioo (f a) b) : ContinuousAt f a :=
  continuousAt_iff_continuous_left_right.2
    ⟨continuousWithinAt_left_of_monotoneOn_of_exists_between h_mono (mem_nhdsWithin_of_mem_nhds hs)
        hfs_l,
      continuousWithinAt_right_of_monotoneOn_of_exists_between h_mono
        (mem_nhdsWithin_of_mem_nhds hs) hfs_r⟩

/-- If a function `f` with a densely ordered codomain is monotone on a neighborhood of `a` and the
closure of the image of this neighborhood under `f` is a neighborhood of `f a`, then `f` is
continuous at `a`. -/
theorem continuousAt_of_monotoneOn_of_closure_image_mem_nhds [DenselyOrdered β] {f : α → β}
    {s : Set α} {a : α} (h_mono : MonotoneOn f s) (hs : s ∈ 𝓝 a)
    (hfs : closure (f '' s) ∈ 𝓝 (f a)) : ContinuousAt f a :=
  continuousAt_iff_continuous_left_right.2
    ⟨continuousWithinAt_left_of_monotoneOn_of_closure_image_mem_nhdsWithin h_mono
        (mem_nhdsWithin_of_mem_nhds hs) (mem_nhdsWithin_of_mem_nhds hfs),
      continuousWithinAt_right_of_monotoneOn_of_closure_image_mem_nhdsWithin h_mono
        (mem_nhdsWithin_of_mem_nhds hs) (mem_nhdsWithin_of_mem_nhds hfs)⟩

/-- If a function `f` with a densely ordered codomain is monotone on a neighborhood of `a` and the
image of this neighborhood under `f` is a neighborhood of `f a`, then `f` is continuous at `a`. -/
theorem continuousAt_of_monotoneOn_of_image_mem_nhds [DenselyOrdered β] {f : α → β} {s : Set α}
    {a : α} (h_mono : MonotoneOn f s) (hs : s ∈ 𝓝 a) (hfs : f '' s ∈ 𝓝 (f a)) : ContinuousAt f a :=
  continuousAt_of_monotoneOn_of_closure_image_mem_nhds h_mono hs
    (mem_of_superset hfs subset_closure)

/-- A monotone function with densely ordered codomain and a dense range is continuous. -/
theorem Monotone.continuous_of_denseRange [DenselyOrdered β] {f : α → β} (h_mono : Monotone f)
    (h_dense : DenseRange f) : Continuous f :=
  continuous_iff_continuousAt.mpr fun a =>
    continuousAt_of_monotoneOn_of_closure_image_mem_nhds (fun _ _ _ _ hxy => h_mono hxy)
        univ_mem <|
      by simp only [image_univ, h_dense.closure_eq, univ_mem]

/-- A monotone surjective function with a densely ordered codomain is continuous. -/
theorem Monotone.continuous_of_surjective [DenselyOrdered β] {f : α → β} (h_mono : Monotone f)
    (h_surj : Function.Surjective f) : Continuous f :=
  h_mono.continuous_of_denseRange h_surj.denseRange

end LinearOrder

/-!
### Continuity of order isomorphisms

In this section we prove that an `OrderIso` is continuous, hence it is a `Homeomorph`. We prove
this for an `OrderIso` between to partial orders with order topology.
-/


namespace OrderIso

variable {α β : Type*} [Preorder α] [Preorder β] [TopologicalSpace α] [TopologicalSpace β]
  [OrderTopology α] [OrderTopology β]

protected theorem continuous (e : α ≃o β) : Continuous e := by
  rw [‹OrderTopology β›.topology_eq_generate_intervals, continuous_generateFrom_iff]
  rintro s ⟨a, rfl | rfl⟩
  · rw [e.preimage_Ioi]
    apply isOpen_lt'
  · rw [e.preimage_Iio]
    apply isOpen_gt'

instance : HomeomorphClass (α ≃o β) α β where
  map_continuous := OrderIso.continuous
  inv_continuous e := e.symm.continuous

/-- An order isomorphism between two linear order `OrderTopology` spaces is a homeomorphism. -/
abbrev toHomeomorph (e : α ≃o β) : α ≃ₜ β :=
  HomeomorphClass.toHomeomorph e

theorem coe_toHomeomorph (e : α ≃o β) : ⇑e.toHomeomorph = e :=
  rfl --Simp can prove this too

@[simp]
theorem coe_toHomeomorph_symm (e : α ≃o β) : ⇑e.toHomeomorph.symm = e.symm :=
  rfl

end OrderIso
