/-
Copyright (c) 2025 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, Anatole Dedecker
-/
module

public import Mathlib.Analysis.Convex.Quasiconvex
public import Mathlib.Order.SaddlePoint
public import Mathlib.Topology.Instances.EReal.Lemmas

/-! # Formalization of the von Neumann Sion theorem

## Statements

`Sion.exists_isSaddlePointOn` :
Let X and Y be convex subsets of topological vector spaces E and F,
X being moreover compact,
and let f : X × Y → ℝ be a function such that
- for all x, f(x, ⬝) is upper semicontinuous and quasiconcave
- for all y, f(⬝, y) is lower semicontinuous and quasiconvex
Then inf_x sup_y f(x,y) = sup_y inf_x f(x,y).

The classical case of the theorem assumes that f is continuous,
f(x, ⬝) is concave, f(⬝, y) is convex.

As a particular case, one get the von Neumann theorem where
f is bilinear and E, F are finite dimensional.

We follow the proof of [Komiya-1988][Komiya (1988)].

## Remark on implementation
  * The essential part of the proof holds for a function
  `f : X → Y → β`, where `β` is a complete dense linear order.
  * We have written part of it for just a dense linear order,

  * On the other hand, if the theorem holds for such `β`,
  it must hold for any linear order, for the reason that
  any linear order embeds into a complete dense linear order.
  However, this result does not seem to be known to Mathlib.
  * When `β` is `ℝ`, one can use `Real.toEReal` and one gets a proof for `ℝ`.

## TODO

Explicit the classical particular cases (in particular, von Neumann)

## References

- [vonNeumann-1928][Neumann, John von (1928).
  ”Zur Theorie der Gesellschaftsspiele”. *Mathematische Annalen* 100 (1): 295‑320]

- [Sion-1958][Sion, Maurice (1958).
  ”On general minimax theorems”. *Pacific Journal of Mathematics* 8 (1): 171‑76.]

- [Komiya-1988][Komiya, Hidetoshi (1988).
  “Elementary Proof for Sion’s Minimax Theorem”. *Kodai Mathematical Journal* 11 (1).]

-/

@[expose] public section

open Set Filter

theorem clusterPt_principal_subtype_iff_frequently {α : Type*} [TopologicalSpace α] {s t : Set α}
    (hst : s ⊆ t) {J : Set s} {a : s} :
    ClusterPt a (Filter.principal J) ↔ ∃ᶠ x in nhdsWithin a t, ∃ h : x ∈ s, (⟨x, h⟩ : s) ∈ J := by
  rw [nhdsWithin_eq_map_subtype_coe (hst a.prop), Filter.frequently_map,
    clusterPt_principal_iff_frequently,
    Topology.IsInducing.subtypeVal.nhds_eq_comap, Filter.frequently_comap,
    Topology.IsInducing.subtypeVal.nhds_eq_comap, Filter.frequently_comap, Subtype.coe_mk]
  apply frequently_congr
  apply Eventually.of_forall
  intro x
  simp only [SetCoe.exists, exists_and_left, exists_eq_left]
  exact ⟨fun ⟨h, hx⟩ => ⟨hst h, h, hx⟩, fun ⟨_, hx⟩ => hx⟩

namespace Sion

section LinearOrder

variable {E F : Type*} {β : Type*} [LinearOrder β]
    (X : Set E) (Y : Set F) (f : E → F → β)

/-- The familywise sublevel sets of `f` -/
def C (b : β) (z : F) : Set X :=
  (fun x => f x z) ∘ (fun x ↦ ↑x)⁻¹' Iic b

variable {X Y f}

theorem mem_C_iff {b : β} {y : Y} {x : X} :
    x ∈ C X f b y ↔ f x y ≤ b := by simp [C]

-- private
theorem monotone_C {u v : β} (y : Y) (h : u ≤ v) :
    C X f u y ⊆ C X f v y :=
  fun _ hxu ↦ le_trans hxu h

variable (X Y f) in
/-- The set of parameters `z` in the segment `[y, y']` such that `f b z ≤ f b' y`. -/
def J [AddCommGroup F] [Module ℝ F]
    (b b' : β) (y y' : Y) : Set (segment ℝ y.val y'.val) :=
    {z | C X f b z ⊆ C X f b' y}

theorem mem_J_iff [AddCommGroup F] [Module ℝ F]
    {b b' : β} {y y' : Y} {z : segment ℝ y.val y'.val} :
    z ∈ J X Y f b b' y y' ↔ C X f b z ⊆ C X f b' y := by
  simp only [mem_setOf_eq, J]

-- unused?
theorem y_mem_J [AddCommGroup F] [Module ℝ F]
    {b b' : β} {y y' : Y} (hbb' : b ≤ b') :
    (⟨y.val, left_mem_segment ℝ y.val y'.val⟩ : segment ℝ y.val y'.val) ∈ J X Y f b b' y y' :=
  monotone_C _ hbb'

-- private
theorem disjoint_C {a : E} {b : β} {y y' : Y}
    (ha : ∀ x ∈ X, f a y ⊔ f a y' ≤ f x y ⊔ f x y')
    (hb : b < f a y ⊔ f a y') :
    Disjoint (C X f b y) (C X f b y') := by
  rw [Set.disjoint_iff]
  rintro ⟨x, hx⟩ ⟨hx1, hx2⟩
  simp only [mem_empty_iff_false]
  apply not_le_of_gt hb
  apply le_trans (ha x hx)
  simp only [sup_le_iff]
  exact ⟨hx1, hx2⟩

theorem nonempty_C [TopologicalSpace E]
    (ne_X : X.Nonempty) (kX : IsCompact X)
    (hfy : ∀ y ∈ Y, LowerSemicontinuousOn (fun x : E => f x y) X)
    (y : Y) {b : β} (h : ∀ y ∈ Y, ∃ x ∈ X, f x y ≤ b) :
    (C X f b y).Nonempty := by
  rcases y with ⟨y, hy⟩
  obtain ⟨x, hx, hx_le⟩ := LowerSemicontinuousOn.exists_isMinOn ne_X kX (hfy y hy)
  obtain ⟨x', hx', hx'b⟩ := h y hy
  exact ⟨⟨x, hx⟩, le_trans (hx_le hx') hx'b⟩

theorem isClosed_C [TopologicalSpace E]
    (hfy : ∀ y ∈ Y, LowerSemicontinuousOn (fun x : E => f x y) X)
    (b : β) (y : Y) :
    IsClosed (C X f b y) := by
  specialize hfy y.val y.prop
  rw [← lowerSemicontinuous_restrict_iff] at hfy
  rw [lowerSemicontinuous_iff_isClosed_preimage] at hfy
  exact hfy b

-- private
theorem isPreconnected_C [TopologicalSpace E]
    [AddCommGroup E] [Module ℝ E] [IsTopologicalAddGroup E]
    [ContinuousSMul ℝ E]
    (hfy' : ∀ y ∈ Y, QuasiconvexOn ℝ X fun x ↦ f x y)
    (b : β) (y : Y) :
    IsPreconnected (C X f b y) :=
  (hfy' y.val y.prop).isPreconnected_preimage_subtype

-- private
theorem C_subset_union [AddCommGroup F] [Module ℝ F]
    (hfx' : ∀ x ∈ X, QuasiconcaveOn ℝ Y fun y => f x y)
    (b : β) (y y' : Y) (z : segment ℝ y.val y'.val) :
    C X f b z ⊆ C X f b y ∪ C X f b y' := fun x hx ↦ by
    simp only [Set.mem_union, mem_C_iff, ← inf_le_iff]
    specialize hfx' x x.2 (f x y ⊓ f x y')
    rw [convex_iff_segment_subset] at hfx'
    specialize hfx' ⟨y.prop, inf_le_left⟩ ⟨y'.prop, inf_le_right⟩ z.prop
    exact le_trans hfx'.2 hx

-- private
theorem C_subset_or [TopologicalSpace E] [AddCommGroup E]
    [IsTopologicalAddGroup E] [Module ℝ E] [ContinuousSMul ℝ E]
    [AddCommGroup F] [Module ℝ F]
    (hfx' : ∀ x ∈ X, QuasiconcaveOn ℝ Y fun y => f x y)
    (hfy : ∀ y ∈ Y, LowerSemicontinuousOn (fun x : E => f x y) X)
    (hfy' : ∀ y ∈ Y, QuasiconvexOn ℝ X fun x => f x y)
    (cY : Convex ℝ Y)
    (a : E) (b : β) (y y' : Y)
    (ha : ∀ x ∈ X, f a y ⊔ f a y' ≤ f x y ⊔ f x y')
    (hb : b < f a y ⊔ f a y')
    (z : segment ℝ y.val y'.val) :
    C X f b z ⊆ C X f b y ∨ C X f b z ⊆ C X f b y' := by
  apply isPreconnected_iff_subset_of_disjoint_closed.mp
    (isPreconnected_C hfy' b ⟨z, cY.segment_subset y.prop y'.prop z.prop⟩)
    _ _ (isClosed_C hfy b y) (isClosed_C hfy b y')
    (C_subset_union hfx' b y y' z)
  rw [Set.disjoint_iff_inter_eq_empty.mp (disjoint_C ha hb),
    Set.inter_empty]

theorem C_subset_or'
    [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    (hfy : ∀ y ∈ Y, LowerSemicontinuousOn (fun x : E => f x y) X)
    (hfy' : ∀ y ∈ Y, QuasiconvexOn ℝ X fun x => f x y)
    [AddCommGroup F] [Module ℝ F]
    (cY : Convex ℝ Y)
    (hfx' : ∀ x ∈ X, QuasiconcaveOn ℝ Y fun y => f x y)
    (a : E) (b : β) (y y' : Y)
    (ha : ∀ x ∈ X, f a y ⊔ f a y' ≤ f x y ⊔ f x y')
    (hb : b < f a y ⊔ f a y')
    (z : Y) (hz : z.val ∈ segment ℝ y.val y'.val) :
    C X f b z ⊆ C X f b y ∨ C X f b z ⊆ C X f b y' := by
  apply isPreconnected_iff_subset_of_disjoint_closed.mp
    (isPreconnected_C hfy' b ⟨z, cY.segment_subset y.prop y'.prop hz⟩)
    _ _ (isClosed_C hfy b y) (isClosed_C hfy b y')
    (C_subset_union hfx' b y y' ⟨z, hz⟩)
  rw [Set.disjoint_iff_inter_eq_empty.mp (disjoint_C ha hb),
    Set.inter_empty]

variable [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    (ne_X : X.Nonempty) (kX : IsCompact X)
    (hfy : ∀ y ∈ Y, LowerSemicontinuousOn (fun x : E => f x y) X)
    (hfy' : ∀ y ∈ Y, QuasiconvexOn ℝ X fun x => f x y)

variable [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]
    (cY : Convex ℝ Y) (kY : IsCompact Y)
    (hfx : ∀ x ∈ X, UpperSemicontinuousOn (fun y : F => f x y) Y)
    (hfx' : ∀ x ∈ X, QuasiconcaveOn ℝ Y fun y => f x y)

-- private
include ne_X kX hfx hfx' cY hfy hfy' in
theorem isClosed_J
    (a : E) (b b' : β) (y y' : Y)
    (ha : ∀ x ∈ X, f a y ⊔ f a y' ≤ f x y ⊔ f x y')
    (hb : ∀ y ∈ Y, ∃ x ∈ X, f x y ≤ b)
    (hb' : b' < f a y ⊔ f a y')
    (hbb' : b < b') :
    IsClosed (J X Y f b b' y y') := by
  rw [isClosed_iff_clusterPt]
    -- Let `y` be a cluster point of `J1`
    -- let us show it's in `J1`, i.e `C t y ⊆ C t' y1`.
    -- Let `x ∈ C t y`
    -- and let's find some `z ∈ J1` such that `x ∈ C t z ⊆ C t' y1`.
  intro z hz x hx
  have hzY :=(convex_iff_segment_subset.mp cY) y.prop y'.prop z.prop
    /- y = lim yn, yn ∈ J1
       comme x ∈ C t y, on a f x y ≤ t < t',
       comme (f x ⬝) est usc, f x yn < t' pour n assez grand
       donc x ∈ C t' yn pour n assez grand

       pour z ∈ J1 tel que x ∈ C t' z
       On prouve C t' z ⊆ C t' y1
       Par hypothèse, C t z ⊆ C t' y1
       Sinon, C t' z ⊆ C t' y2 (hC_subset_or)
       Donc x ∈ C t' y1 ∩ C t' y2 = ∅, contradiction

       En particulier, x ∈ C yt' y1

    -/
  suffices ∃ z' ∈ J X Y f b b' y y', x ∈ C X f b' (z' : F) by
    obtain ⟨z', hz', hxz'⟩ := this
    suffices C X f b' z' ⊆ C X f b' y by
      exact this hxz'
    apply Or.resolve_right (C_subset_or hfx' hfy hfy' cY a b' y y' ha hb' z')
    intro hz'2
    have hz'Y :=(convex_iff_segment_subset.mp cY) y.prop y'.prop z'.prop
    apply (nonempty_C ne_X kX hfy ⟨z', hz'Y⟩ hb).not_subset_empty
    simp only [← disjoint_iff_inter_eq_empty.mp (disjoint_C ha hb')]
    apply Set.subset_inter hz'
    apply subset_trans (monotone_C _ hbb'.le) hz'2
    -- The first goal is to rewrite hfy (lsc of (f ⬝ y)) into an ∀ᶠ form
  simp only [UpperSemicontinuousOn, UpperSemicontinuousWithinAt] at hfx
  have := lt_of_le_of_lt hx hbb'
  dsimp only [Function.comp_apply] at this
  specialize hfx x.val x.prop z (cY.segment_subset y.prop y'.prop z.prop) b'
    (lt_of_le_of_lt hx hbb')
    -- We rewrite h into an ∃ᶠ form
  rw [clusterPt_principal_subtype_iff_frequently (cY.segment_subset y.prop y'.prop)] at hz
  suffices ∀ᶠ z' : F in nhdsWithin z Y,
    (∃ hz' : z' ∈ segment ℝ y.val y'.val,
      (⟨z', hz'⟩ : segment ℝ y.val y'.val) ∈ J X Y f b b' y y') →
      ∃ hz' : z' ∈ segment ℝ y.val y'.val, x ∈ C X f b' z'
        ∧ (⟨z', hz'⟩ : segment ℝ y.val y'.val) ∈ J X Y f b b' y y' by
    obtain ⟨z', hz', hxz'1, hxz'2⟩ := Filter.Frequently.exists (Filter.Frequently.mp hz this)
    exact ⟨⟨z', hz'⟩, ⟨hxz'2, hxz'1⟩⟩
  apply Filter.Eventually.mp hfx
  apply Filter.Eventually.of_forall
  intro z hzt'
  rintro ⟨hz, hz'⟩
  exact ⟨hz, ⟨le_of_lt hzt', hz'⟩⟩

variable [DenselyOrdered β]
variable [IsTopologicalAddGroup F] [ContinuousSMul ℝ F]

include ne_X kX hfx hfx' cY hfy hfy' in
theorem exists_lt_iInf_of_lt_iInf_of_sup
    {y1 : F} (hy1 : y1 ∈ Y) {y2 : F} (hy2 : y2 ∈ Y) {t : β}
    (ht : ∀ x ∈ X, t < f x y1 ⊔ f x y2) :
    ∃ y0 ∈ Y, ∀ x ∈ X, t < f x y0 := by
  by_contra hinfi_le
  push_neg at hinfi_le
  obtain ⟨a, ha, ha'⟩ := LowerSemicontinuousOn.exists_isMinOn
    ne_X kX (LowerSemicontinuousOn.sup (hfy y1 hy1) (hfy y2 hy2))
  obtain ⟨t', htt', ht'⟩ := exists_between (ht a ha)
  let J1 := J X Y f t t' ⟨y1, hy1⟩ ⟨y2, hy2⟩
  have mem_J1_iff : ∀ (z : F) (hz : z ∈ segment ℝ y1 y2),
      ⟨z, hz⟩ ∈ J1 ↔ C X f t z ⊆ C X f t' y1 :=
    fun z _ ↦ by simp [J1, J]
  let φ : segment ℝ y1 y2 ≃ₜ segment ℝ y2 y1 := by
    apply Homeomorph.subtype (Homeomorph.refl F)
    intro x
    rw [segment_symm ℝ y2 y1]
    simp only [Homeomorph.refl_apply, id_eq]
  let J2 := φ ⁻¹' (J X Y f t t' ⟨y2, hy2⟩ ⟨y1, hy1⟩)
  have mem_J2_iff (z) (hz : z ∈ segment ℝ y1 y2) :
      ⟨z, hz⟩ ∈ J2 ↔ C X f t z ⊆ C X f t' y2 := by simp [J2, J, φ]
  have hJ1J2 : J1 ∩ J2 = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    simp only [mem_inter_iff, not_and]
    rintro ⟨z, hz⟩ hz1 hz2
    simp only [mem_J1_iff] at hz1
    simp only [mem_J2_iff] at hz2
    have hz_mem_Y : z ∈ Y := cY.segment_subset hy1 hy2 hz
    apply Set.Nonempty.not_subset_empty (nonempty_C ne_X kX hfy ⟨z, hz_mem_Y⟩ hinfi_le)
    rw [Set.subset_empty_iff, ← bot_eq_empty, ← disjoint_self]
    exact Set.disjoint_of_subset hz1 hz2 (disjoint_C (y := ⟨y1, hy1⟩) (y' := ⟨y2, hy2⟩) ha' ht')
  have hJ1_union_J2 : J1 ∪ J2 = segment ℝ y1 y2 := by
    ext z
    constructor
    · rintro ⟨⟨z, hz⟩, _, rfl⟩
      exact hz
    · intro hz
      have hz_mem_Y : z ∈ Y := cY.segment_subset hy1 hy2 hz
      use ⟨z, hz⟩
      refine ⟨?_, rfl⟩
      rcases C_subset_or hfx' hfy hfy' cY a t' ⟨y1, hy1⟩ ⟨y2, hy2⟩ ha' ht' ⟨z, hz⟩ with (h1 | h2)
      · left
        simp only [mem_J1_iff]
        exact subset_trans (monotone_C ⟨z, hz_mem_Y⟩ htt'.le) h1
      · right
        simp only [mem_J2_iff]
        exact subset_trans (monotone_C ⟨z, hz_mem_Y⟩ htt'.le) h2
  suffices IsPreconnected (Set.univ : Set (segment ℝ y1 y2)) by
    rw [isPreconnected_iff_subset_of_disjoint_closed] at this
    rw [Set.eq_empty_iff_forall_notMem] at hJ1J2
    rcases this J1 J2 ?_ ?_ ?_ ?_ with (h1 | h2)
    · apply hJ1J2 ⟨y2, right_mem_segment ℝ y1 y2⟩
      rw [Set.mem_inter_iff]
      refine ⟨h1 (Set.mem_univ _), ?_⟩
      rw [mem_J2_iff]
      apply monotone_C ⟨y2, hy2⟩ htt'.le
    · apply hJ1J2 ⟨y1, left_mem_segment ℝ y1 y2⟩
      rw [Set.mem_inter_iff]
      refine ⟨?_, h2 (Set.mem_univ _)⟩
      rw [mem_J1_iff]
      apply monotone_C ⟨y1, hy1⟩ htt'.le
  · rw [← Set.eq_empty_iff_forall_notMem] at hJ1J2
    simp only [hJ1J2, inter_empty]
  · -- is preconnected
    rw [← Topology.IsInducing.subtypeVal.isPreconnected_image]
    simp only [image_univ, Subtype.range_coe_subtype, setOf_mem_eq]
    exact Convex.isPreconnected (convex_segment y1 y2)
  · -- is closed J1
    exact isClosed_J ne_X kX hfy hfy' cY hfx hfx' a t t' ⟨y1, hy1⟩ ⟨y2, hy2⟩ ha' hinfi_le ht' htt'
  · -- is closed J2
    rw [Homeomorph.isClosed_preimage]
    simp only [sup_comm (f _ y1)] at ha' ht'
    refine isClosed_J ne_X kX hfy hfy' cY hfx hfx' a t t' ⟨y2, hy2⟩ ⟨y1, hy1⟩ ha' hinfi_le ht' htt'
  · -- univ ⊆ J1 ∪ J2
    rintro ⟨z, hz⟩ _
    rw [← hJ1_union_J2] at hz
    rcases hz with ⟨⟨z, hz'⟩, hz'', rfl⟩
    exact hz''

variable (cX : Convex ℝ X)

include ne_X cX cY kX hfx hfx' hfy hfy' in
theorem exists_lt_iInf_of_lt_iInf_of_finite
    {s : Set F} (hs : s.Finite) (hsY : s ⊆ Y)
    {t : β} (ht : ∀ x ∈ X, ∃ y ∈ s, t < f x y) :
    ∃ y0 ∈ Y, ∀ x ∈ X, t < f x y0 := by
  induction s, hs using Set.Finite.induction_on
    generalizing X with
  | empty => -- empty case
    obtain ⟨x, hx⟩ := id ne_X
    exfalso
    simpa using ht x hx
  | @insert b s _ hs hrec =>  -- insert case
    have hb : (b ∈ Y) := hsY (mem_insert b s)
    let X' := {x ∈ X | f x b ≤ t}
   -- let X' := leSublevelOn X (fun x ↦ f x b) t
    rcases Set.eq_empty_or_nonempty X' with X'_e | X'_ne
    · simp only [sep_eq_empty_iff_mem_false, not_le, X'] at X'_e
      use b, hb
    -- the nonempty case
    have hX'X : X' ⊆ X := sep_subset X _
    have kX' : IsCompact X' := sorry
     -- (hfy b hb).isCompact_leSublevelOn kX t
    have cX' : Convex ℝ X' := hfy' b hb t
    specialize hrec X'_ne kX'
      (fun y hy ↦ LowerSemicontinuousOn.mono (hfy y hy) hX'X)
      (fun y hy ↦ cX'.quasiconvexOn_restrict (hfy' y hy) hX'X)
      (fun x hx' ↦ hfx x (hX'X hx'))
      (fun x hx' ↦ hfx' x (hX'X hx'))
      cX'
    have ht_lt : ∀ x ∈ X', ∃ y ∈ s, t < f x y := by
        /- sinon, si  infi x ∈ X', supr y ∈ s f x y ≤ t
          pour tout t' > t, il existe x ∈ X', supr y ∈ s f x y ≤ t',
          comme x ∈ X' et t ≤ t', on  a supr y ∈ insert b s f x y  ≤ t',
          donc infi x ∈ X, supr y ∈ insert b s, f x y ≤ t',
          donc infi x ∈ X, supr y ∈ insert b s, f x y ≤ t -/
      intro x hx
      obtain ⟨y, hy, h⟩ := ht x hx.1
      rcases hy with hy | hy
      · exfalso
        rw [hy, ← not_le] at h
        exact h hx.2
      · exact ⟨y, hy, h⟩
    obtain ⟨y1, hy1, hty1⟩ := hrec (subset_trans (subset_insert b s) hsY) ht_lt
    apply exists_lt_iInf_of_lt_iInf_of_sup ne_X kX hfy hfy' cY hfx hfx' hb hy1
    intro x hx
    by_cases hx' : x ∈ X'
    · exact lt_of_lt_of_le (hty1 x hx') (le_sup_right)
    · apply lt_of_lt_of_le _ (le_sup_left)
      rw [← not_le]
      exact fun h ↦ hx' ⟨hx, h⟩

    -- hsup_y : ∀ x ∈ X, sup_y x = sup [y ∈ Y] f x y
    -- hinf_x : ∀ y ∈ Y, inf_x y = inf [x ∈ X] f x y
    -- hinf_sup : inf_sup = inf [x ∈ X] sup_y x
    -- hsup_inf : sup_inf = sup [y ∈ Y] inf_x y
include ne_X cX cY kX hfx hfx' hfy hfy' in
/-- A minimax theorem without completeness, using `IsGLB` and `IsULB`. -/
theorem minimax
    (sup_y : E → β) (hsup_y : ∀ x ∈ X, IsLUB {f x y | y ∈ Y} (sup_y x))
    (inf_sup : β) (hinf_sup : IsGLB {sup_y x | x ∈ X} inf_sup)
    (inf_x : F → β) (hinf_x : ∀ y ∈ Y, IsGLB {f x y | x ∈ X} (inf_x y))
    (sup_inf : β) (hsup_inf : IsLUB {inf_x y | y ∈ Y} sup_inf) :
    inf_sup = sup_inf := by
  apply symm
  apply le_antisymm
  -- the obvious inequality
  · rw [le_isGLB_iff hinf_sup, mem_lowerBounds]
    rintro _ ⟨x, hx, rfl⟩
    rw [isLUB_le_iff hsup_inf, mem_upperBounds]
    rintro _ ⟨y, hy, rfl⟩
    trans f x y
    · exact (hinf_x y hy).1 ⟨x, hx, rfl⟩
    · exact (hsup_y x hx).1 ⟨y, hy, rfl⟩
  -- the delicate inequality
  rcases eq_empty_or_nonempty Y with ⟨rfl⟩ | ne_Y
  · -- the case when `Y` is empty is trivial
    simp only [mem_empty_iff_false, IsEmpty.forall_iff, implies_true, false_and, exists_const,
      setOf_false, isLUB_empty_iff] at *
    replace hsup_y : ∀ x ∈ X,  sup_y x = sup_inf :=
      fun x hx ↦ le_antisymm (hsup_y x hx sup_inf) (hsup_inf (sup_y x))
    simp only [isGLB_iff_le_iff] at hinf_sup
    have : {t | ∃ x ∈ X, sup_y x = t} = {sup_inf} := by
      ext t
      simp only [mem_setOf_eq, mem_singleton_iff]
      constructor
      · rintro ⟨x, hx, hxt⟩
        rw [← hxt, hsup_y x hx]
      · intro ht
        obtain ⟨x, hx⟩ := ne_X
        exact ⟨x, hx, ht ▸ hsup_y x hx⟩
    simp only [this, lowerBounds_singleton, mem_Iic] at hinf_sup
    rw [← hinf_sup]
  -- when `Y` is not empty
  rw [← forall_lt_iff_le]
  intro t ht
  have : ⋂ y ∈ Y, {x ∈ X | f x y ≤ t} = ∅ := by
    apply Set.eq_empty_of_forall_notMem
    intro x hx
    simp only [mem_iInter, mem_setOf_eq] at hx
    rw [lt_isGLB_iff hinf_sup] at ht
    obtain ⟨c, hc, htc⟩ := ht
    simp only [mem_lowerBounds, mem_setOf_eq, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂] at hc
    have hxX : x ∈ X := by
      obtain ⟨y, hy⟩ := ne_Y
      exact (hx y hy).1
    specialize hc x hxX
    apply not_le.mpr htc (le_trans hc _)
    rw [isLUB_le_iff (hsup_y x hxX), mem_upperBounds]
    aesop
  -- rw [LowerSemicontinuousOn.inter_leSublevelOn_empty_iff_exists_finset_inter kX ne_Y hfy] at this
  sorry
  obtain ⟨s, hs⟩ := this
  have hs' (x) (hx : x ∈ X) :
      ∃ y ∈ Subtype.val '' (s : Set Y), t < f x y := by
    obtain ⟨i, hi, hi'⟩ := hs x hx
    use i.val
    simp [hi, hi']
  choose y0 hy0 ht0 using exists_lt_iInf_of_lt_iInf_of_finite
        ne_X kX hfy hfy' cY hfx hfx' cX
        (t := t)
        (toFinite _) (Subtype.coe_image_subset Y ↑s)
  simp only [lt_isLUB_iff hsup_inf, mem_setOf_eq, exists_exists_and_eq_and]
  use y0 hs', hy0 hs'
  specialize ht0 hs'
  obtain ⟨a, ha, h⟩ := LowerSemicontinuousOn.exists_isMinOn ne_X kX (hfy (y0  hs') (hy0 hs'))
  apply lt_of_lt_of_le (ht0 a ha)
  simpa [le_isGLB_iff (hinf_x (y0 hs') (hy0 hs')), mem_lowerBounds]

variable (ne_Y : Y.Nonempty) (kY : IsCompact Y)
include ne_X ne_Y cX cY kX kY hfx hfx' hfy hfy' in
/-- The Sion-von Neumann minimax theorem (saddle point form) -/
theorem exists_isSaddlePointOn' :
    ∃ a ∈ X, ∃ b ∈ Y, IsSaddlePointOn X Y f a b := by
  have hmax_y (x) (hx : x ∈ X) : ∃ y ∈ Y, IsMaxOn (f x) Y y := (hfx x hx).exists_isMaxOn ne_Y kY
  choose! η η_mem η_max using hmax_y
  have hlsc : LowerSemicontinuousOn (fun x => f x (η x)) X :=
    lowerSemicontinuousOn_of_forall_isMaxOn_and_mem hfy η_mem η_max
  obtain ⟨a, ha, ha'⟩ : ∃ a ∈ X, IsMinOn (fun x ↦ f x (η x)) X a := hlsc.exists_isMinOn ne_X kX
  use a, ha
  have hmin_x (y) (hy : y ∈ Y) : ∃ x ∈ X, IsMinOn (f · y) X x := (hfy y hy).exists_isMinOn ne_X kX
  choose! ξ ξ_mem ξ_min using hmin_x
  have husc := upperSemicontinuousOn_of_forall_isMinOn_and_mem hfx ξ_mem ξ_min
  obtain ⟨b, hb, hb'⟩ : ∃ b ∈ Y, IsMaxOn (fun y ↦ f (ξ y) y) Y b := husc.exists_isMaxOn ne_Y kY
  use b, hb
  intro x hx y hy
  trans f a (η a)
  · simp only [isMaxOn_iff] at η_max
    exact η_max a ha y hy
  trans f (ξ b) b
  · apply le_of_eq
    apply minimax ne_X kX hfy hfy' cY hfx hfx' cX
      (fun x ↦ f x (η x))
      (fun x hx ↦ (η_max x hx).isLUB (η_mem x hx))
      (f a (η a))
      (ha'.isGLB ha)
      (fun y ↦ f (ξ y) y)
      (fun y hy ↦ (ξ_min y hy).isGLB (ξ_mem y hy))
      (f (ξ b) b)
      (hb'.isLUB hb)
  · simp only [isMinOn_iff] at ξ_min
    exact ξ_min b hb x hx

end LinearOrder

section CompleteLinearOrder

variable {E F β : Type*} [CompleteLinearOrder β] [DenselyOrdered β]
variable {X : Set E} {Y : Set F} {f : E → F → β}
variable [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    (ne_X : X.Nonempty) (cX : Convex ℝ X) (kX : IsCompact X)
    (hfy : ∀ y ∈ Y, LowerSemicontinuousOn (fun x : E ↦ f x y) X)
    (hfy' : ∀ y ∈ Y, QuasiconvexOn ℝ X fun x => f x y)

variable [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F]
  (cY : Convex ℝ Y) (ne_Y : Y.Nonempty) (kY : IsCompact Y)
  (hfx : ∀ x ∈ X, UpperSemicontinuousOn (fun y : F => f x y) Y)
  (hfx' : ∀ x ∈ X, QuasiconcaveOn ℝ Y fun y => f x y)

include ne_X cX cY kX hfx hfx' hfy hfy' in
/-- A minimax theorem in inf-sup form, for complete linear orders. -/
theorem minimax' : (⨅ x ∈ X, ⨆ y ∈ Y, f x y) = ⨆ y ∈ Y, ⨅ x ∈ X, f x y := by
  apply symm
  apply le_antisymm
  -- the obvious inclusion
  · exact iSup₂_iInf₂_le_iInf₂_iSup₂ X Y f
  -- the delicate inclusion
  rcases eq_empty_or_nonempty Y with ⟨rfl⟩ | ne_Y
  · simp [biInf_const ne_X]
  rw [← forall_lt_iff_le]
  intro t ht
  have : ⋂ y ∈ Y, {x ∈ X | f x y ≤ t} = ∅ := by
    apply Set.eq_empty_of_forall_notMem
    intro x hx
    simp only [mem_iInter, mem_setOf_eq] at hx
    rw [lt_iInf_iff] at ht
    obtain ⟨c, htc, hc⟩ := ht
    apply not_le.mpr htc
    simp only [le_iInf_iff] at hc
    apply le_trans (hc x ?_) (by aesop)
    obtain ⟨y, hy⟩ := ne_Y
    exact (hx y hy).1
  sorry
  -- rw [LowerSemicontinuousOn.inter_leSublevelOn_empty_iff_exists_finset_inter kX ne_Y hfy] at this
  obtain ⟨s, hs⟩ := this
  have hs' (x) (hx : x ∈ X) :
      ∃ y ∈ Subtype.val '' (s : Set Y), t < f x y := by
    obtain ⟨i, hi, hi'⟩ := hs x hx
    use i.val
    simp [hi, hi']
  choose y0 hy0 ht0 using exists_lt_iInf_of_lt_iInf_of_finite
        ne_X kX hfy hfy' cY hfx hfx' cX
        (t := t)
        (toFinite _) (Subtype.coe_image_subset Y ↑s)
  simp only [lt_iSup_iff]
  use y0 hs', hy0 hs'
  specialize ht0 hs'
  obtain ⟨a, ha, h⟩ := LowerSemicontinuousOn.exists_isMinOn ne_X kX (hfy (y0  hs') (hy0 hs'))
  apply lt_of_lt_of_le (ht0 a ha)
  simpa only [le_iInf_iff]

include ne_X ne_Y cX cY kX kY hfx hfx' hfy hfy' in
/-- The Sion-von Neumann minimax theorem (saddle point form),
case of complete linear orders. -/
theorem exists_saddlePointOn' :
    ∃ a ∈ X, ∃ b ∈ Y, IsSaddlePointOn X Y f a b := by
  have hlsc : LowerSemicontinuousOn (fun x => ⨆ y ∈ Y, f x y) X := fun x hx ↦ by
    apply lowerSemicontinuousWithinAt_iSup
    intro i
    exact lowerSemicontinuousWithinAt_iSup fun i_1 ↦ hfy i i_1 x hx
  have husc : UpperSemicontinuousOn (fun y => ⨅ x ∈ X, f x y) Y := fun y hy ↦ by
    apply upperSemicontinuousWithinAt_iInf
    intro i
    exact upperSemicontinuousWithinAt_iInf fun i_1 ↦ hfx i i_1 y hy
  obtain ⟨a, ha, ha'⟩ := LowerSemicontinuousOn.exists_isMinOn
   ne_X kX hlsc
  obtain ⟨b, hb, hb'⟩ := UpperSemicontinuousOn.exists_isMaxOn ne_Y kY husc
  use a, ha, b, hb
  rw [isSaddlePointOn_iff' ha hb]
  refine le_trans (le_iInf₂ ha') ?_
  refine le_trans ?_ (iSup₂_le_iff.mpr hb')
  rw [minimax' ne_X cX kX hfy hfy' cY hfx hfx']

end CompleteLinearOrder

section DedekindMacNeille

variable {E F β γ : Type*} [LinearOrder β]

variable {X : Set E} {Y : Set F} {f : E → F → β}
variable [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    (ne_X : X.Nonempty) (cX : Convex ℝ X) (kX : IsCompact X)
    (hfy : ∀ y ∈ Y, LowerSemicontinuousOn (fun x : E ↦ f x y) X)
    (hfy' : ∀ y ∈ Y, QuasiconvexOn ℝ X fun x => f x y)

variable [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F]
  (cY : Convex ℝ Y) (ne_Y : Y.Nonempty) (kY : IsCompact Y)
  (hfx : ∀ x ∈ X, UpperSemicontinuousOn (fun y : F => f x y) Y)
  (hfx' : ∀ x ∈ X, QuasiconcaveOn ℝ Y fun y => f x y)

-- The following lines assume that γ is the Dedekind MacNeille completion of β
variable [TopologicalSpace β] [OrderTopology β]
variable {γ : Type*} [CompleteLinearOrder γ] [DenselyOrdered γ]
  [TopologicalSpace γ] [OrderTopology γ]
  {ι : β ↪o γ} (hι : Continuous ι)

include ne_X ne_Y cX cY kX kY hfx hfx' hfy hfy' hι in
/-- The minimax theorem, in the saddle point form,
when `β` is given a Dedekind-MacNeille completion `ι : β ↪o γ` -/
theorem DMCompletion.exists_isSaddlePointOn :
  ∃ a ∈ X, ∃ b ∈ Y, IsSaddlePointOn X Y f a b := by
  -- Reduce to the cae of EReal-valued functions
  let φ : E → F → γ := fun x y ↦  ι (f x y)
  -- suffices : ∃ a ∈ X, ∃ b ∈ Y, IsSaddlePointOn X Y φ a b
  have hφx (x) (hx : x ∈ X) : UpperSemicontinuousOn (fun y ↦ φ x y) Y := by
    convert Continuous.comp_upperSemicontinuousOn hι (hfx x hx) ι.monotone
  have hφx' (x) (hx : x ∈ X) : QuasiconcaveOn ℝ Y fun y ↦ φ x y := by
    convert (hfx' x hx).monotone_comp ι.monotone
  have hφy (y) (hy : y ∈ Y) : LowerSemicontinuousOn (fun x ↦ φ x y) X := by
    convert Continuous.comp_lowerSemicontinuousOn hι (hfy y hy) ι.monotone
  have hφy' (y) (hy : y ∈ Y) : QuasiconvexOn ℝ X fun x ↦ φ x y := by
    convert (hfy' y hy).monotone_comp ι.monotone
  obtain ⟨a, ha, b, hb, hab⟩ :=
    exists_isSaddlePointOn' ne_X kX hφy hφy' cY kY hφx hφx' cX ne_Y
  use a, ha, b, hb
  intro x hx y hy
  simpa only [OrderEmbedding.le_iff_le, φ] using hab x hx y hy

end DedekindMacNeille

section Real

variable {E F : Type*}
variable {X : Set E} {Y : Set F} {f : E → F → ℝ}
variable [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    (ne_X : X.Nonempty) (cX : Convex ℝ X) (kX : IsCompact X)
    (hfy : ∀ y ∈ Y, LowerSemicontinuousOn (fun x : E ↦ f x y) X)
    (hfy' : ∀ y ∈ Y, QuasiconvexOn ℝ X fun x => f x y)

variable [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F]
  (cY : Convex ℝ Y) (ne_Y : Y.Nonempty) (kY : IsCompact Y)
  (hfx : ∀ x ∈ X, UpperSemicontinuousOn (fun y : F => f x y) Y)
  (hfx' : ∀ x ∈ X, QuasiconcaveOn ℝ Y fun y => f x y)

include ne_X ne_Y cX cY kX kY hfx hfx' hfy hfy' in
/-- The minimax theorem, in the saddle point form -/
theorem exists_isSaddlePointOn :
    ∃ a ∈ X, ∃ b ∈ Y, IsSaddlePointOn X Y f a b :=
  DMCompletion.exists_isSaddlePointOn ne_X cX kX hfy hfy' cY ne_Y kY hfx hfx'
    (ι := EReal.orderEmbedding) (hι := continuous_coe_real_ereal)

end Real

end Sion
