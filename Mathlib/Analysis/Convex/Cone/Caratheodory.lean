import Mathlib.Analysis.Convex.Cone.Pointed
import Mathlib.Analysis.Convex.Caratheodory

universe u

open Set Finset

open BigOperators

def Set.toPointedCone (𝕜 : Type*) {E : Type u} [LinearOrderedField 𝕜] [AddCommGroup E]
    [Module 𝕜 E] (s : Set E) :=
  Submodule.span {c : 𝕜 // 0 ≤ c} s

variable {𝕜 : Type*} {E : Type u} [LinearOrderedField 𝕜] [AddCommGroup E] [Module 𝕜 E]

local notation3 "𝕜≥0" => {c : 𝕜 // 0 ≤ c}

namespace Caratheodory

example (a b : 𝕜) : a ≠ b → a < b ∨ a > b := by exact fun a_1 ↦ Ne.lt_or_lt a_1

-- theorem Fintype.not_linearIndependent_iff'
-- [Fintype ι] :
--     ¬LinearIndependent R v ↔ ∃ g : ι → R, ∑ i, g i • v i = 0 ∧ ∃ i, g i ≠ 0 :=
--     by sorry



theorem mem_convexCone_erase [DecidableEq E] {t : Finset E}
    (h : ¬LinearIndependent 𝕜 ((↑) : t → E))
    {x : E} (hx : x ∈ Submodule.span 𝕜≥0 t) :
    ∃ y : (↑t : Set E), x ∈ Submodule.span 𝕜≥0 (↑(t.erase y) : Set E) := by
  replace ⟨f, combo⟩ := mem_span_finset.1 hx
  replace ⟨g, relation, c, hnzero⟩ := Fintype.not_linearIndependent_iff.1 h
  simp only [mem_span_finset, coe_sort_coe, coe_mem, not_true_eq_false,
    Subtype.exists, exists_prop]
  obtain (hneg | hpos) := Ne.lt_or_lt hnzero
  · let s := @Finset.filter _ (fun z => g z < 0) (fun _ => LinearOrder.decidableLT _ _) Finset.univ
    obtain ⟨d, hd₁, hd₂⟩ := s.exists_min_image (fun z => g z / f z) $ ⟨c, by simpa⟩
    simp at hd₁ hd₂
    use d, d.2

    -- let s := { x // f x < 0 }
    -- haveI : Nonempty s := ⟨c, hfneg⟩
    -- let i₀ := Function.argmin (fun (x : s) => f x / g x)
    -- simp at *
    -- use i₀

    -- have min := min (fun (x : s) => f x / g x)
    --obtain ⟨i₀, hi₀⟩ : ∃ i₀ : t, ∀ i : t, f i₀ / g i₀ ≤ f i / g i := by
    sorry
    --   apply s.exists_min_image fun z => f z / g z
    --   obtain ⟨x, hx, hgx⟩ : ∃ x ∈ t, 0 < g x := gpos
    --   exact ⟨x, mem_filter.mpr ⟨hx, hgx⟩⟩
  · sorry
#exit
  simp only [Finset.convexHull_eq, mem_setOf_eq] at m ⊢
  obtain ⟨f, fpos, fsum, rfl⟩ := m
  obtain ⟨g, gcombo, gsum, gpos⟩ := exists_nontrivial_relation_sum_zero_of_not_affine_ind h
  replace gpos := exists_pos_of_sum_zero_of_exists_nonzero g gsum gpos
  clear h
  let s := @Finset.filter _ (fun z => 0 < g z) (fun _ => LinearOrder.decidableLT _ _) t
  obtain ⟨i₀, mem, w⟩ : ∃ i₀ ∈ s, ∀ i ∈ s, f i₀ / g i₀ ≤ f i / g i := by
    apply s.exists_min_image fun z => f z / g z
    obtain ⟨x, hx, hgx⟩ : ∃ x ∈ t, 0 < g x := gpos
    exact ⟨x, mem_filter.mpr ⟨hx, hgx⟩⟩
  have hg : 0 < g i₀ := by
    rw [mem_filter] at mem
    exact mem.2
  have hi₀ : i₀ ∈ t := filter_subset _ _ mem
  let k : E → 𝕜 := fun z => f z - f i₀ / g i₀ * g z
  have hk : k i₀ = 0 := by field_simp [ne_of_gt hg]
  have ksum : ∑ e in t.erase i₀, k e = 1 := by
    calc
      ∑ e in t.erase i₀, k e = ∑ e in t, k e := by
        conv_rhs => rw [← insert_erase hi₀, sum_insert (not_mem_erase i₀ t), hk, zero_add]
      _ = ∑ e in t, (f e - f i₀ / g i₀ * g e) := rfl
      _ = 1 := by rw [sum_sub_distrib, fsum, ← mul_sum, gsum, mul_zero, sub_zero]
  refine' ⟨⟨i₀, hi₀⟩, k, _, by convert ksum, _⟩
  · simp only [and_imp, sub_nonneg, mem_erase, Ne.def, Subtype.coe_mk]
    intro e _ het
    by_cases hes : e ∈ s
    · have hge : 0 < g e := by
        rw [mem_filter] at hes
        exact hes.2
      rw [← le_div_iff hge]
      exact w _ hes
    · calc
        _ ≤ 0 := by
          apply mul_nonpos_of_nonneg_of_nonpos
          · apply div_nonneg (fpos i₀ (mem_of_subset (filter_subset _ t) mem)) (le_of_lt hg)
          · simpa only [mem_filter, het, true_and_iff, not_lt] using hes
        _ ≤ f e := fpos e het
  · rw [Subtype.coe_mk, centerMass_eq_of_sum_1 _ id ksum]
    calc
      ∑ e in t.erase i₀, k e • e = ∑ e in t, k e • e := sum_erase _ (by rw [hk, zero_smul])
      _ = ∑ e in t, (f e - f i₀ / g i₀ * g e) • e := rfl
      _ = t.centerMass f id := by
        simp only [sub_smul, mul_smul, sum_sub_distrib, ← smul_sum, gcombo, smul_zero, sub_zero,
          centerMass, fsum, inv_one, one_smul, id.def]
#align caratheodory.mem_convex_hull_erase Caratheodory.mem_convexHull_erase

variable {s : Set E} {x : E} (hx : x ∈ convexHull 𝕜 s)

/-- Given a point `x` in the convex hull of a set `s`, this is a finite subset of `s` of minimum
cardinality, whose convex hull contains `x`. -/
noncomputable def minCardFinsetOfMemConvexHull : Finset E :=
  Function.argminOn Finset.card Nat.lt_wfRel.2 { t | ↑t ⊆ s ∧ x ∈ convexHull 𝕜 (t : Set E) } <| by
    simpa only [convexHull_eq_union_convexHull_finite_subsets s, exists_prop, mem_iUnion] using hx
#align caratheodory.min_card_finset_of_mem_convex_hull Caratheodory.minCardFinsetOfMemConvexHull

theorem minCardFinsetOfMemConvexHull_subseteq : ↑(minCardFinsetOfMemConvexHull hx) ⊆ s :=
  (Function.argminOn_mem _ _ { t : Finset E | ↑t ⊆ s ∧ x ∈ convexHull 𝕜 (t : Set E) } _).1
#align caratheodory.min_card_finset_of_mem_convex_hull_subseteq Caratheodory.minCardFinsetOfMemConvexHull_subseteq

theorem mem_minCardFinsetOfMemConvexHull :
    x ∈ convexHull 𝕜 (minCardFinsetOfMemConvexHull hx : Set E) :=
  (Function.argminOn_mem _ _ { t : Finset E | ↑t ⊆ s ∧ x ∈ convexHull 𝕜 (t : Set E) } _).2
#align caratheodory.mem_min_card_finset_of_mem_convex_hull Caratheodory.mem_minCardFinsetOfMemConvexHull

theorem minCardFinsetOfMemConvexHull_nonempty : (minCardFinsetOfMemConvexHull hx).Nonempty := by
  rw [← Finset.coe_nonempty, ← @convexHull_nonempty_iff 𝕜]
  exact ⟨x, mem_minCardFinsetOfMemConvexHull hx⟩
#align caratheodory.min_card_finset_of_mem_convex_hull_nonempty Caratheodory.minCardFinsetOfMemConvexHull_nonempty

theorem minCardFinsetOfMemConvexHull_card_le_card {t : Finset E} (ht₁ : ↑t ⊆ s)
    (ht₂ : x ∈ convexHull 𝕜 (t : Set E)) : (minCardFinsetOfMemConvexHull hx).card ≤ t.card :=
  Function.argminOn_le _ _ _ (by exact ⟨ht₁, ht₂⟩)
#align caratheodory.min_card_finset_of_mem_convex_hull_card_le_card Caratheodory.minCardFinsetOfMemConvexHull_card_le_card

theorem affineIndependent_minCardFinsetOfMemConvexHull :
    AffineIndependent 𝕜 ((↑) : minCardFinsetOfMemConvexHull hx → E) := by
  let k := (minCardFinsetOfMemConvexHull hx).card - 1
  have hk : (minCardFinsetOfMemConvexHull hx).card = k + 1 :=
    (Nat.succ_pred_eq_of_pos (Finset.card_pos.mpr (minCardFinsetOfMemConvexHull_nonempty hx))).symm
  classical
  by_contra h
  obtain ⟨p, hp⟩ := mem_convexHull_erase h (mem_minCardFinsetOfMemConvexHull hx)
  have contra := minCardFinsetOfMemConvexHull_card_le_card hx (Set.Subset.trans
    (Finset.erase_subset (p : E) (minCardFinsetOfMemConvexHull hx))
    (minCardFinsetOfMemConvexHull_subseteq hx)) hp
  rw [← not_lt] at contra
  apply contra
  erw [card_erase_of_mem p.2, hk]
  exact lt_add_one _
#align caratheodory.affine_independent_min_card_finset_of_mem_convex_hull Caratheodory.affineIndependent_minCardFinsetOfMemConvexHull

end Caratheodory

variable {s : Set E}

/-- **Carathéodory's convexity theorem** -/
theorem convexHull_eq_union : convexHull 𝕜 s =
    ⋃ (t : Finset E) (hss : ↑t ⊆ s) (hai : AffineIndependent 𝕜 ((↑) : t → E)), convexHull 𝕜 ↑t := by
  apply Set.Subset.antisymm
  · intro x hx
    simp only [exists_prop, Set.mem_iUnion]
    exact ⟨Caratheodory.minCardFinsetOfMemConvexHull hx,
      Caratheodory.minCardFinsetOfMemConvexHull_subseteq hx,
      Caratheodory.affineIndependent_minCardFinsetOfMemConvexHull hx,
      Caratheodory.mem_minCardFinsetOfMemConvexHull hx⟩
  · iterate 3 convert Set.iUnion_subset _; intro
    exact convexHull_mono ‹_›
#align convex_hull_eq_union convexHull_eq_union

/-- A more explicit version of `convexHull_eq_union`. -/
theorem eq_pos_convex_span_of_mem_convexHull {x : E} (hx : x ∈ convexHull 𝕜 s) :
    ∃ (ι : Sort (u + 1)) (_ : Fintype ι),
      ∃ (z : ι → E) (w : ι → 𝕜) (_ : Set.range z ⊆ s) (_ : AffineIndependent 𝕜 z)
        (_ : ∀ i, 0 < w i), ∑ i, w i = 1 ∧ ∑ i, w i • z i = x := by
  rw [convexHull_eq_union] at hx
  simp only [exists_prop, Set.mem_iUnion] at hx
  obtain ⟨t, ht₁, ht₂, ht₃⟩ := hx
  simp only [t.convexHull_eq, exists_prop, Set.mem_setOf_eq] at ht₃
  obtain ⟨w, hw₁, hw₂, hw₃⟩ := ht₃
  let t' := t.filter fun i => w i ≠ 0
  refine' ⟨t', t'.fintypeCoeSort, ((↑) : t' → E), w ∘ ((↑) : t' → E), _, _, _, _, _⟩
  · rw [Subtype.range_coe_subtype]
    exact Subset.trans (Finset.filter_subset _ t) ht₁
  · exact ht₂.comp_embedding ⟨_, inclusion_injective (Finset.filter_subset (fun i => w i ≠ 0) t)⟩
  · exact fun i =>
      (hw₁ _ (Finset.mem_filter.mp i.2).1).lt_of_ne (Finset.mem_filter.mp i.property).2.symm
  · erw [Finset.sum_attach, Finset.sum_filter_ne_zero, hw₂]
  · change (∑ i : t' in t'.attach, (fun e => w e • e) ↑i) = x
    erw [Finset.sum_attach (f := fun e => w e • e), Finset.sum_filter_of_ne]
    · rw [t.centerMass_eq_of_sum_1 id hw₂] at hw₃
      exact hw₃
    · intro e _ hwe contra
      apply hwe
      rw [contra, zero_smul]
#align eq_pos_convex_span_of_mem_convex_hull eq_pos_convex_span_of_mem_convexHull
