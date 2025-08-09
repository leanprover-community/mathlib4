/-
Copyright (c) 2025 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/
import Mathlib.GroupTheory.GroupAction.SubMulAction
import Mathlib.GroupTheory.Perm.MaximalSubgroups
import Mathlib.GroupTheory.SpecificGroups.Alternating
/-! # Maximal subgroups of the alternating group

* `AlternatingGroup.isCoatom_stabilizer`:
if `s : Set α` is nonempty as well as its complement, and `Nat.card α ≠ 2 * s.ncard',
then `stabilizer (alternatingGroup α) s` is a maximal subgroup of `alternatingGroup α`.

This is the “intransitive case” of the O'Nan-Scott classification
of maximal subgroups of the alternating groups.

-/

open scoped Pointwise

open MulAction

variable {α : Type*} [Fintype α] [DecidableEq α]

namespace Equiv.Perm

omit [DecidableEq α] in
theorem ofSubtype_mem_stabilizer' (s : Set α) (g : Equiv.Perm (sᶜ : Set α))
    [DecidablePred fun x ↦ x ∈ sᶜ] :
    Equiv.Perm.ofSubtype g ∈ stabilizer (Equiv.Perm α) s := by
  classical
  rw [mem_stabilizer_set_iff_subset_smul_set s.toFinite]
  intro x hx
  rw [Set.mem_smul_set]
  use x, hx
  simp [Equiv.Perm.ofSubtype_apply_of_not_mem g (Set.notMem_compl_iff.mpr hx)]

end Equiv.Perm

namespace AlternatingGroup

theorem stabilizer.isPreprimitive (s : Set α) (hs : (sᶜ : Set α).Nontrivial) :
    IsPreprimitive (stabilizer (alternatingGroup α) s) s := by
  classical
  let φ : stabilizer (alternatingGroup α) s → Equiv.Perm s := MulAction.toPerm
  suffices hφ : Function.Surjective φ by
    let f : s →ₑ[φ] s := {
      toFun := id
      map_smul' := fun ⟨g, hg⟩ ⟨x, hx⟩ => by
        simp only [id, Equiv.Perm.smul_def]
        rw [toPerm_apply] }
    have hf : Function.Bijective f := Function.bijective_id
    rw [isPreprimitive_congr hφ hf]
    infer_instance
  -- function.surjective φ
  suffices ∃ k : Equiv.Perm (sᶜ : Set α), Equiv.Perm.sign k = -1 by
    obtain ⟨k, hk_sign⟩ := this
    have hks : Equiv.Perm.ofSubtype k • s = s := by
      rw [← mem_stabilizer_iff]
      exact Equiv.Perm.ofSubtype_mem_stabilizer' s k
    have hminus_one_ne_one : (-1 : Units ℤ) ≠ 1 := Ne.symm (units_ne_neg_self 1)
    intro g
    let g' := if Equiv.Perm.sign g = 1
      then Equiv.Perm.ofSubtype g
      else Equiv.Perm.ofSubtype g * Equiv.Perm.ofSubtype k
    use! g'
    rw [Equiv.Perm.mem_alternatingGroup]
    rcases Int.units_eq_one_or (Equiv.Perm.sign g) with hsg | hsg <;>
    · simp only [g', if_true, hminus_one_ne_one, if_false, Equiv.Perm.sign_ofSubtype,
      Equiv.Perm.sign_mul, mul_neg, mul_one, neg_neg, hsg, hk_sign]
    rw [mem_stabilizer_iff, Submonoid.mk_smul]
    rcases Int.units_eq_one_or (Equiv.Perm.sign g) with hsg | hsg
    · simp only [g', hsg, if_true]
      exact Equiv.Perm.ofSubtype_mem_stabilizer g
    · simp only [g', hsg, hminus_one_ne_one, if_false, mul_smul, hks]
      exact Equiv.Perm.ofSubtype_mem_stabilizer g
    dsimp only [id_eq, ite_true, ite_false, eq_mpr_eq_cast, cast_eq, φ]
    rcases Int.units_eq_one_or (Equiv.Perm.sign g) with hsg | hsg
    · simp only [g', hsg, if_true]
      ext x
      simp
    · simp only [g', hsg, hminus_one_ne_one, if_false]
      ext x
      simp only [toPerm_apply, SMul.smul_stabilizer_def]
      simp only [Subgroup.mk_smul, Equiv.Perm.smul_def, Equiv.Perm.coe_mul, Function.comp_apply]
      rw [Equiv.Perm.ofSubtype_apply_of_not_mem k _]
      exact Equiv.Perm.ofSubtype_apply_coe g x
      rw [Set.notMem_compl_iff]; exact x.prop
  -- ∃ k : equiv.perm (sᶜ : set α), equiv.perm.sign k = -1,
  obtain ⟨a, ha, b, hb, hab⟩ := hs
  use Equiv.swap ⟨a, ha⟩ ⟨b, hb⟩
  rw [Equiv.Perm.sign_swap _]
  simp [← Function.Injective.ne_iff Subtype.coe_injective, hab]

theorem stabilizer.isPreprimitive' (s : Set α) (hsc : sᶜ.Nontrivial)
    (G : Subgroup (Equiv.Perm α))
    (hG : stabilizer (Equiv.Perm α) s ⊓ alternatingGroup α ≤ G) :
    IsPreprimitive (stabilizer G s) s := by
  have _ := stabilizer.isPreprimitive s hsc
  let φ : stabilizer (alternatingGroup α) s → stabilizer G s := fun g => by
    use! (g : alternatingGroup α)
    apply hG
    rw [Subgroup.mem_inf]
    constructor
    · let h := g.prop; rw [mem_stabilizer_iff] at h ⊢; exact h
    · exact SetLike.coe_mem _
    exact g.prop
  let f : s →ₑ[φ] s :=
    { toFun := id
      map_smul' := fun ⟨⟨m, hm'⟩, hm⟩ ⟨a, ha⟩ => rfl }
  have hf : Function.Surjective f := Function.surjective_id
  exact IsPreprimitive.of_surjective hf

theorem isPretransitive_ofFixingSubgroup (s : Set α) (h0 : s.Nontrivial)
    (hα : Set.ncard s < Set.ncard (sᶜ : Set α)) :
    IsPretransitive (fixingSubgroup (alternatingGroup α) s)
      (SubMulAction.ofFixingSubgroup (alternatingGroup α) s) := by
  rw [← is_one_pretransitive_iff]
  apply SubMulAction.ofFixingSubgroup.isMultiplyPretransitive (Hn := ?_) (hmn := rfl)
  have _ := AlternatingGroup.isMultiplyPretransitive α
  apply isMultiplyPretransitive_of_le (n := Nat.card α - 2)
  · have h1' : 2 < Set.ncard (sᶜ : Set α) := by
      apply lt_of_le_of_lt _ hα
      rw [Nat.succ_le_iff, Set.one_lt_ncard]
      exact h0
    rw [add_comm, ← Set.ncard_add_ncard_compl s,
      Nat.add_sub_assoc (le_of_lt h1'), add_comm 1, add_le_add_iff_left]
    apply Nat.le_sub_of_add_le
    exact h1'
  · exact Nat.sub_le (Nat.card α) 2

theorem _root_.Equiv.Perm.swap_mul_swap_mem_alternatingGroup {α : Type*} [Fintype α] [DecidableEq α]
    {g g' : Equiv.Perm α} (hg : Equiv.Perm.IsSwap g) (hg' : Equiv.Perm.IsSwap g') :
    g * g' ∈ alternatingGroup α := by
  simp [Equiv.Perm.mem_alternatingGroup, map_mul, hg.sign_eq, hg'.sign_eq]

/-- If `s : Set α` is nonempty and its complement has at least two elements,
then `stabilizer (alternatingGroup α) s ≠ ⊤`. -/
theorem stabilizer_ne_top (s : Set α) (hs : s.Nonempty) (hsc : sᶜ.Nontrivial) :
    stabilizer (alternatingGroup α) s ≠ ⊤ := by
  obtain ⟨a, ha⟩ := hs
  obtain ⟨b, hb, c, hc, hbc⟩ := hsc
  rw [Set.mem_compl_iff] at hb hc
  have hac : a ≠ c := ne_of_mem_of_not_mem ha hc
  have hab : a ≠ b := ne_of_mem_of_not_mem ha hb
  intro h; apply hc
  let g := Equiv.swap a b * Equiv.swap a c
  suffices g • s = s by
    rw [← this]
    use a, ha
    dsimp [g]
    rw [Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne hac.symm hbc.symm]
  have hg : g ∈ alternatingGroup α := by
    rw [← Equiv.Perm.swap_isSwap_iff] at hab hac
    exact Equiv.Perm.swap_mul_swap_mem_alternatingGroup hab hac
  rw [← Subgroup.mk_smul g hg, ← MulAction.mem_stabilizer_iff, h]
  apply Subgroup.mem_top

/-- If `s : Set α` is nonempty, as well as its complement,
and one of `s`, `sᶜ` has at least two elements,
then `stabilizer (alternatingGroup α) s ≠ ⊤`. -/
theorem stabilizer_ne_top' (s : Set α) (hs : s.Nonempty) (hsc : sᶜ.Nonempty)
    (hssc : s.Nontrivial ∨ (sᶜ : Set α).Nontrivial) : stabilizer (alternatingGroup α) s ≠ ⊤ := by
  rcases hssc with hs' | hsc'
  · rw [← stabilizer_compl]
    rw [← compl_compl s] at hs'
    exact stabilizer_ne_top (sᶜ) hsc hs'
  exact stabilizer_ne_top s hs hsc'

-- Il va falloir, soit que t ait ≥ 3 éléments, soit que tᶜ en ait ≥ 2.
-- autrement dit : fintype.card α ≥ 4.
-- La condition est nécessaire :
-- dans le cas α = {1, 2, 3}, t = {1,2} ou t = {1}, le résultat est faux
theorem moves_in (hα : 4 ≤ Nat.card α) (t : Set α) :
    ∀ a ∈ t, ∀ b ∈ t, ∃ g ∈ stabilizer (Equiv.Perm α) t ⊓ alternatingGroup α, g • a = b := by
  intro a ha b hb
  by_cases hab : a = b
  · -- a = b, on prend g = 1,
    use 1
    simp only [hab, Subgroup.one_mem, one_smul, and_self]
  · rw [← Ne] at hab
    rcases le_or_gt (Set.ncard t) 2 with ht | ht'
    · -- fintype.card t ≤ 2, alors on prend le produit d'un swap (a b) avec un swap dans tᶜ
      have h : 1 < Set.ncard (tᶜ : Set α) := by
        by_contra h
        rw [← not_lt] at hα
        apply hα
        rw [← Set.ncard_add_ncard_compl t]
        grind
      rw [Set.one_lt_ncard_iff] at h
      obtain ⟨c, d, hc, hd, hcd⟩ := h
      simp only [Ne] at hcd
      use Equiv.swap a b * Equiv.swap c d
      constructor
      · simp only [Subgroup.mem_inf]
        constructor
        · rw [mem_stabilizer_set_iff_subset_smul_set t.toFinite, Set.subset_smul_set_iff]
          rintro _ ⟨x, hx, rfl⟩
          simp only [mul_inv_rev, Equiv.swap_inv, Equiv.Perm.smul_def, Equiv.Perm.coe_mul,
            Function.comp_apply]
          by_cases hxa : x = a
          · rwa [hxa, Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne]
            · apply ne_of_mem_of_not_mem hb hc
            · apply ne_of_mem_of_not_mem hb hd
          · by_cases hxb : x = b
            · rwa [hxb, Equiv.swap_apply_right, Equiv.swap_apply_of_ne_of_ne]
              · apply ne_of_mem_of_not_mem ha hc
              · apply ne_of_mem_of_not_mem ha hd
            · rwa [Equiv.swap_apply_of_ne_of_ne hxa hxb, Equiv.swap_apply_of_ne_of_ne]
              · apply ne_of_mem_of_not_mem hx hc
              · apply ne_of_mem_of_not_mem hx hd
        · simp only [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul]
          rw [Equiv.Perm.sign_swap hab]; rw [Equiv.Perm.sign_swap hcd]
          simp only [Int.units_mul_self]
      · simp only [Equiv.Perm.smul_def, Equiv.Perm.coe_mul, Function.comp_apply]
        rw [Set.mem_compl_iff t] at hc hd
        have hac : a ≠ c := by intro h; apply hc; rw [← h]; exact ha
        have had : a ≠ d := by intro h; apply hd; rw [← h]; exact ha
        rw [Equiv.swap_apply_of_ne_of_ne hac had]
        rw [Equiv.swap_apply_left]
    · -- fintype t ≥ 3, alors on prend un 3-cycle dans t
      suffices ∃ c ∈ t, c ≠ a ∧ c ≠ b by
        obtain ⟨c, hc, hca, hcb⟩ := this
        use Equiv.swap a c * Equiv.swap a b
        constructor
        · simp only [Subgroup.mem_inf]
          constructor
          · rw [mem_stabilizer_set_iff_subset_smul_set t.toFinite, Set.subset_smul_set_iff]
            rintro _ ⟨x, hx, rfl⟩
            · simp only [mul_inv_rev, Equiv.swap_inv, Equiv.Perm.smul_def, Equiv.Perm.coe_mul,
                Function.comp_apply]
              by_cases hxa : x = a
              · rwa [hxa, Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne hca hcb]
              · rw [← Ne] at hxa
                by_cases hxc : x = c
                · rwa [hxc, Equiv.swap_apply_right, Equiv.swap_apply_left]
                · rw [← Ne] at hxc
                  rw [Equiv.swap_apply_of_ne_of_ne hxa hxc]
                  by_cases hxc : x = b
                  · rw [hxc, Equiv.swap_apply_right]; exact ha
                  · rw [← Ne] at hxc
                    rw [Equiv.swap_apply_of_ne_of_ne hxa hxc]
                    exact hx
          · simp only [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul]
            rw [Equiv.Perm.sign_swap hab]; rw [Equiv.Perm.sign_swap (Ne.symm hca)]
            simp only [Int.units_mul_self]
        · simp only [Equiv.Perm.smul_def, Equiv.Perm.coe_mul, Function.comp_apply]
          rw [Equiv.swap_apply_left]
          rw [Equiv.swap_apply_of_ne_of_ne (Ne.symm hab) (Ne.symm hcb)]
      suffices (t \ {a, b}).Nonempty by
        obtain ⟨c, h⟩ := this
        simp only [Set.mem_diff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at h
        use c
  -- apply And.intro h.left
  -- exact h.right
      rw [Set.diff_nonempty]
      intro ht
      rw [← not_le] at ht'
      apply ht'
      convert Set.ncard_le_ncard ht
      rw [(Set.ncard_pair hab).symm]

theorem moves_in' (hα : 4 ≤ Nat.card α) (G : Subgroup (Equiv.Perm α)) (t : Set α)
    (hGt : stabilizer (Equiv.Perm α) t ⊓ alternatingGroup α ≤ G) :
    ∀ a ∈ t, ∀ b ∈ t, ∃ g : G, g • a = b := by
  intro a ha b hb
  obtain ⟨g, hg, H⟩ := moves_in hα t a ha b hb
  use! g, hGt hg, H

theorem has_three_cycle_of_stabilizer' (s : Set α) (hs : 2 < Set.ncard s) :
    ∃ g : Equiv.Perm α, g.IsThreeCycle ∧ g ∈ stabilizer (Equiv.Perm α) s := by
  rw [Set.two_lt_ncard_iff] at hs
  obtain ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩ := hs
  use Equiv.swap a b * Equiv.swap a c
  constructor
  · apply Equiv.Perm.isThreeCycle_swap_mul_swap_same hab hac hbc
  rw [← stabilizer_compl]
  rw [mem_stabilizer_set_iff_subset_smul_set sᶜ.toFinite, Set.subset_smul_set_iff]
  rintro _ ⟨x, hx, rfl⟩
  simp only [mul_inv_rev, Equiv.swap_inv, Equiv.Perm.smul_def, Equiv.Perm.coe_mul,
    Function.comp_apply, Set.mem_compl_iff]
  rw [Set.mem_compl_iff] at hx
  suffices h : ∀ u ∈ s, x ≠ u by
    rw [Equiv.swap_apply_of_ne_of_ne (h a ha) (h b hb)]
    rw [Equiv.swap_apply_of_ne_of_ne (h a ha) (h c hc)]
    exact hx
  grind  -- since x ∉ s, x ≠ u, for any u ∈ s

omit [DecidableEq α] in
theorem has_three_cycle_of_stabilizer [DecidableEq α] (s : Set α) (hα : 4 < Nat.card α) :
    ∃ g : Equiv.Perm α, g.IsThreeCycle ∧ g ∈ stabilizer (Equiv.Perm α) s := by
  rcases Nat.lt_or_ge 2 (Set.ncard s) with hs | hs
  · exact has_three_cycle_of_stabilizer' s hs
  · suffices hs' : _ by
      obtain ⟨g, hg, hg'⟩ := has_three_cycle_of_stabilizer' (sᶜ) hs'
      use g
      rw [stabilizer_compl] at hg'
      exact ⟨hg, hg'⟩
    rw [lt_iff_not_ge] at hα ⊢
    intro hs'
    apply hα
    rw [← Set.ncard_add_ncard_compl s]
    grind

theorem le_of_isPreprimitive (h4 : 4 < Nat.card α)
    (G : Subgroup (Equiv.Perm α)) [hG' : IsPreprimitive G α]
    {s : Set α}
    (hG : stabilizer (Equiv.Perm α) s ⊓ alternatingGroup α ≤ G) :
    alternatingGroup α ≤ G := by
  -- We need to prove that alternating_group α ≤ ⊤
  -- G contains a three_cycle
  obtain ⟨g, hg3, hg⟩ := has_three_cycle_of_stabilizer s h4
  -- By Jordan's theorem, it suffices to prove that G acts primitively
  apply jordan_three_cycle hG' hg3
  apply hG
  simp only [Subgroup.mem_inf, hg, true_and]
  exact Equiv.Perm.IsThreeCycle.mem_alternatingGroup hg3

theorem isPreprimitive_of_stabilizer_lt
    (h4 : 4 ≤ Nat.card α)
    {G : Subgroup (Equiv.Perm α)}
    {s : Set α} (h0 : s.Nontrivial) (h1 : sᶜ.Nontrivial)
    (hα : Set.ncard s < Set.ncard (sᶜ : Set α))
    (hG : stabilizer (Equiv.Perm α) s ⊓ alternatingGroup α < G ⊓ alternatingGroup α) :
    IsPreprimitive G α := by
      /- This will be ultimately be deleted, unless one
      can avoid proving transitivity first.
  -- G acts nontrivially
  have : fixedPoints G α ≠ .univ := by
    by_contra hG'
    rw [lt_iff_le_and_ne] at hG
    apply hG.2
    apply le_antisymm hG.1
    intro g hg
    simp only [Subgroup.mem_inf] at hg
    simp only [Subgroup.mem_inf, hg.2, and_true]
    simp only [mem_stabilizer_iff]
    conv_rhs => rw [← one_smul G s]
    apply Set.image_congr
    intro a ha
    simp only [Equiv.Perm.smul_def, OneMemClass.coe_one, one_smul]
    have ha' : a ∈ fixedPoints G α := by rw [hG']; trivial
    simp only [mem_fixedPoints, Subtype.forall, Subgroup.mk_smul, Equiv.Perm.smul_def] at ha'
    exact ha' g hg.1
  rw [Set.ne_univ_iff_exists_notMem] at this
  obtain ⟨a, ha⟩ := this
  -- apply IsPreprimitive.of_isTrivialBlock_of_notMem_fixedPoints ha -/
  -- G acts transitively
  have : IsPretransitive G α := by
    have hG' : stabilizer (Equiv.Perm α) s ⊓ alternatingGroup α ≤ G :=
      le_trans (le_of_lt hG) inf_le_left
    apply Equiv.Perm.IsPretransitive.of_partition G (s := s)
    · intro a ha b hb
      obtain ⟨g, hg, H⟩ := moves_in h4 s a ha b hb
      use! g, hG' hg, H
    · intro a ha b hb
      obtain ⟨g, hg, H⟩ := moves_in h4 (sᶜ) a ha b hb
      use! g, hG' (by rwa [stabilizer_compl] at hg), H
    · intro h
      apply (lt_iff_le_not_ge.mp hG).right
      rw [le_inf_iff]
      constructor
      · intro g
        rw [Subgroup.mem_inf, mem_stabilizer_iff]
        rintro ⟨hg, _⟩
        rw [← Subgroup.coe_mk G g hg]
        change (⟨g, hg⟩ : ↥G) • s = s
        rw [← mem_stabilizer_iff, h]
        exact Subgroup.mem_top _
      · exact inf_le_right
  apply IsPreprimitive.mk
  -- The proof needs 4 steps
  /- Step 1 : No block is equal to `sᶜ`
       This uses that `Nat.card s` < `Nat.card sᶜ`.
       In the equality case, `Nat.card s = Nat.card sᶜ`,
       it is possible that `B = sᶜ` is a block:
       in that case, `G` would be a wreath product,
       this is case (b) of the O'Nan-Scott classification
       of maximal subgroups of the alternating group. -/
  have hB_ne_sc (B : Set α) (hB : IsBlock G B) : ¬B = sᶜ := by
    intro hBsc
    obtain ⟨b, hb⟩ := h1.nonempty
    obtain ⟨a, ha⟩ := h0.nonempty
    obtain ⟨k, hk⟩ := exists_smul_eq G b a
    suffices B.ncard ≤ s.ncard by
      apply Nat.lt_irrefl B.ncard
      apply lt_of_le_of_lt this
      simp_rw [hBsc]; exact hα
    rw [← Set.ncard_smul_set k B]
    apply Set.ncard_le_ncard (ht := Set.toFinite s)
    rw [← Set.disjoint_compl_right_iff_subset, ← hBsc]
    apply isBlock_iff_disjoint_smul_of_ne.mp hB
    intro h
    apply Set.notMem_empty a
    rw [← Set.inter_compl_self s]
    constructor
    · exact ha
    · rwa [← hk, ← hBsc, ← h, Set.smul_mem_smul_set_iff, hBsc]

  -- Step 2 : A block contained in `sᶜ` is a subsingleton
  have hB_not_le_sc (B : Set α) (hB : IsBlock G B) (hBsc : B ⊆ sᶜ) :
      B.Subsingleton := by
    rw [← Subtype.image_preimage_of_val hBsc]
    apply Set.Subsingleton.image
    suffices IsTrivialBlock (Subtype.val ⁻¹' B : Set (sᶜ : Set α)) by
      apply Or.resolve_right this
      intro hB'
      apply hB_ne_sc B hB
      simp only [Set.preimage_eq_univ_iff, Subtype.range_coe_subtype] at hB'
      apply Set.Subset.antisymm hBsc hB'
    suffices IsPreprimitive (stabilizer G (sᶜ : Set α)) (sᶜ : Set α) by
      apply this.isTrivialBlock_of_isBlock
      let φ' : stabilizer G (sᶜ : Set α) → G := Subtype.val
      let f' : (sᶜ : Set α) →ₑ[φ'] α := {
        toFun := Subtype.val
        map_smul' := fun m x => by simp only [φ', SMul.smul_stabilizer_def] }
      exact hB.preimage f'
    apply stabilizer.isPreprimitive'
    · rw [compl_compl]; exact h0
    · rw [stabilizer_compl]
      convert le_trans (le_of_lt hG) inf_le_left

 -- Step 3 : A block contained in `s` is a subsingleton
  have hB_not_le_s (B : Set α) (hB : IsBlock G B) (hBs : B ⊆ s) :
      B.Subsingleton := by
    suffices IsTrivialBlock (Subtype.val ⁻¹' B : Set s) by
      rcases this with hB' | hB'
      · rw [← Subtype.image_preimage_of_val hBs]
        apply Set.Subsingleton.image
        exact hB'
      · have hBs' : B = s := by
          apply Set.Subset.antisymm hBs
          intro x hx
          suffices x = Subtype.val (⟨x, hx⟩ : s) by
            rw [this, ← Set.mem_preimage, hB']
            apply Set.mem_univ
          rfl
        have : ∃ g' ∈ G, g' • s ≠ s := by
          by_contra h
          push_neg at h
          apply ne_of_lt hG
          apply le_antisymm (le_of_lt hG)
          intro g' hg'
          rw [Subgroup.mem_inf] at hg' ⊢
          exact ⟨h g' hg'.left, hg'.right⟩
        obtain ⟨g', hg', hg's⟩ := this
        rcases isBlock_iff_smul_eq_or_disjoint.mp hB ⟨g', hg'⟩ with h | h
        · -- case g' • B = B : absurd, since B = s and choice of g'
          exfalso
          apply hg's; rw [← hBs']; exact h
        · -- case g' • B disjoint from B
          suffices (g' • B).Subsingleton by
            apply Set.subsingleton_of_image _ B this
            apply Function.Bijective.injective (MulAction.bijective _)
          apply hB_not_le_sc ((⟨g', hg'⟩ : G) • B) (hB.translate _)
          rw [← hBs']
          exact Disjoint.subset_compl_right h
    suffices IsPreprimitive (stabilizer G s) (s : Set α) by
      apply this.isTrivialBlock_of_isBlock
      let φ' : stabilizer G s → G := Subtype.val
      let f' : s →ₑ[φ'] α := {
        toFun := Subtype.val
        map_smul' := fun ⟨m, _⟩ x => by simp [φ'] }
      exact hB.preimage f'
    apply stabilizer.isPreprimitive' s h1
    convert le_trans (le_of_lt hG) inf_le_left
  intro B hB
  unfold IsTrivialBlock
  rw [or_iff_not_imp_left]
  intro hB'
  obtain ⟨a, ha, ha'⟩ := Set.not_subset_iff_exists_mem_notMem.mp
    fun h ↦ hB' ((hB_not_le_sc B hB) h)
  rw [Set.notMem_compl_iff] at ha'
  obtain ⟨b, hb, hb'⟩ := Set.not_subset_iff_exists_mem_notMem.mp
    fun h ↦ hB' ((hB_not_le_s B hB) h)
  rw [← Set.mem_compl_iff] at hb'
  have hsc_le_B : sᶜ ⊆ B := by
    intro x hx'
    suffices ∃ k : fixingSubgroup (alternatingGroup α) s, k • b = x by
      obtain ⟨⟨k, hk⟩, hkbx : k • b = x⟩ := this
      suffices k • B = B by
        rw [← hkbx, ← this, Set.smul_mem_smul_set_iff]
        exact hb
      suffices hk_mem : (k : Equiv.Perm α) ∈ G by
        apply isBlock_iff_smul_eq_of_nonempty.mp hB (g := ⟨k, hk_mem⟩)
        simp only [Subgroup.mk_smul]
        use a
        refine ⟨?_, ha⟩
        rw [mem_fixingSubgroup_iff] at hk
        rw [← hk a ha']
        exact Set.smul_mem_smul_set ha
      -- ↑k ∈ G
      apply le_trans (le_of_lt hG); exact inf_le_left
      rw [Subgroup.mem_inf]
      refine ⟨?_, k.prop⟩
      suffices hk' : k ∈ stabilizer (alternatingGroup α) s by
        simpa [mem_stabilizer_iff] using hk'
      exact MulAction.fixingSubgroup_le_stabilizer _ _ hk
    · -- ∃ (k : fixingSubgroup (alternatingGroup α) s), k • b = x,
      haveI : IsPretransitive (fixingSubgroup (alternatingGroup α) s)
          (SubMulAction.ofFixingSubgroup (alternatingGroup α) s) :=
        isPretransitive_ofFixingSubgroup s h0 hα
      obtain ⟨k, hk⟩ :=
        exists_smul_eq (fixingSubgroup (alternatingGroup α) s)
          (⟨b, hb'⟩ : SubMulAction.ofFixingSubgroup (alternatingGroup α) s) ⟨x, hx'⟩
      use k
      rw [← Subtype.coe_inj, SubMulAction.val_smul] at hk
      exact hk
  -- Conclusion of the proof : B = ⊤
  rw [Set.eq_univ_iff_forall]
  intro x
  obtain ⟨b, hb⟩ := h1.nonempty
  obtain ⟨⟨g, hg⟩, hgbx : g • b = x⟩ := exists_smul_eq G b x
  suffices g • B = B by
    rw [← hgbx, ← this, Set.smul_mem_smul_set_iff]
    exact hsc_le_B hb
  -- g • B = B,
  apply isBlock_iff_smul_eq_of_nonempty.mp hB (g := ⟨g, hg⟩)
  simp only [Subgroup.mk_smul]
  apply Set.ncard_pigeonhole
  -- card B + card (g • B) = card B + card B
  -- ... ≥ card sᶜ + card sᶜ
  -- ... > card s + card s ᶜ = card α
  rw [← Set.ncard_add_ncard_compl s]
  apply Nat.lt_of_lt_of_le
  · apply Nat.add_lt_add_right _ (Set.ncard (sᶜ : Set α))
    · use Set.ncard (sᶜ : Set α)
    · exact hα
  apply Nat.add_le_add
  · apply le_trans (Set.ncard_le_ncard hsc_le_B)
    apply le_of_eq
    rw [Set.ncard_smul_set]
  exact Set.ncard_le_ncard hsc_le_B

theorem isCoatom_stabilizer_of_ncard_lt_ncard_compl
    (s : Set α)
    (h0' : s.Nontrivial) (h1' : sᶜ.Nontrivial) (hs : Set.ncard s < Set.ncard (sᶜ : Set α)) :
    IsCoatom (stabilizer (alternatingGroup α) s) := by
  suffices hα : 4 < Nat.card α by
  -- h0 : s.nonempty, h1  : sᶜ.nonempty
  --  cases em(s.nontrivial) with h0' h0',
  -- We start with the case where s.nontrivial
    constructor
    · -- stabilizer (alternating_group α) s ≠ ⊤
      exact stabilizer_ne_top' s h0'.nonempty h1'.nonempty (Or.inl h0')
    · -- ∀ (G : subgroup (alternating_group α)), stabilizer (alternating_group α) s < b) → b = ⊤
      intro G' hG'
      suffices alternatingGroup α ≤ G'.map (alternatingGroup α).subtype by
        rw [eq_top_iff]; intro g _
        obtain ⟨g', hg', hgg'⟩ := this g.prop
        simp only [Subgroup.coe_subtype, SetLike.coe_eq_coe] at hgg'
        rw [← hgg']; exact hg'
      --   apply is_maximal_stab'_temp' s hα,
      apply le_of_isPreprimitive hα (s := s) (hG' := ?_)
      · rw [← Subgroup.subgroupOf_map_subtype, Subgroup.map_subtype_le_map_subtype]
        exact le_of_lt hG'
      · apply isPreprimitive_of_stabilizer_lt (le_of_lt hα) h0' h1' hs
        rw [lt_iff_le_not_ge]
        constructor
        · intro g
          simp only [Subgroup.mem_inf]
          rintro ⟨hg, hg'⟩
          refine ⟨?_, hg'⟩
          simp only [Subgroup.mem_map, Subgroup.coe_subtype]
          refine ⟨⟨g, hg'⟩, ?_, rfl⟩
          apply le_of_lt hG'
          simpa only [mem_stabilizer_iff] using hg
        · intro h
          rw [lt_iff_le_not_ge] at hG'
          apply hG'.right
          intro g' hg'
          rw [mem_stabilizer_iff]
          rw [Subgroup.smul_def, ← mem_stabilizer_iff]
          apply inf_le_left (α := Subgroup (Equiv.Perm α))
          apply h
          simp [g'.prop, hg']
  -- `4 < Nat.card α`
  have h0 : 2 ≤ Set.ncard s := by
    rw [Nat.succ_le_iff, Set.one_lt_ncard_iff]
    obtain ⟨a, ha, b, hb, h⟩ := h0'
    use a, b, ha, hb, h
  rw [← Set.ncard_add_ncard_compl s]
  grind

theorem isCoatom_stabilizer_singleton (h3 : 3 ≤ Nat.card α)
    {s : Set α} (h : s.Nonempty) (h1 : s.Subsingleton) :
    IsCoatom (stabilizer (alternatingGroup α) s) := by
  have _ : Nontrivial α := by
    rw [← Fintype.one_lt_card_iff_nontrivial, ← Nat.card_eq_fintype_card]
    grind
  obtain ⟨a, ha⟩ := h
  rw [Set.Subsingleton.eq_singleton_of_mem h1 ha, stabilizer_singleton]
  have : IsPreprimitive (alternatingGroup α) α :=
    AlternatingGroup.isPreprimitive_of_three_le_card α h3
  apply IsPreprimitive.isCoatom_stabilizer_of_isPreprimitive

/-- `stabilizer (alternating_group α) s` is a maximal subgroup of alternating_group α,
  provided s ≠ ⊥, s ≠ ⊤ and fintype.card α ≠ 2 * fintype.card ↥s) -/
theorem isCoatom_stabilizer {s : Set α}
    (h0 : s.Nonempty) (h1 : sᶜ.Nonempty) (hs : Nat.card α ≠ 2 * Set.ncard s) :
    IsCoatom (stabilizer (alternatingGroup α) s) := by
  have hα : 3 ≤ Nat.card α := by
    rw [← Set.ncard_add_ncard_compl s] at hs ⊢
    by_contra! h3
    rw [← Set.ncard_pos, ← Nat.succ_le_iff] at h0 h1
    grind
  by_cases h0' : Set.Nontrivial s
  · by_cases h1' : Set.Nontrivial sᶜ
    · rcases Nat.lt_trichotomy s.ncard sᶜ.ncard with hs' | hs'
      · exact isCoatom_stabilizer_of_ncard_lt_ncard_compl s h0' h1' hs'
      rcases hs' with hs' | hs'
      · exfalso; apply hs
        rw [← Set.ncard_add_ncard_compl s, ← hs', two_mul]
      · rw [← compl_compl s] at h0'
        rw [← stabilizer_compl]
        apply isCoatom_stabilizer_of_ncard_lt_ncard_compl sᶜ h1' h0'
        simpa
    · simp only [Set.not_nontrivial_iff] at h1'
      rw [← stabilizer_compl]
      exact isCoatom_stabilizer_singleton hα h1 h1'
  · simp only [Set.not_nontrivial_iff] at h0'
    exact isCoatom_stabilizer_singleton hα h0 h0'

end AlternatingGroup
