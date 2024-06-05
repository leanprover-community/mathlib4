import Mathlib.InformationTheory.Code.Linear.Mathieu.Hexads
-- import Mathlib.GroupTheory.GroupAction.Blocks

namespace SemilinearCodeAut

variable {γ K:Type*}[Field K] {σ: RingAut K} {Tₖ M Tₘ:Type*} {gdistₖ: Tₖ} {gdistₘ:Tₘ}
variable [Semiring γ] [CompleteLinearOrder γ]
  [CovariantClass γ γ (.+.) (.≤.)] [FunLike Tₖ K (K → γ)]
  [GPseudoMetricClass Tₖ K γ]


variable  [AddCommGroup M]
variable? [AddGNorm K γ gdistₖ] => [AddGNorm K γ gdistₖ]
variable? [AddGNorm M γ gdistₘ] => [FunLike Tₘ M (M → γ)] [GPseudoMetricClass Tₘ M γ]
  [AddGNorm M γ gdistₘ]

variable--? {s : Submodule K M} =>
  [Module K M] {s : Submodule K M}

variable--? [_LinearCode γ K gdistₖ gdistₘ sₘ] =>
  [Set.GMetric.IsDelone gdistₘ ↑s] [Nontrivial γ]
  [PosMulMono γ] [MulPosMono γ] [ZeroLEOneClass γ] [StrictModuleGNorm K K gdistₖ gdistₖ]
  [StrictModuleGNorm K M gdistₖ gdistₘ]


protected lemma map_neg (f  : SemilinearCodeAut K gdistₖ gdistₘ s) {m : M} :
  f (-m) = -(f m) := by
  rw [map_neg]


end SemilinearCodeAut

namespace GolayCode
-- lemma minrep_four_finset_card : minrep_four_finset.card = 1771 := by
--   apply le_antisymm
--   . sorry
--   sorry
open BigOperators Submodule.Quotient
-- #check weight_four_finset_card_eq_sum

lemma weight_four_finset_card_eq : weight_four_finset.card = 10626 := by
  dsimp [weight_four_finset]
  rw [finset_filter_card_weight_eq]
  decide

lemma minrep_four_finset_card_ge : 1771 ≤ minrep_four_finset.card := by
  letI := fun a b : Hexad_space => Classical.propDecidable (a = b)
  suffices 10626 ≤ 6 * minrep_four_finset.card by
    omega
  calc
    10626
    _ = weight_four_finset.card := by
      rw [weight_four_finset_card_eq]
    _ = ∑ y ∈ minrep_four_finset, (Finset.filter (fun x ↦ bar x = y) weight_four_finset).card := by
      rw [weight_four_finset_card_eq_sum]
    _ ≤ ∑ y ∈ minrep_four_finset, 6 := by
      apply Finset.sum_le_sum
      exact fun i _ ↦ card_fiber_le_6 i
    _ ≤ 6 * minrep_four_finset.card := by
      rw [mul_comm,Finset.sum_const_nat]
      simp only [implies_true]

lemma minrep_four_finset_card_eq : minrep_four_finset.card = 1771 := by
  apply le_antisymm
  . exact card_minrep_four_le
  . exact minrep_four_finset_card_ge

lemma card_fiber_eq_six :
    letI := fun a b : Hexad_space => Classical.propDecidable (a = b)
    ∀ y ∈ minrep_four_finset, (Finset.filter (fun x => bar x = y) weight_four_finset).card = 6 := by
  rw [← Finset.sum_eq_sum_iff_of_le]
  . rw [← weight_four_finset_card_eq_sum]
    rw [Finset.sum_const_nat]
    skip_goal
    skip_goal
    . exact 6
    . rw [weight_four_finset_card_eq]
      rw [minrep_four_finset_card_eq]
    . simp only [implies_true]
  . intro i _
    exact card_fiber_le_6 i


-- #synth FaithfulSMul (SemilinearCodeAut F4 trivdist hdist HexaCode) F_4_6
-- #synth DistribMulAction (SemilinearCodeAut F4 trivdist hdist HexaCode) HexaCode

/-
new goal: prove that (the image of)
- (Multiplicative ↥HexaCode ⋊[apply_aut] SemilinearCodeAut F4 trivdist hdist HexaCode)
(under apply_hexacode_semi) is the stabilizer of col 0
-/


-- #synth MulAction (SemilinearCodeAut (ZMod 2) trivdist hdist GolayCode) Hexad_space

section
variable {α : Type*} (β : Type*) (K : Type*) [Ring K]
  [AddCommGroup α]
  [Module K α]
  [Monoid β] [MulAction β α] (H : Submodule K α)


class MulAction.ModuleQuotientAction : Prop where
  neg_add_mem : ∀ (b : β), ∀ (a a' : α) , - a + a' ∈ H → - (b • a) + (b • a') ∈ H


variable [MulAction.ModuleQuotientAction β K H]

instance : MulAction β (α ⧸ H) where
  smul b := Quotient.map' (b • ·) fun a a' h => by
    apply QuotientAddGroup.leftRel_apply.mpr
    simp only [Submodule.mem_toAddSubgroup]
    apply MulAction.ModuleQuotientAction.neg_add_mem b
    apply QuotientAddGroup.leftRel_apply.mp h
  one_smul q := Quotient.inductionOn' q fun a => congr_arg Quotient.mk'' (one_smul β a)
  mul_smul b b' q := Quotient.inductionOn' q fun a => congr_arg Quotient.mk'' (mul_smul b b' a)

#synth SMul K (α ⧸ H)

lemma mk_smul_eq_smul_mk (b : β) (a : α) : (mk (b • a) : α ⧸ H) = b • (mk a : α ⧸ H) := by
  exact rfl

end

instance :
    MulAction.ModuleQuotientAction
      (SemilinearCodeAut (ZMod 2) trivdist hdist GolayCode)
      (ZMod 2)
      GolayCode where
  neg_add_mem := fun b a a' => by
    dsimp [SMul.smul]
    rw [← b.map_neg,← b.map_add]
    exact b.map_code

-- instance : MulAction (SemilinearCodeAut (ZMod 2) trivdist hdist GolayCode) Hexad_space := _

lemma hexacode_auts_is_stabilizer :
  apply_hexacode_semi.range = MulAction.stabilizer _ (mk (col 0) : Hexad_space) := sorry


abbrev Sextet := {a : Hexad_space // minrep_weight a = 4}

instance : MulAction (SemilinearCodeAut (ZMod 2) trivdist hdist GolayCode) Sextet where
  smul φ := fun a => ⟨φ • a.1, by
    obtain hz := a.2
    dsimp [minrep_weight] at hz ⊢
    rw [← minrep_in a]
    rw [← mk_smul_eq_smul_mk]
    suffices (φ • (minrep a)).weight = 4 by
      exact minrep_weight_four_of_weight_four this
    suffices addGNorm hdist (φ • (minrep a)) = 4 by
      rw [weight_eq_norm] at this
      rw [← @Nat.cast_eq_ofNat ℕ∞] at this
      rw [Nat.cast_inj] at this
      exact this
    dsimp [SMul.smul]
    rw [φ.map_addGNorm]
    rw [weight_eq_norm]
    rw [hz]
    decide⟩
  one_smul := fun a => by
    ext : 1
    dsimp [HSMul.hSMul]
    exact one_smul _ _
  mul_smul := fun x y a => by
    ext : 1
    dsimp [HSMul.hSMul]
    exact mul_smul _ _ _


open Pointwise

section
variable {G : Type*} [Group G] {α : Type*} [MulAction G α] [Fintype α] [Fintype G]
  [MulAction.IsPretransitive G α]

lemma orbit_set_eq_union_orbits (s : Set α) :
    ⋃ (g : G), g • s = ⋃ o ∈ MulAction.orbit G '' s, o := by
  ext a
  simp only [Set.mem_iUnion, Set.mem_image, Set.iUnion_exists, Set.biUnion_and',
    Set.iUnion_iUnion_eq_right, exists_prop]
  simp_rw [Set.mem_smul_set]
  constructor
  . rintro ⟨g,⟨a',ha',rfl⟩⟩
    use a', ha'
    exact MulAction.mem_orbit a' g
  . intro ⟨b,hb,hab⟩
    rw [MulAction.mem_orbit_iff] at hab
    obtain ⟨g,hg⟩ := hab
    use g, b

#check MulAction.isBlock



instance :
  MulAction.IsPretransitive (SemilinearCodeAut (ZMod 2) trivdist hdist GolayCode) Sextet := by
    sorry

#check apply_hexacode_semi_inj
