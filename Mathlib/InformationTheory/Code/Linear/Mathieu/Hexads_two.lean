import Mathlib.InformationTheory.Code.Linear.Mathieu.Hexads
import Mathlib.GroupTheory.GroupAction.Blocks
import Mathlib.Data.Set.Card
import Mathlib.Topology.Algebra.InfiniteSum.Defs


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



abbrev Sextet := {a : Hexad_space // minrep_weight a = 4}

lemma sextet_card_eq : Fintype.card Sextet = 1771 := by
  rw [← minrep_four_finset_card_eq]
  dsimp only [Sextet,minrep_four_finset]
  rw [Fintype.card_subtype]


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
variable {G : Type*} [Group G] {α : Type*} [MulAction G α]
  [MulAction.IsPretransitive G α] [Fintype α]

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

def card_translate_eq_card (s : Set α) (g : G) : Set.encard s = Set.encard (g • s) := by
  apply Set.encard_congr
  exact {
    toFun := fun ⟨x,hx⟩ => ⟨g • x, by
      rw [Set.mem_smul_set]
      use x⟩
    invFun := fun ⟨x,hx⟩ => ⟨g⁻¹ • x, by
      rw [Set.mem_smul_set] at hx
      obtain ⟨y,hy,rfl⟩ := hx
      simp only [inv_smul_smul]
      exact hy⟩
    left_inv := fun x => by simp only [inv_smul_smul, Subtype.coe_eta]
    right_inv := fun y => by simp only [smul_inv_smul, Subtype.coe_eta]
  }

lemma block_eq_union_stabilizer_orbits {s : Set α} (hs : MulAction.IsBlock G s)
    {a : α} (ha : a ∈ s) : s = ⋃ b ∈ s, MulAction.orbit (MulAction.stabilizer G a) b := by
  ext c
  simp only [Set.mem_iUnion, exists_prop]
  constructor
  . intro hc
    use c, hc
    simp only [MulAction.mem_orbit_self, and_true]
  . rintro ⟨d,hd,⟨⟨g,hg⟩,rfl⟩⟩
    simp only [Submonoid.mk_smul]
    have : g • a ∈ s := by
      rw [hg]
      exact ha
    have : g • s = s := by
      apply hs.def_mem ha this
    rw [← this]
    simp only [Set.smul_mem_smul_set_iff]
    exact hd


lemma card_block_eq_sum_card_stabilizer_orbits [DecidableEq α] {s : Set α} (hs : MulAction.IsBlock G s)
    {a : α}
    [Fintype ↑((fun x ↦ MulAction.orbit (↥(MulAction.stabilizer G a)) x) '' s)]
    (ha : a ∈ s) :Set.ncard s =
    ∑ O ∈ ((MulAction.orbit (MulAction.stabilizer G a) .) '' s : Set (Set α)), Set.ncard O := by
  letI hsetfin : ∀ s' : Set α, Fintype s' := by exact fun s' ↦ Fintype.ofFinite ↑s'
  calc s.ncard
    = s.toFinset.card := by
        rw [Set.ncard_eq_toFinset_card']
  _ = (⋃ b ∈ s, MulAction.orbit (MulAction.stabilizer G a) b).toFinset.card := by
    rw [Set.toFinset_congr]
    exact block_eq_union_stabilizer_orbits hs ha
  _ = ((MulAction.orbit (MulAction.stabilizer G a) '' s).toFinset.biUnion (fun b => b.toFinset)).card := by
    congr
    ext i
    simp only [Set.mem_toFinset, Set.mem_iUnion, exists_prop, Finset.mem_biUnion, Set.mem_image,
      exists_exists_and_eq_and]
  _ = ∑ u ∈ (MulAction.orbit ↥(MulAction.stabilizer G a) '' s).toFinset, u.toFinset.card := by
    rw [Finset.card_biUnion]
    . intro a ha b hb
      simp only [ne_eq, Set.disjoint_toFinset]
      simp only [Set.mem_toFinset, Set.mem_image] at ha hb
      obtain ⟨x,_,rfl⟩ := ha
      obtain ⟨y,_,rfl⟩ := hb
      intro hne
      obtain h|h := (@MulAction.orbit.eq_or_disjoint (MulAction.stabilizer G a)) x y
      . contradiction
      . exact h
  _ = ∑ O ∈ (MulAction.orbit ↥(MulAction.stabilizer G a) '' s).toFinset, O.ncard := by
    congr
    ext o
    rw [Set.ncard_eq_toFinset_card']

abbrev rep1_val := col 0

abbrev rep1_val_weight : rep1_val.weight = 4 := by
  decide

abbrev rep1 : Sextet := ⟨(mk rep1_val : Hexad_space), by
  exact minrep_weight_four_of_weight_four rep1_val_weight⟩

abbrev rep2_val := to_gc !![1,1,0,0,0,0;1,1,0,0,0,0;0,0,0,0,0,0;0,0,0,0,0,0]
lemma rep2_val_weight : rep2_val.weight = 4 := by decide

abbrev rep2 : Sextet := ⟨(mk rep2_val : Hexad_space), by
  exact minrep_weight_four_of_weight_four rep2_val_weight⟩

abbrev rep3_val := to_gc !![0,1,0,0,0,0;1,0,0,0,0,0;1,0,0,0,0,0;1,0,0,0,0,0]
lemma rep3_val_weight : rep3_val.weight = 4 := by decide

abbrev rep3 : Sextet := ⟨(mk rep3_val : Hexad_space), by
  exact minrep_weight_four_of_weight_four rep3_val_weight⟩

abbrev rep4_val := to_gc !![1,1,1,0,0,0;1,0,0,0,0,0;0,0,0,0,0,0;0,0,0,0,0,0]
lemma rep4_val_weight : rep4_val.weight = 4 := by decide

abbrev rep4 : Sextet := ⟨(mk rep4_val : Hexad_space), by
  exact minrep_weight_four_of_weight_four rep4_val_weight⟩

lemma hexacode_auts_is_stabilizer :
  apply_hexacode_semi.range = MulAction.stabilizer _ rep1 := sorry

abbrev golay_aut := SemilinearCodeAut (ZMod 2) trivdist hdist GolayCode

abbrev orbit1 := MulAction.orbit (MulAction.stabilizer golay_aut rep1) rep1

lemma rep1_orbit_eq_singleton : orbit1 = {rep1} := by
  ext z
  simp only [Set.mem_singleton_iff]
  rw [MulAction.mem_orbit_iff]
  simp only [Subtype.exists, Submonoid.mk_smul, MulAction.mem_stabilizer_iff, exists_prop]
  constructor
  . rintro ⟨g,hg,rfl⟩
    exact hg
  . rintro rfl
    use 1
    simp only [one_smul, and_self]

lemma card_orbit1_eq : orbit1.ncard = 1 := by
  rw [rep1_orbit_eq_singleton]
  exact Set.ncard_singleton rep1

abbrev orbit2 := MulAction.orbit (MulAction.stabilizer golay_aut rep1) rep2

lemma card_orbit2_eq : orbit2.ncard = 90 := by sorry

abbrev orbit3 := MulAction.orbit (MulAction.stabilizer golay_aut rep1) rep3

lemma card_orbit3_eq : orbit3.ncard = 240 := by sorry

abbrev orbit4 := MulAction.orbit (MulAction.stabilizer golay_aut rep1) rep4

lemma card_orbit4_eq : orbit4.ncard = 1440 := by sorry

lemma orbit1_disjoint_orbit2 : Disjoint orbit1 orbit2 := by
  obtain h|h := (@MulAction.orbit.eq_or_disjoint (MulAction.stabilizer golay_aut rep1)) rep1 rep2
  . rw [MulAction.orbit_eq_iff] at h
    rw [MulAction.mem_orbit_iff] at h
    obtain ⟨⟨g,hg⟩,hg'⟩ := h
    dsimp [rep1,rep2] at hg hg'
    simp_rw [HSMul.hSMul, SMul.smul] at hg'
    simp only [Subtype.mk.injEq] at hg'

    sorry
  . exact h


lemma card_union_orbits_eq : (orbit1 ∪ orbit2 ∪ orbit3 ∪ orbit4).ncard = 1771 := by
  rw [Set.ncard_union_eq]
  rw [card_orbit4_eq]
  rw [Set.ncard_union_eq]
  rw [card_orbit3_eq]
  rw [Set.ncard_union_eq]
  rw [card_orbit2_eq,card_orbit1_eq]
  . sorry
  . sorry
  . sorry


example : Fintype.card ((Finset.univ : Finset α) :Set α) = Fintype.card α := by
  simp only [Finset.coe_univ]
  exact (set_fintype_card_eq_univ_iff Set.univ).mpr rfl

abbrev Sextet.mk' (x:golay_code_space') (hx : x.weight = 4) : Sextet := ⟨(mk x), by
  exact minrep_weight_four_of_weight_four hx⟩

lemma smul_map_weight {φ : golay_aut} {x : golay_code_space'}:
    (φ • x).weight = x.weight := by
  rw [← (@Nat.cast_inj ℕ∞)]
  simp_rw [← weight_eq_norm]
  dsimp [SMul.smul]
  rw [φ.map_addGNorm x]

lemma Sextet.smul_mk' (φ : golay_aut) {x:golay_code_space'} (hx : x.weight = 4) (hxsmul : (φ • x).weight = 4):
  Sextet.mk' (φ • x) (hxsmul) = φ • Sextet.mk' x hx := by
    rfl

lemma Set.ncard_eq_fintype_card {α : Type*} (s : Set α) [Fintype s] :
    s.ncard = Fintype.card s := by
  rw [Set.ncard_eq_toFinset_card']
  simp_rw [Fintype.card]
  rw [Finset.card_bij]
  . exact fun a ha => ⟨a,by
      simp only [Set.mem_toFinset] at ha
      exact ha⟩
  . exact fun a ha => by
      simp only [Finset.mem_univ]
  . exact fun a ha b hb => by
      simp only [Subtype.mk.injEq, imp_self]
  . exact fun ⟨a,ha⟩ => by
      simp only [Finset.mem_univ, Subtype.mk.injEq, Set.mem_toFinset, exists_prop, exists_eq_right,
        true_implies]
      exact ha

lemma orbits_total : orbit1 ∪ orbit2 ∪ orbit3 ∪ orbit4 = ⊤ := by
  letI : ∀ s : Set Sextet, Fintype s := by exact fun s ↦ Fintype.ofFinite ↑s
  apply Set.eq_of_subset_of_card_le
  . exact fun _ _ => trivial
  . rw [(set_fintype_card_eq_univ_iff ⊤).mpr rfl]
    calc
      Fintype.card Sextet
       = 1771 := by
        rw [sextet_card_eq]
      _ ≤ Fintype.card ↑(orbit1 ∪ orbit2 ∪ orbit3 ∪ orbit4) := by
        rw [← card_union_orbits_eq]
        apply Eq.le
        rw [Set.ncard_eq_fintype_card]
