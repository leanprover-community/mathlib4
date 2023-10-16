import Mathlib.GroupTheory.Subgroup.Basic
import Mathlib.Topology.Category.TopCat.Basic
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Basic
import Mathlib.GroupTheory.Coset
import Mathlib.GroupTheory.Subgroup.Basic
import Mathlib.GroupTheory.Index
import Mathlib.Data.Setoid.Partition

section CompactQuotient

open Function Set

lemma QuotientGroup.preimage_mk_singleton_mk {G : Type*} [Group G] (H : Subgroup G) (g : G) :
    mk (s := H) ⁻¹' {mk g} = (g * ·) '' H := by
  ext g'
  simp only [mem_preimage, mem_singleton_iff, QuotientGroup.eq, image_mul_left, SetLike.mem_coe]
  rw [← H.inv_mem_iff]
  simp

variable {G : Type*} [Group G] [TopologicalSpace G] [TopologicalGroup G] (U : Subgroup G)

lemma Subgroup.discreteTopology  (U_open : IsOpen (U : Set G)) : DiscreteTopology (G ⧸ U) := by
  apply singletons_open_iff_discrete.mp
  rintro ⟨g⟩
  erw [isOpen_mk, QuotientGroup.preimage_mk_singleton_mk]
  exact Homeomorph.mulLeft g |>.isOpen_image|>.mpr U_open

lemma Subgroup.finite_quotient [CompactSpace G] (U_open : IsOpen (U : Set G)) : Finite (G ⧸ U) :=
  have : CompactSpace (G ⧸ U) := Quotient.compactSpace
  have : DiscreteTopology (G ⧸ U) := U.discreteTopology U_open
  finite_of_compact_of_discrete

end CompactQuotient

section ConjAction

universe u

variable {G : Type u} [Group G]

open ConjAct

instance : MulAction (ConjAct G) (Subgroup G) := Subgroup.pointwiseMulAction

lemma intersectionOfConjugatesIsNormal (H : Subgroup G) :
    (⨅ (g : ConjAct G), g • H).Normal := by
  constructor
  intro n hn g
  simp only [Subgroup.mem_iInf] at *
  intro k
  obtain ⟨h, h_in_H : h ∈ H, hh : ((toConjAct g)⁻¹ * k) • h = n⟩ := hn _
  exists h
  simp only [MulDistribMulAction.toMonoidEnd_apply, MulDistribMulAction.toMonoidHom_apply]
  rw [←hh, smul_def, smul_def]
  simp only [map_mul, map_inv, ofConjAct_toConjAct, mul_inv_rev, inv_inv]
  group
  exact And.intro h_in_H trivial

lemma conjActionOrbitSubgroup_def (H : Subgroup G) :
    ⨅ (g : ConjAct G), g • H = ⨅ C ∈ MulAction.orbit (ConjAct G) H, C := by
  ext
  simp [Subgroup.pointwise_smul_def, MulAction.mem_orbit_iff, Subgroup.mem_iInf]

lemma stabilizer_eq_normalizer (H : Subgroup G) : MulAction.stabilizer (ConjAct G) H = H.normalizer := by
  ext
  erw [MulAction.mem_stabilizer_iff, ←eq_inv_smul_iff, Subgroup.mem_normalizer_iff, SetLike.ext_iff]
  simp only [Subgroup.mem_inv_pointwise_smul_iff]
  rfl

lemma subgroup_stabilizes_itself (H : Subgroup G) : H ≤ MulAction.stabilizer (ConjAct G) H := by
  rw [stabilizer_eq_normalizer]
  exact Subgroup.le_normalizer

lemma QuotientGroup.finite_of_le {H K : Subgroup G} (le : H ≤ K) (fh : Finite (G ⧸ H)) : Finite (G ⧸ K) := by
  apply Nat.finite_of_card_ne_zero
  intro (n_0 : K.index = 0)
  have := Subgroup.index_dvd_of_le le
  simp_all only [zero_dvd_iff, Subgroup.index_ne_zero_of_finite]

lemma Subgroup.finiteConjugationOrbit_of_finiteIndex (H : Subgroup G) (hf : H.index ≠ 0)
    : Finite (MulAction.orbit (ConjAct G) H) := by
  rw [Equiv.finite_iff <| MulAction.orbitEquivQuotientStabilizer (ConjAct G) H]
  exact QuotientGroup.finite_of_le (subgroup_stabilizes_itself H) (Nat.finite_of_card_ne_zero hf)

end ConjAction

section ContConjAction

universe u

variable {G : Type u} [Group G] [TopologicalSpace G] [TopologicalGroup G]

open ConjAct

lemma conjOpen_ofOpen (U : Subgroup G) (U_open : IsOpen (U : Set G)) (g : ConjAct G)
    : IsOpen (g • U : Set G) := by
  apply (Homeomorph.isOpen_image
    (Homeomorph.trans (Homeomorph.mulLeft (ofConjAct g)) (Homeomorph.mulRight (ofConjAct g)⁻¹))).mpr
  assumption

end ContConjAction

section TopGroups

universe u

variable {G : Type u} [Group G]

def subGroup_in_set (U : Set G) (one_mem : 1 ∈ U) : Subgroup G :=
  let V := { v | (· * v) '' U ⊆ U }
  let H := { h ∈ V | h⁻¹ ∈ V }
  have : 1 ∈ V := by simp [Eq.subset rfl]
  {
    carrier := H
    mul_mem' := by
      suffices ∀ a b : G, a ∈ V → b ∈ V → a * b ∈ V
        by intro x y ⟨x_in_V, x_in_V_inv⟩ ⟨y_in_V, y_in_V_inv⟩
           constructor
           exact this x y x_in_V y_in_V
           simp only [mul_inv_rev]
           exact this y⁻¹ x⁻¹ y_in_V_inv x_in_V_inv
      intro a b ha hb z ⟨u, u_in_U, hu⟩
      simp only [←hu, ←mul_assoc]
      apply hb
      simp only [Set.image_mul_right]
      apply ha
      simpa
    one_mem' := by aesop
    inv_mem' := by aesop
  }

lemma subGroup_in_set_in_U (U : Set G) (one_mem : 1 ∈ U) : (subGroup_in_set U one_mem : Set G) ⊆ U := by
  intro h ⟨h_in_V, _⟩
  rw [←one_mul h]
  exact h_in_V (Set.mem_image_of_mem (· * h) one_mem)

variable [TopologicalSpace G] [TopologicalGroup G]

lemma subGroup_in_set_open_of_compact (U : Set G) (one_mem : 1 ∈ U) (U_open : IsOpen U)
    (U_compact : IsCompact U) : IsOpen (subGroup_in_set U one_mem : Set G) := by
  let V := { v | (· * v) '' U ⊆ U }
  suffices IsOpen V by exact IsOpen.inter this (IsOpen.inv this)
  apply isOpen_iff_forall_mem_open.mpr
  intro v hv
  let m : G × G → G := fun ⟨g₁, g₂⟩ => g₁ * g₂
  let r (u : U) : Set G × Set G → Prop := fun ⟨U_u, V_u⟩ ↦
    (u : G) ∈ U_u ∧ v ∈ V_u ∧ IsOpen U_u ∧ IsOpen V_u ∧ (U_u ×ˢ V_u) ⊆ m⁻¹' U
  have hU (u : U) : ∃ s, r u s := by
    have ⟨(U_u : Set G), (V_u : Set G), U_u_open, V_u_closed, u_in_U_u, v_in_V_u, hm⟩ :
        ∃ U_u V_u, IsOpen U_u ∧ IsOpen V_u ∧ (u : G) ∈ U_u ∧ v ∈ V_u ∧ (U_u ×ˢ V_u) ⊆ m⁻¹' U := by
      apply isOpen_prod_iff.mp
      . exact IsOpen.preimage continuous_mul U_open
      . apply hv; simp
    exists (U_u, V_u)
  obtain ⟨f, hf⟩ := Classical.axiomOfChoice hU
  let cov (u : U) : Set G := (f u).1
  obtain ⟨t, ht⟩ := by
    apply IsCompact.elim_finite_subcover U_compact cov
    . aesop
    . intro u u_in_U
      simp only [Set.mem_iUnion]
      exists ⟨u, u_in_U⟩
      simp_all only [Subtype.forall]
  let V' := ⋂ u ∈ t, (f u).2
  have : IsOpen V' := by
    apply isOpen_biInter_finset
    intro u _
    have ⟨_, _, _, V_u_open, _⟩ := hf u
    assumption
  have : v ∈ V' := by simp_all only [Set.mem_iInter, implies_true]
  have : V' ⊆ V := by
    intro v' v'_in_V' _ ⟨u, u_in_U, hu⟩
    have : u ∈ ⋃ i ∈ t, cov i := ht u_in_U
    simp only [Set.mem_iUnion, Set.mem_iInter, ←hu] at *
    obtain ⟨i, (i_in_t : i ∈ t), (u_in_i : u ∈ (f i).1)⟩ := bex_def.mp this
    let ⟨_, _, _, _, hm⟩ := hf i
    exact hm (Set.mk_mem_prod u_in_i (v'_in_V' i i_in_t))
  exists V'

end TopGroups

section CompactGroups

universe u

variable {G : Type u} [Group G] [TopologicalSpace G] [TopologicalGroup G] [CompactSpace G]

lemma clopenContainsOpenSubgroup (U : Set G) (U_clopen : IsClopen U) (one_mem : 1 ∈ U) :
    ∃ H : Subgroup G, IsOpen (H : Set G) ∧ (H : Set G) ⊆ U := by
  exists (subGroup_in_set U one_mem)
  constructor
  exact subGroup_in_set_open_of_compact U one_mem U_clopen.left (IsClosed.isCompact U_clopen.right)
  exact subGroup_in_set_in_U U one_mem

lemma openSubgroupFiniteConjActOrbit (U : Subgroup G) (u_open : IsOpen (U : Set G))
    : (MulAction.orbit (ConjAct G) U).Finite := by
  have : Finite (MulAction.orbit (ConjAct G) U) := by
    apply Subgroup.finiteConjugationOrbit_of_finiteIndex
    have : Finite (G ⧸ U) := Subgroup.finite_quotient U u_open
    exact Subgroup.index_ne_zero_of_finite
  exact Set.toFinite _

lemma openSubgroupContainsNormal (U : Subgroup G) (u_open : IsOpen (U : Set G)) 
    : ∃ N : Subgroup G, IsOpen (N : Set G) ∧ N.Normal ∧ N ≤ U := by
  exists ⨅ (g : ConjAct G), g • U
  constructor
  . simp only [conjActionOrbitSubgroup_def, Subgroup.coe_iInf]
    apply Set.Finite.isOpen_biInter
    exact openSubgroupFiniteConjActOrbit U u_open
    intro H ⟨g, (hH : g • U = H)⟩
    rw [←hH]
    exact conjOpen_ofOpen U u_open g
  . constructor
    . exact intersectionOfConjugatesIsNormal U
    . have := iInf_le (fun g : ConjAct G => g • U) (1 : ConjAct G)
      simp only [one_smul] at this
      assumption

end CompactGroups

section Profinite

universe u

variable {G : Type u} [Group G] [TopologicalSpace G] [TopologicalGroup G]
  [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]

lemma openNhdOneContainsNormal (U : Set G) (U_open : IsOpen U) (one_mem : 1 ∈ U) :
    ∃ V : Subgroup G, IsOpen (V : Set G) ∧ V.Normal ∧ (V : Set G) ⊆ U := by
  obtain ⟨U', U'_clopen, one_in_U', U'_in_U⟩ := compact_exists_clopen_in_open U_open one_mem
  obtain ⟨H, H_open, H_in_U'⟩ := clopenContainsOpenSubgroup U' U'_clopen one_in_U'
  obtain ⟨N, N_open, N_normal, N_in_H⟩ := openSubgroupContainsNormal H H_open
  have : (N : Set G) ⊆ U
  repeat (trans; assumption; try trivial)
  exists N

theorem profiniteOpenNormalNhdsBasis : Filter.HasBasis (nhds (1 : G))
    (fun s : Subgroup G ↦ IsOpen (s : Set G) ∧ s.Normal)
    (fun s ↦ s) := by
  simp only [Filter.hasBasis_iff, mem_nhds_iff]
  intro U
  constructor
  . intro ⟨t, t_in_U, t_open, one_in_t⟩
    obtain ⟨V, V_open, V_normal, V_in_t⟩ := openNhdOneContainsNormal t t_open one_in_t
    have : (V : Set G) ⊆ U
    trans
    repeat assumption
    exists V
  . intro ⟨s, ⟨s_open, _⟩, s_in_U⟩
    exists s
    repeat (constructor; assumption)
    exact Subgroup.one_mem s

end Profinite
