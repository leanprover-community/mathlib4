/-
Copyright (c) 2020 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying
-/
import Mathlib.Algebra.Group.Action.End
import Mathlib.GroupTheory.Subgroup.Center
import Mathlib.GroupTheory.Submonoid.Centralizer

/-!
# Centralizers of subgroups
-/

assert_not_exists MonoidWithZero

variable {G G' : Type*} [Group G] [Group G']

namespace Subgroup

variable {H K : Subgroup G}

/-- The `centralizer` of `s` is the subgroup of `g : G` commuting with every `h : s`. -/
@[to_additive
/-- The `centralizer` of `s` is the additive subgroup of `g : G` commuting with every `h : s`. -/]
def centralizer (s : Set G) : Subgroup G :=
  { Submonoid.centralizer s with
    carrier := Set.centralizer s
    inv_mem' := Set.inv_mem_centralizer }

@[to_additive]
theorem mem_centralizer_iff {g : G} {s : Set G} : g ∈ centralizer s ↔ ∀ h ∈ s, h * g = g * h :=
  Iff.rfl

@[to_additive]
theorem mem_centralizer_iff_commutator_eq_one {g : G} {s : Set G} :
    g ∈ centralizer s ↔ ∀ h ∈ s, h * g * h⁻¹ * g⁻¹ = 1 := by
  simp only [mem_centralizer_iff, mul_inv_eq_iff_eq_mul, one_mul]

@[to_additive]
lemma mem_centralizer_singleton_iff {g k : G} :
    k ∈ Subgroup.centralizer {g} ↔ k * g = g * k := by
  simp only [mem_centralizer_iff, Set.mem_singleton_iff, forall_eq]
  exact eq_comm

@[to_additive]
theorem centralizer_univ : centralizer Set.univ = center G :=
  SetLike.ext' (Set.centralizer_univ G)

@[to_additive]
theorem le_centralizer_iff : H ≤ centralizer K ↔ K ≤ centralizer H :=
  ⟨fun h x hx _y hy => (h hy x hx).symm, fun h x hx _y hy => (h hy x hx).symm⟩

@[to_additive]
theorem center_le_centralizer (s) : center G ≤ centralizer s :=
  Set.center_subset_centralizer s

@[to_additive]
theorem centralizer_le {s t : Set G} (h : s ⊆ t) : centralizer t ≤ centralizer s :=
  Submonoid.centralizer_le h

@[to_additive (attr := simp)]
theorem centralizer_eq_top_iff_subset {s : Set G} : centralizer s = ⊤ ↔ s ⊆ center G :=
  SetLike.ext'_iff.trans Set.centralizer_eq_top_iff_subset

@[to_additive]
theorem map_centralizer_le_centralizer_image (s : Set G) (f : G →* G') :
    (Subgroup.centralizer s).map f ≤ Subgroup.centralizer (f '' s) := by
  rintro - ⟨g, hg, rfl⟩ - ⟨h, hh, rfl⟩
  rw [← map_mul, ← map_mul, hg h hh]

@[to_additive]
instance normal_centralizer [H.Normal] : (centralizer H : Subgroup G).Normal where
  conj_mem g hg i h hh := by
    simpa [-mul_left_inj, -mul_right_inj, mul_assoc]
      using congr(i * $(hg _ <| ‹H.Normal›.conj_mem _ hh i⁻¹) * i⁻¹)

@[to_additive]
instance characteristic_centralizer [hH : H.Characteristic] :
    (centralizer (H : Set G)).Characteristic := by
  refine Subgroup.characteristic_iff_comap_le.mpr fun ϕ g hg h hh => ϕ.injective ?_
  rw [map_mul, map_mul]
  exact hg (ϕ h) (Subgroup.characteristic_iff_le_comap.mp hH ϕ hh)

@[to_additive]
theorem le_centralizer_iff_isMulCommutative : K ≤ centralizer K ↔ IsMulCommutative K :=
  ⟨fun h => ⟨⟨fun x y => Subtype.ext (h y.2 x x.2)⟩⟩,
    fun h x hx y hy => congr_arg Subtype.val (h.1.1 ⟨y, hy⟩ ⟨x, hx⟩)⟩

@[deprecated (since := "2025-04-09")] alias le_centralizer_iff_isCommutative :=
  le_centralizer_iff_isMulCommutative
@[deprecated (since := "2025-04-09")] alias _root_.AddSubgroup.le_centralizer_iff_isCommutative :=
  AddSubgroup.le_centralizer_iff_isAddCommutative

variable (H)

@[to_additive]
theorem le_centralizer [h : IsMulCommutative H] : H ≤ centralizer H :=
  le_centralizer_iff_isMulCommutative.mpr h

variable {H} in
@[to_additive]
lemma closure_le_centralizer_centralizer (s : Set G) :
    closure s ≤ centralizer (centralizer s) :=
  closure_le _ |>.mpr Set.subset_centralizer_centralizer

@[to_additive]
theorem centralizer_closure (s : Set G) : centralizer (closure s) = centralizer s :=
  le_antisymm (centralizer_le subset_closure)
    (le_centralizer_iff.mp (closure_le_centralizer_centralizer s))

@[to_additive]
theorem centralizer_eq_iInf (s : Set G) : centralizer s = ⨅ g ∈ s, centralizer {g} :=
  le_antisymm (le_iInf₂ fun g hg ↦ centralizer_le (Set.singleton_subset_iff.mpr hg)) fun x hx ↦ by
    simpa only [mem_iInf, mem_centralizer_singleton_iff, eq_comm (a := x * _)] using hx

@[to_additive]
theorem center_eq_iInf {s : Set G} (hs : closure s = ⊤) :
    center G = ⨅ g ∈ s, centralizer {g} := by
  rw [← centralizer_univ, ← coe_top, ← hs, centralizer_closure, centralizer_eq_iInf]

@[to_additive]
theorem center_eq_infi' {s : Set G} (hs : closure s = ⊤) :
    center G = ⨅ g : s, centralizer {(g : G)} := by
  rw [center_eq_iInf hs, ← iInf_subtype'']

/-- If all the elements of a set `s` commute, then `closure s` is a commutative group. -/
@[to_additive
/-- If all the elements of a set `s` commute, then `closure s` is an additive commutative group. -/]
abbrev closureCommGroupOfComm {k : Set G} (hcomm : ∀ x ∈ k, ∀ y ∈ k, x * y = y * x) :
    CommGroup (closure k) :=
  { (closure k).toGroup with
    mul_comm := fun ⟨_, h₁⟩ ⟨_, h₂⟩ ↦
      have := closure_le_centralizer_centralizer k
      Subtype.ext <| Set.centralizer_centralizer_comm_of_comm hcomm _ (this h₁) _ (this h₂) }

/-- The conjugation action of N(H) on H. -/
@[simps]
instance : MulDistribMulAction H.normalizer H where
  smul g h := ⟨g * h * g⁻¹, (g.2 h).mp h.2⟩
  one_smul g := by simp [HSMul.hSMul]
  mul_smul := by simp [HSMul.hSMul, mul_assoc]
  smul_one := by simp [HSMul.hSMul]
  smul_mul := by simp [HSMul.hSMul]

/-- The homomorphism N(H) → Aut(H) with kernel C(H). -/
@[simps!]
def normalizerMonoidHom : H.normalizer →* MulAut H :=
  MulDistribMulAction.toMulAut H.normalizer H

theorem normalizerMonoidHom_ker :
    H.normalizerMonoidHom.ker = (Subgroup.centralizer H).subgroupOf H.normalizer := by
  simp [Subgroup.ext_iff, DFunLike.ext_iff, Subtype.ext_iff,
    mem_subgroupOf, mem_centralizer_iff, eq_mul_inv_iff_mul_eq, eq_comm]

end Subgroup
