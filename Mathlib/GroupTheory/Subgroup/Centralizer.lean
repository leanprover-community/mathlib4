/-
Copyright (c) 2020 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying
-/
module

public import Mathlib.Algebra.Group.Action.End
public import Mathlib.Algebra.Group.Commutator
public import Mathlib.GroupTheory.Subgroup.Center
public import Mathlib.GroupTheory.Submonoid.Centralizer
import Mathlib.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike
import Mathlib.Tactic.Translate.ToAdditive
import Mathlib.Util.CompileInductive

/-!
# Centralizers of subgroups
-/

@[expose] public section

assert_not_exists MonoidWithZero

variable {G G' : Type*} [Group G] [Group G']

namespace Subgroup

variable {H K : Subgroup G}

/-- The `centralizer` of `s` is the subgroup of `g : G` commuting with every `h : s`. -/
@[to_additive
/-- The `centralizer` of `s` is the additive subgroup of `g : G` commuting with every `h : s`. -/]
def centralizer (s : Set G) : Subgroup G where
  __ := Submonoid.centralizer s
  inv_mem' := Set.inv_mem_centralizer

@[to_additive]
theorem mem_centralizer_iff {g : G} {s : Set G} : g ∈ centralizer s ↔ ∀ h ∈ s, h * g = g * h :=
  Iff.rfl

open scoped commutatorElement in
@[to_additive]
theorem mem_centralizer_iff_commutator_eq_one {g : G} {s : Set G} :
    g ∈ centralizer s ↔ ∀ h ∈ s, ⁅h, g⁆ = 1 := by
  simp only [commutatorElement_def, mem_centralizer_iff, mul_inv_eq_iff_eq_mul, one_mul]

open scoped commutatorElement in
@[to_additive]
theorem mem_centralizer_iff_commutator_eq_one' {g : G} {s : Set G} :
    g ∈ centralizer s ↔ ∀ h ∈ s, ⁅g, h⁆ = 1 := by
  refine forall₂_congr fun _ _ ↦ ?_
  rw [commutatorElement_def, mul_inv_eq_iff_eq_mul, mul_inv_eq_iff_eq_mul, one_mul, eq_comm]

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
  ⟨fun h ↦ ⟨⟨fun x y ↦ Subtype.ext <| h y.2 x x.2⟩⟩,
    fun _ x hx y hy ↦ congrArg Subtype.val <| mul_comm' ⟨y, hy⟩ ⟨x, hx⟩⟩

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
theorem isMulCommutative_closure {k : Set G} (hcomm : ∀ x ∈ k, ∀ y ∈ k, x * y = y * x) :
    IsMulCommutative (closure k) :=
  have := closure_le_centralizer_centralizer k
  .of_setLike_mul_comm fun _ h₁ _ h₂ ↦
    Set.centralizer_centralizer_comm_of_comm hcomm _ (this h₁) _ (this h₂)

open scoped IsMulCommutative in
/-- If all the elements of a set `s` commute, then `closure s` is a commutative group. -/
@[to_additive (attr := deprecated isMulCommutative_closure (since := "2026-03-10"))
/-- If all the elements of a set `s` commute, then `closure s` is an additive commutative group. -/]
abbrev closureCommGroupOfComm {k : Set G} (hcomm : ∀ x ∈ k, ∀ y ∈ k, x * y = y * x) :
    CommGroup (closure k) :=
  have := isMulCommutative_closure hcomm
  inferInstance

@[to_additive]
instance instIsMulCommutative_closure {S : Type*} [SetLike S G] [MulMemClass S G] (s : S)
    [IsMulCommutative s] : IsMulCommutative (closure (s : Set G)) :=
  isMulCommutative_closure fun _ h₁ _ h₂ => setLike_mul_comm h₁ h₂

@[to_additive]
theorem centralizer_le_normalizer (s : Set G) : centralizer s ≤ normalizer s := by
  refine fun g hg h ↦ ⟨fun hh ↦ ?_, fun hh ↦ ?_⟩
  · simpa [← hg h hh]
  · convert hh
    simpa using hg _ hh

@[to_additive]
instance normal_subgroupOf_centralizer_normalizer (s : Set G) :
    (centralizer s |>.subgroupOf <| normalizer s).Normal := by
  refine (Subgroup.normal_subgroupOf_iff <| centralizer_le_normalizer s).mpr fun c n hc hn ↦ ?_
  refine mem_centralizer_iff_commutator_eq_one'.mpr fun g hg ↦ ?_
  suffices n * (c * (n⁻¹ * g * n) * c⁻¹ * n⁻¹ * g⁻¹) = 1 by simpa [commutatorElement_def, mul_assoc]
  simp [← hc _ <| mem_set_normalizer_iff''.mp hn g |>.mp hg]

@[to_additive]
theorem normalizer_singleton (g : G) : normalizer {g} = centralizer {g} := by
  refine ext fun h ↦ ⟨?_, ?_⟩
  · rintro hh g rfl
    exact mul_eq_of_eq_mul_inv (hh g |>.mp rfl).symm
  · refine fun hh g ↦ ⟨?_, ?_⟩ <;> rintro rfl
    · exact (eq_mul_inv_of_mul_eq <| hh g rfl).symm
    · simpa using hh _ rfl

/-- The conjugation action of `N(H)` on `H`. -/
@[simps]
instance : MulDistribMulAction (normalizer H : Subgroup G) H where
  smul g h := ⟨g * h * g⁻¹, (g.2 h).mp h.2⟩
  one_smul g := by simp [HSMul.hSMul]
  mul_smul := by simp [HSMul.hSMul, mul_assoc]
  smul_one := by simp [HSMul.hSMul]
  smul_mul := by simp [HSMul.hSMul]

/-- The homomorphism `N(H) → Aut(H)` with kernel `C(H)`. -/
@[simps!]
def normalizerMonoidHom : normalizer (H : Set G) →* MulAut H :=
  MulDistribMulAction.toMulAut (normalizer H : Subgroup G) H

theorem normalizerMonoidHom_ker :
    H.normalizerMonoidHom.ker = (centralizer H).subgroupOf (normalizer H : Subgroup G) := by
  simp [Subgroup.ext_iff, DFunLike.ext_iff, Subtype.ext_iff,
    mem_subgroupOf, mem_centralizer_iff, eq_mul_inv_iff_mul_eq, eq_comm]

end Subgroup
