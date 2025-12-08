/-
Copyright (c) 2025 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/

module

public import Mathlib.LinearAlgebra.Transvections.Basic

public import Mathlib.LinearAlgebra.Dual.BaseChange
public import Mathlib.LinearAlgebra.SpecialLinearGroup
public import Mathlib.RingTheory.TensorProduct.IsBaseChangeHom
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.Data.ENat.Lattice
public import Mathlib.Algebra.Group.Pointwise.Set.ListOfFn
public import Mathlib.Algebra.Group.Pointwise.Set.Basic
public import Mathlib.LinearAlgebra.Projectivization.Action

public import Mathlib.Algebra.Module.Torsion.Free
public import Mathlib.GroupTheory.GroupAction.FixingSubgroup

import Mathlib.LinearAlgebra.Charpoly.BaseChange
import Mathlib.LinearAlgebra.DFinsupp
import Mathlib.LinearAlgebra.Dimension.DivisionRing

/-!
# Transvections generate the special linear group

-/

@[expose] public section

namespace SpecialLinearGroup

section generation

open Module.End Module

section

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

abbrev fixedSubmodule (e : SpecialLinearGroup R V) :
    Submodule R V :=
  eigenspace (e : End R V) (1 : R)

theorem mem_fixedSubmodule_iff {e : SpecialLinearGroup R V} {v : V} :
    v ∈ e.fixedSubmodule ↔ e v = v := by simp

theorem inf_fixedSubmodule_le_fixedSubmodule_mul (e f : SpecialLinearGroup R V) :
    e.fixedSubmodule ⊓ f.fixedSubmodule ≤ (e * f).fixedSubmodule := by
  intro; aesop

/-- An element of the special linear group is exceptional if
  it is a nontrivial homothety modulo the eigenspace for eigenvalue 1. -/
abbrev IsExceptional (e : SpecialLinearGroup R V) : Prop :=
  e ≠ 1 ∧ ∃ a : R, a ≠ 1 ∧ ∀ v, e v - a • v ∈ e.fixedSubmodule

open scoped Pointwise

theorem transvections_pow_mono :
    Monotone (fun n : ℕ ↦ (transvections R V) ^ n) := by
  apply Set.pow_right_monotone
  refine ⟨0, 0, by simp, ?_⟩
  rw [← Subtype.coe_inj, SpecialLinearGroup.coe_transvection,
    ← LinearEquiv.toLinearMap_inj, LinearEquiv.transvection.coe_toLinearMap]
  simp [LinearMap.transvection.of_right_eq_zero]

noncomputable def transvection_degree (e : SpecialLinearGroup R V) : ℕ∞ :=
  sInf (Nat.cast '' {n | e ∈ (transvections R V) ^ n })

lemma transvection_degree_eq_top_iff {e : SpecialLinearGroup R V} :
    transvection_degree e = ⊤ ↔ {n | e ∈ transvections R V ^ n} = ∅ := by
  simp [transvection_degree, Set.eq_empty_iff_forall_notMem]

theorem transvection_degree_one :
    transvection_degree (1 : SpecialLinearGroup R V) = 0 := by
  simp [transvection_degree, ENat.sInf_eq_zero]

theorem transvection_degree_le_iff {e : SpecialLinearGroup R V} {n : ℕ} :
    transvection_degree e ≤ n ↔ e ∈ (transvections R V) ^ n := by
  constructor
  · intro he
    have h : Set.Nonempty {n | e ∈ transvections R V ^ n} := by
      rw [Set.nonempty_iff_ne_empty]
      contrapose! he
      simp [transvection_degree, he]
    rw [transvection_degree, sInf_image, ← ENat.coe_sInf h, Nat.cast_le] at he
    exact transvections_pow_mono he (Nat.sInf_mem h)
  · intro he
    simp only [transvection_degree, sInf_le_iff, mem_lowerBounds, Set.mem_image, Set.mem_setOf_eq,
      forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
    intro b hb
    exact hb n he

end

open Pointwise

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Module.Finite K V]

example (e : V →ₗ[K] V) (W W' : Submodule K V) (he : W ≤ W'.comap e) :
    V ⧸ W →ₗ[K] V ⧸ W' :=
  W.liftQ (W'.mkQ ∘ₗ e) (fun v hv ↦ by simpa using he hv)

example (e : V →ₗ[K] V) (W W' : Submodule K V) (he : W.map e ≤ W') :
    V ⧸ W →ₗ[K] V ⧸ W' :=
  W.liftQ (W'.mkQ ∘ₗ e) (fun v hv ↦ by aesop)

example (e : V →ₗ[K] V) (W : Submodule K V) (he : W ≤ W.comap e) :
    V ⧸ W →ₗ[K] V ⧸ W :=
  W.mapQ W e he

example (e : V →ₗ[K] V) (W : Submodule K V) (he : W.map e ≤ W) :
    V ⧸ W →ₗ[K] V ⧸ W :=
  W.mapQ W e (Submodule.map_le_iff_le_comap.mp he)

example (e : V →ₗ[K] V) (W : Submodule K V) (he : W ≤ W.comap e) :
    W →ₗ[K] W := by
  exact e.restrict he

example (e : V ≃ₗ[K] V) (W W' : Submodule K V) (he : W = W'.comap e) :
    (V ⧸ W) ≃ₗ[K] (V ⧸ W') where
  toLinearMap := W.liftQ (W'.mkQ ∘ₗ e) (fun v hv ↦ by
    simpa [he] using hv)
  invFun := W'.liftQ (W.mkQ ∘ₗe.symm) (fun v hv ↦ by
    simpa [he] using hv)
  left_inv v' := by
    obtain ⟨v, rfl⟩ := W.mkQ_surjective v'
    simp
  right_inv v' := by
    obtain ⟨v, rfl⟩ := W'.mkQ_surjective v'
    simp

example (e : V ≃ₗ[K] V) (W W' : Submodule K V)
    (he : W = W'.comap e) :
    (V ⧸ W) ≃ₗ[K] (V ⧸ W') := by
  apply Submodule.Quotient.equiv W W' e
  erw [Submodule.map_equiv_eq_comap_symm e W]
  aesop

omit [Module.Finite K V] in
theorem map_eq_of_mem_fixingSubgroup
    (W : Submodule K V) (e : SpecialLinearGroup K V)
    (he : e ∈ fixingSubgroup _ W.carrier) :
    Submodule.map e.val W = W := by
  ext v
  simp [mem_fixingSubgroup_iff] at he
  refine ⟨fun ⟨w, hv, hv'⟩ ↦ ?_, fun hv ↦ ?_⟩
  · simp only [SetLike.mem_coe] at hv hv'
    rwa [← hv', he w hv]
  · refine ⟨v, hv, he v hv⟩

def mkQ (W : Submodule K V) :
    fixingSubgroup (SpecialLinearGroup K V) W.carrier →* SpecialLinearGroup K (V ⧸ W) where
  toFun := fun ⟨e, he⟩ ↦
    { val := Submodule.Quotient.equiv W W e (map_eq_of_mem_fixingSubgroup W e he)
      property := by
        simp only [Submodule.carrier_eq_coe, mem_fixingSubgroup_iff, SetLike.mem_coe,
          smul_def] at he
        rw [← Units.val_inj, LinearEquiv.coe_det, Units.val_one]
        set f := LinearMap.restrict e (p := W) (q := W)
          (fun v hv ↦ by aesop) with hf
        change LinearMap.det (W.mapQ W e (fun v hv ↦ by aesop)) = 1
        suffices f = LinearMap.id by
          have that := e.property
          rwa [← Units.val_inj, LinearEquiv.coe_det, Units.val_one,
            LinearMap.det_eq_det_mul_det W e (fun v hv ↦ by
              simpa [he v hv]),
            ← hf, this, LinearMap.det_id, one_mul] at that
        aesop }
  map_one' := by aesop
  map_mul' e f := by
    simp only
    ext v
    obtain ⟨w, rfl⟩ := W.mkQ_surjective v
    simp

/-- For `e : SpecialLinearGroup K V`, the element
of `SpecialLinearGroup K (V ⧸ e.fixedSubmodule) induced by `e`. -/
def reduce (e : SpecialLinearGroup K V) :
    SpecialLinearGroup K (V ⧸ e.fixedSubmodule) :=
  mkQ e.fixedSubmodule ⟨e, by simp [mem_fixingSubgroup_iff]⟩

theorem finrank_le_one_add_finrank_fixedSubmodule_of_mem_transvections
    {t : SpecialLinearGroup K V} (ht : t ∈ transvections K V) :
    finrank K V ≤ 1 + finrank K t.fixedSubmodule := by
  obtain ⟨f, v, hfv, ht⟩ := ht
  suffices LinearMap.ker f ≤ t.fixedSubmodule by
    replace this := Submodule.finrank_mono this
    rw [← Nat.add_le_add_iff_left (n := 1)] at this
    refine le_trans ?_ this
    rw [← (LinearMap.ker f).finrank_quotient_add_finrank,
        f.quotKerEquivRange.finrank_eq]
    simp only [add_le_add_iff_right]
    rw [← Module.finrank_self K]
    apply Submodule.finrank_le
  intro x hx
  simp only [LinearMap.mem_ker] at hx
  simp [ht, LinearMap.transvection.apply, hx]

theorem finrank_le_add_finrank_fixedSubmodule
    {n : ℕ} {e : SpecialLinearGroup K V} (he : e ∈ transvections K V ^ n) :
    finrank K V ≤ n + finrank K e.fixedSubmodule := by
  induction n generalizing e with
  | zero =>
    simp only [pow_zero, Set.mem_one] at he
    rw [zero_add]
    suffices e.fixedSubmodule = ⊤ by
      rw [this, finrank_top]
    aesop
  | succ n hind =>
    rw [pow_succ] at he
    obtain ⟨f, hf, t, ht, he⟩ := he
    simp only at he
    specialize hind hf
    replace ht := finrank_le_one_add_finrank_fixedSubmodule_of_mem_transvections ht
    have : finrank K (f.fixedSubmodule ⊓ t.fixedSubmodule : Submodule K V) ≤
      finrank K (fixedSubmodule e) := by
      apply Submodule.finrank_mono
      rw [← he]
      exact inf_fixedSubmodule_le_fixedSubmodule_mul f t
    have := Submodule.finrank_sup_add_finrank_inf_eq f.fixedSubmodule t.fixedSubmodule
    have := Submodule.finrank_le (f.fixedSubmodule ⊔ t.fixedSubmodule)
    linarith

theorem finrank_le_transvection_degree_add (e : SpecialLinearGroup K V) :
    finrank K V ≤ transvection_degree e + finrank K e.fixedSubmodule := by
  induction hn : transvection_degree e with
  | top => simp
  | coe n =>
    rw [← ENat.coe_add, ENat.coe_le_coe]
    apply finrank_le_add_finrank_fixedSubmodule
    rw [← transvection_degree_le_iff, hn]

theorem finrank_lt_transvection_degree_add_of_isExceptional
    (e : SpecialLinearGroup K V) (he : IsExceptional e) :
    finrank K V < transvection_degree e +
      finrank K (eigenspace (e : End K V) (1 : K)) := sorry

theorem _root_.Module.Basis.sumExtend_apply_left {ι K V : Type*}
    [DivisionRing K] [AddCommGroup V] [Module K V] {v : ι → V}
    (hs : LinearIndependent K v) (i : ι) :
    Module.Basis.sumExtend hs (Sum.inl i) = v i := by
  simp only [Basis.sumExtend, Equiv.trans_def, Basis.coe_reindex, Basis.coe_extend, Equiv.symm_symm,
    Equiv.coe_trans, Function.comp_apply]
  rfl

theorem exists_mem_transvections_apply_eq_of_indep {u v : V}
    (h : LinearIndependent K ![u, v]) :
    ∃ t ∈ transvections K V, v = t • u := by
  have : ∃ f : Dual K V, f (v - u) = 0 ∧ f u = 1 := by
    replace h : LinearIndepOn K ![u, v] ⊤ :=
      linearIndepOn_iff.mpr fun l a a_1 ↦ h a_1
    set ι := ↑(⊤ : Set (Fin 2)) ⊕ ↑(Basis.sumExtendIndex h)
    set b : Basis ι K V := Module.Basis.sumExtend h with hb
    let i : ι := Sum.inl (⟨0, Set.mem_univ 0⟩)
    let j : ι := Sum.inl (⟨1, Set.mem_univ 1⟩)
    have hi : b i = u := Module.Basis.sumExtend_apply_left h ⟨0, Set.mem_univ 0⟩
    have hj : b j = v := Basis.sumExtend_apply_left h ⟨1, Set.mem_univ 1⟩
    use b.coord i + b.coord j
    rw [← hi, ← hj]
    have hij : i ≠ j := by simp [ne_eq, i, j, Sum.inl_injective.eq_iff]
    simp [Finsupp.single_eq_of_ne hij, Finsupp.single_eq_of_ne' hij]
  obtain ⟨f, hvu, hx⟩ := this
  refine ⟨SpecialLinearGroup.transvection hvu, ⟨f, v - u, hvu, rfl⟩, ?_⟩
  simp [transvection, LinearMap.transvection.apply, hx]

theorem exists_mem_transvections_apply_eq_of_indep'
    {W : Submodule K V} {u v : V}
    (hu : u ∉ W) (hv : u ∉ W)
    (h : LinearIndependent K ![u, v]) :
    ∃ t ∈ transvections K V, t ∈ fixingSubgroup _ W.carrier ∧ v = t • u := by
  sorry /-
  have : ∃ f : Dual K V, W ≤ LinearMap.ker f ∧ f (v - u) = 0 ∧ f u = 1 := by
    replace h : LinearIndepOn K ![u, v] ⊤ :=
      linearIndepOn_iff.mpr fun l a a_1 ↦ h a_1
    set ι := ↑(⊤ : Set (Fin 2)) ⊕ ↑(Basis.sumExtendIndex h)
    set b : Basis ι K V := Module.Basis.sumExtend h with hb
    let i : ι := Sum.inl (⟨0, Set.mem_univ 0⟩)
    let j : ι := Sum.inl (⟨1, Set.mem_univ 1⟩)
    have hi : b i = u := Module.Basis.sumExtend_apply_left h ⟨0, Set.mem_univ 0⟩
    have hj : b j = v := Basis.sumExtend_apply_left h ⟨1, Set.mem_univ 1⟩
    use b.coord i + b.coord j
    rw [← hi, ← hj]
    have hij : i ≠ j := by simp [ne_eq, i, j, Sum.inl_injective.eq_iff]
    simp [Finsupp.single_eq_of_ne hij, Finsupp.single_eq_of_ne' hij]
  obtain ⟨f, hvu, hx⟩ := this
  refine ⟨SpecialLinearGroup.transvection hvu, ⟨f, v - u, hvu, rfl⟩, ?_⟩
  simp [transvection, LinearMap.transvection.apply, hx] -/

section

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]
    (W : Submodule R V)

theorem linearIndependent_sum (ι κ : Type*) (b : ι → W) (c : κ → V ⧸ W)
    (hb : LinearIndependent R b) (hc : LinearIndependent R c) :
    LinearIndependent R
      (Sum.elim (fun i ↦ (b i : V)) ((Function.surjInv W.mkQ_surjective) ∘ c)) := by
  rw [linearIndependent_iff]
  intro a ha
  set a' := Finsupp.sumFinsuppLEquivProdFinsupp R a with ha'
  rw [← LinearEquiv.symm_apply_eq] at ha'
  suffices a' = 0 by rw [← ha', this, map_zero]
  rw [Prod.ext_iff]
  simp only [Prod.fst_zero, Prod.snd_zero]
  rw [← ha'] at ha
  -- nonterminal simp
  simp [Finsupp.linearCombination_apply, Finsupp.sum_sumElim] at ha
  suffices a'.2 = 0 by
    simp only [this, and_true]
    rw [linearIndependent_iff] at hb
    specialize hb a'.1
    apply hb
    rw [Finsupp.linearCombination_apply]
    rwa [this, Finsupp.sum_zero_index, add_zero,
      Finsupp.sum_congr (g2 := (fun i a ↦ W.subtype (a • (b i)))) (by simp),
      ← map_finsuppSum, LinearMap.map_eq_zero_iff _ W.subtype_injective] at ha
  replace ha := LinearMap.congr_arg (f := W.mkQ) ha
  simp only [map_add] at ha
  suffices W.mkQ _ = 0 by
    rw [linearIndependent_iff] at hc
    specialize hc a'.2
    apply hc
    rw [Finsupp.linearCombination_apply]
    rwa [this, zero_add, map_finsuppSum, map_zero,
      Finsupp.sum_congr (g2 := fun k a ↦ a • (c k))] at ha
    intro k _
    simp [Function.surjInv_eq W.mkQ_surjective (c k)]
  rw [map_finsuppSum]
  convert Finsupp.sum_zero with i r
  simp only [Function.comp_apply, Sum.elim_inl, map_smul, Submodule.mkQ_apply]
  convert smul_zero _
  simp


variable [Module.Free R W]
    [Module.Free R (V ⧸ W)] [Module.Finite R V]
    (f : V →ₗ[R] V) (hfW : W ≤ W.comap f)

example (hfW : W ≤ W.comap f) : V ⧸ W →ₗ[R] V ⧸ W :=
  Submodule.mapQ W W f hfW

example (hfW : W ≤ W.comap f) : W →ₗ[R] W :=
  f.restrict hfW

#synth Module.Finite R (V ⧸ W)





noncomputable example (ι κ : Type*) (b : Basis ι R W) (c : Basis κ R (V ⧸ W)) :
    Basis (ι ⊕ κ) R V := by
  have : Function.Surjective W.mkQ := by
    exact Submodule.mkQ_surjective W
  let w : V ⧸ W → V := Function.invFun W.mkQ
  let v : (ι ⊕ κ) → V := Sum.elim (fun i ↦ b i) (fun k ↦ Function.invFun W.mkQ (c k))
  apply Basis.mk (v := v)
  · sorry
  · sorry


example : (V ⧸ W) →ₗ[R] V := by
  have := Module.Free.of_basis (Basis.ofShortExact hS' (Module.Free.chooseBasis R S.X₁)
    (Module.Free.chooseBasis R S.X₃))


example : f.det = (f.restrict hfW).det * (Submodule.mapQ W W f hfW).det := by
  sorry

end
example (W : Submodule K V) :
    fixingSubgroup (SpecialLinearGroup K V) W.carrier →* SpecialLinearGroup K (V ⧸ W) where
  toFun e := sorry
  map_mul' := sorry
  map_one' := sorry

example {ι : Type*} [Fintype ι] (v : ι → V) :
    Fintype.card ι = finrank K (Submodule.span K (Set.range v)) ↔
      LinearIndependent K v := by
  simp [linearIndependent_iff_card_eq_finrank_span, Set.finrank]

lemma linearIndependent_of_not_mem_span {x y z : V} (hx : x ≠ 0)
    (hz : z ∉ Submodule.span K {x, y}) :
    LinearIndependent K ![x, z] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  rw [and_comm]
  by_contra! h'
  apply hz
  by_cases ht : t = 0
  · exfalso
    apply h' ht
    simpa [ht, hx] using hst
  rw [Submodule.mem_span_insert]
  refine ⟨ -(s / t), 0, Submodule.zero_mem _, ?_⟩
  rw [add_zero, ← sub_eq_zero, neg_smul, sub_neg_eq_add,
    ← smul_eq_zero_iff_right ht, smul_add, smul_smul,
    add_comm, mul_div_cancel₀ s ht, hst]

theorem transvections_isPretransitive (h2 : 2 ≤ finrank K V) :
    MulAction.IsPretransitive (Subgroup.closure (transvections K V)) {v : V | v ≠ 0} where
  exists_smul_eq x y := by
    classical
    wlog h : LinearIndependent K ![x.val , y.val] with hyp
    · suffices ∃ z : V, z ∉ Submodule.span K {x.val, y.val} by
        obtain ⟨z, hz⟩ := this
        have hz0 : z ≠ 0 := fun h ↦ hz <| by
          rw [h]
          exact zero_mem _
        have hxz : LinearIndependent K ![x.val, z] := by
          exact linearIndependent_of_not_mem_span x.prop hz
        have hzy : LinearIndependent K ![z, y.val] := by
          rw [LinearIndependent.pair_symm_iff]
          apply linearIndependent_of_not_mem_span y.prop (y := x.val)
          convert hz using 3
          grind
        obtain ⟨g, hg⟩ := hyp h2 x ⟨z, hz0⟩ hxz
        obtain ⟨h, hh⟩ := hyp h2 ⟨z, hz0⟩ y hzy
        use h * g
        simp [mul_smul, hg, hh]
      suffices Submodule.span K {x.val, y.val} ≠ ⊤ by
        by_contra! hz
        apply this
        rw [eq_top_iff]
        exact fun z _ ↦ hz z
      intro h'
      have : Set.finrank K {x.val, y.val} < 2 := by
        apply Nat.lt_of_le_of_ne _ ?_
        · rw [← Finset.coe_pair]
          exact le_trans (finrank_span_finset_le_card _) Finset.card_le_two
        rw [eq_comm]
        simpa [linearIndependent_iff_card_eq_finrank_span, Set.pair_comm] using h
      rw [← not_le] at this
      apply this
      simp only [Set.finrank]
      rwa [h', finrank_top]
    obtain ⟨g, hg, hgxy⟩ := exists_mem_transvections_apply_eq_of_indep h
    use ⟨g, Subgroup.subset_closure hg⟩
    simp only [Subgroup.smul_def, ne_eq, Set.coe_setOf]
    rw [smul_eq_iff g x y, hgxy]

example (W : Submodule K V) :
    Set (fixingSubgroup (SpecialLinearGroup K V) W.carrier) := by
  exact (fixingSubgroup  _ _).subtype ⁻¹' (transvections K V)

open scoped Set.Notation in
theorem transvections_isPretransitive_fixingSubgroup
    (W : Submodule K V) (h2 : 2 ≤ finrank K V) :
    MulAction.IsPretransitive
      (Subgroup.closure
        ((fixingSubgroup (SpecialLinearGroup K V) W.carrier).subtype ⁻¹' (transvections K V)))
      {v : V | v ∉ W} where
  exists_smul_eq := by
    rintro ⟨x, hx⟩ ⟨y, hy⟩
    simp only [Set.mem_setOf_eq] at hx hy
    classical
    wlog h : LinearIndependent K ![x , y] with hyp
    · suffices ∃ z : V, z ∉ W ⊔ Submodule.span K {x, y} by
        obtain ⟨z, hz⟩ := this
        have hz0 : z ≠ 0 := fun h ↦ hz <| by
          rw [h]
          exact zero_mem _
        have hxz : LinearIndependent K ![x, z] := by
          sorry -- exact linearIndependent_of_not_mem_span hx hz
        have hzy : LinearIndependent K ![z, y] := by
          rw [LinearIndependent.pair_symm_iff]
          sorry -- apply linearIndependent_of_not_mem_span hy (y := x)
          convert hz using 3
          grind
        obtain ⟨g, hg⟩ := hyp W h2 x hx z hz0 hxz
        obtain ⟨h, hh⟩ := hyp h2 ⟨z, hz0⟩ y hzy
        use h * g
        simp [mul_smul, hg, hh]
      suffices Submodule.span K {x.val, y.val} ≠ ⊤ by
        by_contra! hz
        apply this
        rw [eq_top_iff]
        exact fun z _ ↦ hz z
      intro h'
      have : Set.finrank K {x.val, y.val} < 2 := by
        apply Nat.lt_of_le_of_ne _ ?_
        · rw [← Finset.coe_pair]
          exact le_trans (finrank_span_finset_le_card _) Finset.card_le_two
        rw [eq_comm]
        simpa [linearIndependent_iff_card_eq_finrank_span, Set.pair_comm] using h
      rw [← not_le] at this
      apply this
      simp only [Set.finrank]
      rwa [h', finrank_top]
    obtain ⟨g, hg, hgxy⟩ := exists_mem_transvections_apply_eq_of_indep h
    use ⟨g, Subgroup.subset_closure hg⟩
    simp only [Subgroup.smul_def, ne_eq, Set.coe_setOf]
    rw [smul_eq_iff g x y, hgxy]

theorem closure_transvection [Module.Finite K V] :
    Subgroup.closure (transvections K V) = ⊤ := by
  rw [eq_top_iff]
  nontriviality V
  wlog h2 : 2 ≤ Module.finrank K V
  · suffices Subsingleton (SpecialLinearGroup K V) by simp
    rw [not_le, Nat.lt_succ_iff] at h2
    apply subsingleton_of_finrank_eq_one
    apply le_antisymm h2
    rwa [Nat.add_one_le_iff, finrank_pos_iff]
  suffices ∀ (n : ℕ) (e : SpecialLinearGroup K V)
    (hn : n = finrank K (eigenspace (e : End K V) (1 : K))),
      e ∈ Subgroup.closure (transvections K V) by
    intro e _
    apply this _ e rfl
  intro n
  induction n using Nat.strong_decreasing_induction with
  | base =>
    use finrank K V
    intro m hm e he
    rw [gt_iff_lt, he, ← not_le] at hm
    exact hm.elim (Submodule.finrank_le _)
  | step n hind=>
    intro e he
    set W := eigenspace (e : End K V) (1 : K) with hW
    by_cases H : W = ⊤
    · suffices e = 1 by
        rw [this]; exact one_mem _
      ext v
      change (e : End K V) v = v
      conv_rhs => rw [← one_smul K v]
      rw [← mem_eigenspace_iff, ← hW, H]
      exact Submodule.mem_top
    · obtain ⟨v, hv⟩ := SetLike.exists_not_mem_of_ne_top W H rfl
      have hv' := hv
      rw [hW, mem_eigenspace_iff, one_smul] at hv'
      have H' : finrank K W < finrank K V - 1 := sorry
      -- e' = t f u ∘ e
      -- f = 0 sur W, f u = 0
      -- e' v = (t f u) (e v) = e v + f (e v) • u = v
      -- u = v - e v, f (e v) = f (v) = 1
      have := transvections_isPretransitive h2
      have := this.exists_smul_eq
        ⟨(e : End K V) v, fun h ↦ hv' <| by rw [h, eq_comm];simpa using h⟩
        ⟨v, fun h ↦ hv' <| by rw [h, map_zero]⟩
      obtain ⟨⟨t, ht⟩, htv⟩ := this
      set e' := t * e with he'
      rw [← inv_mul_eq_iff_eq_mul] at he'
      rw [← he']
      apply Subgroup.mul_mem _ (Subgroup.inv_mem _ ht)
      apply hind _ _ e' rfl
      set W' := W ⊔ Submodule.span K {(e : End K V) v - v} with hW'
      rw [gt_iff_lt, he]
      apply Submodule.finrank_lt_finrank_of_lt
      rw [lt_iff_le_and_ne]
      constructor


      have hv' : v ∉ W' := fun h ↦ by
        rw [hW', Submodule.mem_sup] at h
        obtain ⟨w, hw, z, hz, hwz⟩ := h
        simp [Submodule.mem_span_singleton] at hz
        obtain ⟨a, rfl⟩ := hz
        have ha : a ≠ 0 := fun h ↦ by
          apply hv
          rwa [← hwz, h, zero_smul, add_zero]
        sorry
      sorry

end generation

end SpecialLinearGroup

section

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]
    {W : Submodule R V} {m n : Type*}
    (bW : Basis m R W) (bQ : Basis n R (V ⧸ W))

/-- Given a basis `bW` of a submodule of an `R`-module `V`,
and a basis `bQ` of the quotient `V ⧸ W`,
this is a basis of `V` combining `bW` and a lift of `bQ`. -/
noncomputable def basisSum :
    Basis (m ⊕ n) R V := by
  let b : m ⊕ n → V := Sum.elim (fun i ↦ bW i) ((Function.surjInv W.mkQ_surjective) ∘ bQ)
  have bl : b ∘ Sum.inl = W.subtype ∘ bW := rfl
  have br : W.mkQ ∘ b ∘ Sum.inr = bQ := by
    ext j
    simp only [Function.comp_apply, b, Sum.elim_inr, Function.comp_apply]
    rw [Function.rightInverse_surjInv W.mkQ_surjective]
  apply Basis.mk (v := b)
  · apply  LinearIndependent.sumElim_of_quotient
    · exact bW.linearIndependent
    · convert bQ.linearIndependent
  · intro x _
    simp only [b, Set.Sum.elim_range, Submodule.span_union]
    have := bW.span_eq
    rw [show Set.range (fun i ↦ (bW i : V)) =
      W.subtype '' (Set.range (fun i ↦ bW i)) from by aesop]
    rw [← Submodule.map_span, bW.span_eq, Submodule.map_top, Submodule.range_subtype]
    generalize_proofs hQ
    suffices W.mkQ x ∈ Submodule.map W.mkQ
      (Submodule.span R (Set.range (Function.surjInv hQ ∘ ⇑bQ))) by
      obtain ⟨y, hy, hxy⟩ := this
      rw [eq_comm, ← sub_eq_zero, ← map_sub, ← LinearMap.mem_ker, W.ker_mkQ] at hxy
      rw [← sub_add_cancel x y]
      exact add_mem (Submodule.mem_sup_left hxy) (Submodule.mem_sup_right hy)
    rw [Submodule.map_span, ← Set.range_comp]
    convert Submodule.mem_top
    rw [← bQ.span_eq]
    congr 2

@[simp]
theorem basisSum_inl (i : m) :
    basisSum bW bQ (Sum.inl i) = bW i := by
  simp [basisSum]

@[simp]
theorem basisSum_inr (j : n) :
    W.mkQ (basisSum bW bQ (Sum.inr j)) = bQ j := by
  simp only [basisSum, Basis.coe_mk, Function.comp_apply, Sum.elim_inr, Function.comp_apply]
  rw [Function.rightInverse_surjInv W.mkQ_surjective]

theorem basisSum_repr_left (i : m) :
    (basisSum bW bQ).repr (bW i) = Finsupp.single (Sum.inl i) 1 := by
  rw [← Module.Basis.apply_eq_iff, basisSum_inl]

@[simp]
theorem basisSum_repr_inl_of_mem (v : V) (hv : v ∈ W) (i : m) :
    (basisSum bW bQ).repr v (Sum.inl i) = bW.repr ⟨v, hv⟩ i := by
  suffices ∀ w : W,
    (basisSum bW bQ).repr (W.subtype w) (Sum.inl i) = bW.repr w i by
    exact this ⟨v, hv⟩
  classical
  intro w
  simp only [← Module.Basis.coord_apply]
  rw [← LinearMap.comp_apply]
  revert w
  rw [← LinearMap.ext_iff]
  apply bW.ext
  intro j
  simp [basisSum_repr_left, Finsupp.single_apply]

@[simp]
theorem basisSum_repr_inr_of_mem (v : V) (hv : v ∈ W) (j : n) :
    (basisSum bW bQ).repr v (Sum.inr j) = 0 := by
  classical
  suffices ∀ w : W,
    (basisSum bW bQ).repr (W.subtype w) (Sum.inr j) = 0 by
    exact this ⟨v, hv⟩
  intro w
  simp only [← Module.Basis.coord_apply]
  rw [← LinearMap.comp_apply]
  rw [← LinearMap.zero_apply (σ₁₂ := RingHom.id R) w]
  revert w
  rw [← LinearMap.ext_iff]
  apply bW.ext
  intro i
  simp [basisSum_repr_left]

@[simp]
theorem basisSum_repr_inr (v : V) (j : n) :
    (basisSum bW bQ).repr v (Sum.inr j) = bQ.repr (W.mkQ v) j := by
  simp only [← Module.Basis.coord_apply]
  rw [← LinearMap.comp_apply]
  revert v
  rw [← LinearMap.ext_iff]
  apply (basisSum bW bQ).ext
  intro x
  induction x with
  | inl i =>
    simp [basisSum_inl, LinearMap.comp_apply,
      show W.mkQ (bW i) = 0 from by
      rw [← LinearMap.mem_ker, Submodule.ker_mkQ]
      exact Submodule.coe_mem (bW i)]
  | inr i =>
    classical
    rw [LinearMap.comp_apply, basisSum_inr]
    simp [Finsupp.single_apply]

theorem LinearMap.det_eq_det_mul_det [Module.Finite R V]
    (W : Submodule R V) [Module.Free R W] [Module.Finite R W] [Module.Free R (V ⧸ W)]
    (e : V →ₗ[R] V) (he : W ≤ W.comap e) :
    e.det = (e.restrict he).det * (W.mapQ W e he).det := by
  let m := Module.Free.ChooseBasisIndex R W
  let bW : Basis m R W := Module.Free.chooseBasis R W
  let n := Module.Free.ChooseBasisIndex R (V ⧸ W)
  let bQ : Basis n R (V ⧸ W) := Module.Free.chooseBasis R (V ⧸ W)
  let b := basisSum bW bQ
  let A : Matrix m m R := LinearMap.toMatrix bW bW (e.restrict he)
  let B : Matrix m n R := Matrix.of fun i l ↦
    ((basisSum bW bQ).repr (e ((basisSum bW bQ) (Sum.inr l)))) (Sum.inl i)
  let D : Matrix n n R := LinearMap.toMatrix bQ bQ (W.mapQ W e he)
  suffices LinearMap.toMatrix b b e = Matrix.fromBlocks A B 0 D by
    rw [← LinearMap.det_toMatrix b, this, ← LinearMap.det_toMatrix bW,
      ← LinearMap.det_toMatrix bQ, Matrix.det_fromBlocks_zero₂₁]
  ext u v
  cases u with
  | inl i =>
    cases v with
    | inl k =>
      simp only [b, basisSum_inl, Matrix.fromBlocks_apply₁₁, A, LinearMap.toMatrix_apply]
      apply basisSum_repr_inl_of_mem
    | inr l => simp [b, LinearMap.toMatrix_apply, Matrix.fromBlocks_apply₁₂, B]
  | inr j =>
    cases v with
    | inl k =>
      suffices W.mkQ (e (bW k)) = 0 by simp [LinearMap.toMatrix_apply, b, this]
      rw [← LinearMap.mem_ker, Submodule.ker_mkQ]
      exact he (Submodule.coe_mem (bW k))
    | inr l =>
      simp only [LinearMap.toMatrix_apply, basisSum_repr_inr,
        Matrix.fromBlocks_apply₂₂, b, D]
      rw [Submodule.mkQ_apply, ← W.mapQ_apply , ← Submodule.mkQ_apply, basisSum_inr]

end


#exit

