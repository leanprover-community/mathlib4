/-
Copyright (c) 2024 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/

import Mathlib.RingTheory.GradedAlgebra.Noetherian
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Algebra.HilbertSerre.AdditiveFunction
import Mathlib.Algebra.Category.FGModuleCat.Abelian

/-!
# Hilbert Serre Theorem

-/

universe u
variable {A M : Type u}
variable [CommRing A] [AddCommGroup M] [Module A M]
variable [finite_module : Module.Finite A M] [noetherian_ring : IsNoetherianRing A]
variable (𝒜 : ℕ → AddSubgroup A) [GradedRing 𝒜]
variable (ℳ : ℕ → AddSubgroup M) [SetLike.GradedSMul 𝒜 ℳ] [DirectSum.Decomposition ℳ]

open GradedRing.finite_algebra_over_degree_zero_subring
open GradedModule.finite_module_over_degree_zero_subring
open CategoryTheory.Limits
open BigOperators
open PowerSeries


variable (μ : (FGModuleCat (𝒜 0)) ⟹+ ℤ)

namespace AdditiveFunction

def poincareSeries : ℤ⟦X⟧ :=
PowerSeries.mk fun n ↦ μ <| .of _ <| (ℳ n : Type u)

lemma map_subsingleton (x : FGModuleCat (𝒜 0)) [subsingleton : Subsingleton x] : μ x = 0 :=
  μ.eq_of_iso (IsZero.iso
    { unique_to := fun y ↦ ⟨⟨⟨0⟩, fun l ↦ LinearMap.ext fun a : x ↦ by
        simp only [show a = 0 from Subsingleton.elim _ _, _root_.map_zero]⟩⟩
      unique_from := fun y ↦ ⟨⟨⟨0⟩, fun l ↦ LinearMap.ext fun a : y ↦
        Subsingleton.elim (α := x) _ _⟩⟩ } <| isZero_zero _)
  |>.trans μ.map_zero

end AdditiveFunction

namespace GradedRing.HomogeneousGeneratingSetOf

variable (S : GradedRing.HomogeneousGeneratingSetOf 𝒜 (HomogeneousIdeal.irrelevant 𝒜).toIdeal)

variable {𝒜} in
@[simps] noncomputable def poles : ℤ⟦X⟧ˣ where
  val := ∏ i in S.toFinset.attach, (1 - PowerSeries.X ^ S.deg i.2)
  inv := PowerSeries.invOfUnit (∏ i in S.toFinset.attach, (1 - PowerSeries.X ^ S.deg i.2)) 1
  val_inv := PowerSeries.mul_invOfUnit _ _ <| by
    simp only [map_prod, map_sub, map_one, map_pow, constantCoeff_X, Units.val_one]
    refine Finset.prod_eq_one fun i _ ↦ ?_
    rw [zero_pow, sub_zero]
    linarith [irrelevant.deg_pos S i.2]
  inv_val := by
    rw [mul_comm]
    refine mul_invOfUnit _ _ ?_
    simp only [map_prod, map_sub, map_one, map_pow, constantCoeff_X, Units.val_one]
    refine Finset.prod_eq_one fun i _ ↦ ?_
    rw [zero_pow, sub_zero]
    linarith [irrelevant.deg_pos S i.2]

lemma poles_inv_eq' :
    (↑S.poles⁻¹ : ℤ⟦X⟧) =
    ∏ i in S.toFinset.attach, PowerSeries.invOfUnit (1 - PowerSeries.X ^ S.deg i.2) 1 := by
  rw [← Units.mul_eq_one_iff_inv_eq, val_poles, ← Finset.prod_mul_distrib]
  apply Finset.prod_eq_one
  rintro ⟨i, hi⟩ -
  refine mul_invOfUnit _ _ ?_
  simp only [map_sub, map_one, map_pow, constantCoeff_X, Units.val_one, sub_eq_self,
    pow_eq_zero_iff', ne_eq, true_and]
  linarith [irrelevant.deg_pos S hi]


end GradedRing.HomogeneousGeneratingSetOf

namespace HilbertSerre

variable (S : GradedRing.HomogeneousGeneratingSetOf 𝒜 (HomogeneousIdeal.irrelevant 𝒜).toIdeal)

abbrev statement : Prop := ∃ (p : Polynomial ℤ), μ.poincareSeries 𝒜 ℳ = p • S.poles⁻¹

section base_case

variable {𝒜}
variable (card_generator : S.toFinset.card = 0)

lemma eventually_eq_zero_of_empty_generatorSet :
    ∃ N : ℕ, ∀ n : ℕ, N < n → ∀ (x : ℳ n), x = 0 := by
  classical
  rw [Finset.card_eq_zero] at card_generator

  let T := GradedModule.HomogeneousGeneratingSetOf.Top A ℳ
  let deg : T.toFinset → ℕ := fun x ↦ T.deg x.2
  by_cases ne_empty : T.toFinset = ∅
  · refine ⟨1, fun n _ x ↦ ?_⟩
    have eq1 := kth_degree_eq_span S T n
    simp_rw [card_generator, Finset.subset_empty, Finsupp.support_eq_empty] at eq1
    replace eq1 := calc ⊤
      _ = _ := eq1
      _ = Submodule.span (𝒜 0) ∅ := by
          congr
          rw [Set.eq_empty_iff_forall_not_mem]
          rintro x ⟨ω, (hω : ω ∈ T.toFinset), -⟩
          rw [ne_empty] at hω
          simp only [Finset.not_mem_empty] at hω
      _ = ⊥ := by rw [Submodule.span_empty]
    rw [← Submodule.mem_bot (R := 𝒜 0), ← eq1]
    trivial

  let maxDeg : ℕ := Finset.image deg Finset.univ |>.max' (by
    simp only [Finset.univ_eq_attach, Finset.image_nonempty, Finset.attach_nonempty_iff]
    rw [Finset.nonempty_iff_ne_empty]
    exact ne_empty)

  refine ⟨maxDeg, fun n hn x ↦ ?_⟩
  have hn' (m : M) (hm : m ∈ T.toFinset) : T.deg hm < n
  · exact lt_of_le_of_lt (Finset.le_max' _ _ <| by aesop) hn

  have eq0 := kth_degree_eq_span S T n
  simp_rw [card_generator, Finset.subset_empty, Finsupp.support_eq_empty] at eq0
  replace eq0 := calc _
    _ = _ := eq0
    _ = Submodule.span (𝒜 0) {x : ℳ n | ∃ ω : M, ∃ (_ : ω ∈ T.toFinset), x = ω } := by
        congr
        ext x
        rw [Set.mem_setOf_eq, Set.mem_setOf_eq]
        refine exists_congr fun m ↦ exists_congr fun _ ↦ ⟨?_, ?_⟩
        · rintro ⟨_, rfl, -, h⟩; rwa [evalMonomial_zero, one_smul] at h
        · intro h
          refine ⟨_, rfl, ?_, h ▸ ?_⟩
          · erw [degreeMonomial_zero]; norm_num
          · rw [evalMonomial_zero, one_smul]
    _ = Submodule.span (𝒜 0) {x : ℳ n | (x : M) ∈ T.toFinset } := by
        congr
        ext x
        simp only [exists_prop, exists_eq_right', Set.mem_setOf_eq]
  have mem1 : x ∈ (⊤ : Submodule (𝒜 0) (ℳ n)) := ⟨⟩
  rw [eq0, mem_span_set] at mem1
  obtain ⟨f, support_le, (eq1 : ∑ i in f.support, f i • i = x)⟩ := mem1
  rw [Subtype.ext_iff, AddSubgroup.val_finset_sum] at eq1
  ext1
  rw [show (x : M) = GradedModule.proj ℳ n x from
    DirectSum.decompose_of_mem_same (hx := x.2) |>.symm, ← eq1, map_sum, AddSubgroup.coe_zero]
  refine Finset.sum_eq_zero fun x hx ↦ show GradedModule.proj ℳ n ((f x : A) • (x : M)) = 0 from ?_

  rw [GradedModule.proj_smul_mem_right 𝒜 ℳ (f x : A) (x : M) (T.mem_deg (support_le hx)),
    if_pos (le_of_lt <| hn' x (support_le hx)), GradedRing.proj_apply,
    DirectSum.decompose_of_mem_ne (hx := (f x).2), zero_smul]

  intro r
  rw [eq_comm, Nat.sub_eq_zero_iff_le] at r
  exact not_le_of_lt (hn' x (support_le hx)) r

lemma eventually_subsingleton_of_empty_generatorSet :
    ∃ N : ℕ, ∀ n : ℕ, N < n → Subsingleton (ℳ n) := by
  obtain ⟨N, h⟩ := eventually_eq_zero_of_empty_generatorSet ℳ S card_generator
  exact ⟨N, fun n hn ↦ ⟨fun x y ↦ (h n hn x).trans (h n hn y).symm⟩⟩

lemma proof.base_case : statement 𝒜 ℳ μ S := by
  obtain ⟨N, hN⟩ := eventually_subsingleton_of_empty_generatorSet ℳ S card_generator
  delta statement
  classical
  rw [Finset.card_eq_zero] at card_generator

  refine ⟨(μ.poincareSeries 𝒜 ℳ).trunc (N + 1), ?_⟩
  rw [Algebra.smul_def, eq_comm, Units.mul_inv_eq_iff_eq_mul, eq_comm]
  convert mul_one _
  · simp only [GradedRing.HomogeneousGeneratingSetOf.val_poles]
    convert Finset.prod_empty
    simp only[Finset.attach_eq_empty_iff, card_generator]

  · ext n
    simp only [algebraMap_apply', Algebra.id.map_eq_id, map_id, id_eq, Polynomial.coeff_coe,
      coeff_trunc, AdditiveFunction.poincareSeries, coeff_mk]
    by_cases hn : N < n
    · rw [if_neg (by linarith), eq_comm]
      exact μ.map_subsingleton (subsingleton := hN _ hn)
    · rw [if_pos]
      linarith

end base_case

namespace induction.constructions

variable {𝒜}
variable {d : ℕ} (x : A) (deg_x : x ∈ 𝒜 d)

@[simps]
def smulBy (n : ℕ) : ℳ n →ₗ[𝒜 0] ℳ (d + n) where
  toFun m := ⟨x • m, SetLike.GradedSMul.smul_mem deg_x m.2⟩
  map_add' := by aesop
  map_smul' r m := Subtype.ext <|
    show (x : A) • (r : A) • (m : M) = (r : A) • (x : A) • (m : M) from smul_comm _ _ _

def KER : Submodule A M where
  carrier := {m : M | x • m = 0}
  add_mem' {a b} (ha : x • a = 0) (hb : x • b = 0) := show x • (a + b) = 0 by
    rw [smul_add, ha, hb, add_zero]
  zero_mem' := show x • 0 = 0 from smul_zero _
  smul_mem' {a m} (hm : x • m = 0) := show x • (a • m) = 0 by
    rw [smul_comm, hm, smul_zero]

lemma mem_KER_iff (a : M) : a ∈ KER x ↔ x • a = 0 := Iff.rfl

def KERGradedPiece' (n : ℕ) : Submodule (𝒜 0) (ℳ n) :=
  LinearMap.ker (smulBy ℳ x deg_x n)

def KERGradedPiece (n : ℕ) : AddSubgroup (KER (M := M) x) where
  carrier := {m | (m : M) ∈ ℳ n ∧ x • m = 0}
  add_mem' := by
    rintro m₁ m₂ ⟨hm₁, hm₁'⟩ ⟨hm₂, hm₂'⟩
    refine ⟨AddSubgroup.add_mem _ hm₁ hm₂, ?_⟩
    rw [smul_add, hm₁', hm₂', add_zero]
  zero_mem' := ⟨AddSubgroup.zero_mem _, smul_zero _⟩
  neg_mem' := by
    rintro m ⟨hm1, hm2⟩
    refine ⟨AddSubgroup.neg_mem _ hm1, ?_⟩
    rw [smul_neg, hm2, neg_zero]


open DirectSum

instance : AddCommGroup (⨁ (i : ℕ), KERGradedPiece ℳ x i) :=
  DirectSum.addCommGroupSetLike _

variable [(i : ℕ) → (x : ℳ i) → Decidable (x ≠ 0)]

set_option synthInstance.maxHeartbeats 200000

def KER.decompose : KER (M := M) x → ⨁ (i : ℕ), KERGradedPiece ℳ x i := fun k ↦
  ∑ i in (DirectSum.decompose ℳ (k : M)).support, .of _ i
    ⟨⟨GradedModule.proj ℳ (i : ℕ) (k : M), by
      rw [mem_KER_iff]
      have hk : x • (k : M) = 0 := k.2
      apply_fun GradedModule.proj ℳ (i + d : ℕ) at hk
      rwa [GradedModule.proj_smul_mem_left 𝒜 ℳ x (k : M) deg_x, if_pos,
        Nat.add_sub_cancel, map_zero] at hk
      linarith⟩, ⟨(DirectSum.decompose ℳ (k : M) (i : ℕ)).2, by
        have hk : x • (k : M) = 0 := k.2
        apply_fun GradedModule.proj ℳ (i + d : ℕ) at hk
        rw [GradedModule.proj_smul_mem_left 𝒜 ℳ x (k : M) deg_x, if_pos (by linarith),
          Nat.add_sub_cancel, map_zero] at hk
        exact Subtype.ext hk⟩⟩

lemma KER.coe_decompose_apply (k : KER (M := M) x) (j : ℕ) :
    (KER.decompose ℳ x deg_x k j : M) =
    if j ∈ (DirectSum.decompose ℳ (k : M)).support
    then GradedModule.proj ℳ j (k : M)
    else 0 := by
  delta KER.decompose
  erw [DFinsupp.finset_sum_apply,  AddSubmonoidClass.coe_finset_sum,
        AddSubmonoidClass.coe_finset_sum]
  simp_rw [DirectSum.coe_of_apply]
  calc _
    _ = ∑ i in (DirectSum.decompose ℳ (k : M)).support,
          if i = j then GradedModule.proj ℳ i (k : M)
          else 0 := by
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        split_ifs <;> rfl
  rw [Finset.sum_ite_eq']

lemma KER.decompose_zero : KER.decompose ℳ x deg_x 0 = 0 := by
  refine DFinsupp.ext fun i ↦ ?_
  ext
  rw [KER.coe_decompose_apply, DirectSum.zero_apply, ZeroMemClass.coe_zero, ZeroMemClass.coe_zero]
  split_ifs
  · exact (GradedModule.proj ℳ i).map_zero
  · rfl

set_option maxHeartbeats 1000000 in
lemma KER.decompose_add (k₁ k₂ : KER (M := M) x) :
    KER.decompose ℳ x deg_x (k₁ + k₂) =
    KER.decompose ℳ x deg_x k₁ +
    KER.decompose ℳ x deg_x k₂ := by
  refine DFinsupp.ext fun i ↦ ?_
  ext
  rw [KER.coe_decompose_apply, DirectSum.add_apply, AddSubgroup.coe_add, Submodule.coe_add,
    Submodule.coe_add, KER.coe_decompose_apply, KER.coe_decompose_apply]
  split_ifs with h1 h2 h3 h4 h5 h6 h7
  · rw [map_add]
  · rw [map_add]
    simp only [DFinsupp.mem_support_toFun, ne_eq, not_not, Subtype.ext_iff] at h3
    rw [show GradedModule.proj ℳ i (k₂ : M) = 0 from h3]
  · rw [map_add]
    simp only [DFinsupp.mem_support_toFun, ne_eq, not_not, Subtype.ext_iff] at h2
    rw [show GradedModule.proj ℳ i (k₁ : M) = 0 from h2]
  · rw [map_add]
    simp only [DFinsupp.mem_support_toFun, ne_eq, not_not, Subtype.ext_iff] at h2 h4
    rw [show GradedModule.proj ℳ i (k₁ : M) = 0 from h2,
      show GradedModule.proj ℳ i (k₂ : M) = 0 from h4]
  · rw [← map_add]
    simp only [DFinsupp.mem_support_toFun, ne_eq, not_not, Subtype.ext_iff] at h1
    rw [show GradedModule.proj ℳ i (k₁ + k₂ : M) = 0 from h1]
  · simp only [DFinsupp.mem_support_toFun, ne_eq, not_not, Subtype.ext_iff] at h1 h6
    change GradedModule.proj ℳ i (k₁ + k₂ : M) = 0 at h1
    change GradedModule.proj ℳ i (k₂ : M) = 0 at h6
    rw [map_add] at h1
    have h2 : (_ + _) - _ = 0 - 0 := congr_arg₂ (· - ·) h1 h6
    rw [add_sub_assoc, sub_self, add_zero, sub_self] at h2
    rw [h2, add_zero]
  · simp only [DFinsupp.mem_support_toFun, ne_eq, not_not, Subtype.ext_iff] at h1 h5
    change GradedModule.proj ℳ i (k₁ + k₂ : M) = 0 at h1
    change GradedModule.proj ℳ i (k₁ : M) = 0 at h5
    rw [map_add] at h1
    have h2 : (_ + _) - _ = 0 - 0 := congr_arg₂ (· - ·) h1 h5
    rw [add_comm, add_sub_assoc, sub_self, add_zero, sub_self] at h2
    rw [h2, add_zero]
  · rw [add_zero]

lemma KER.decompose_leftInverse :
    Function.LeftInverse ((DirectSum.coeAddMonoidHom fun i ↦ KERGradedPiece ℳ x i))
      (KER.decompose ℳ x deg_x) := by
  rintro ⟨k, hk⟩
  ext
  simp only [map_sum, DirectSum.coeAddMonoidHom_of, KER.decompose,
    AddSubmonoid.coe_finset_sum, GradedModule.proj_apply, DirectSum.sum_support_decompose]

set_option maxHeartbeats 1000000 in
lemma KER.decompose_rightInverse :
    Function.RightInverse ((DirectSum.coeAddMonoidHom fun i ↦ KERGradedPiece ℳ x i))
      (KER.decompose ℳ x deg_x) := by
  intro z
  induction' z using DirectSum.induction_on with i z a b ha hb
  · apply KER.decompose_zero
  · rw [DirectSum.coeAddMonoidHom_of]
    refine DFinsupp.ext fun j ↦ ?_
    ext
    rw [KER.coe_decompose_apply, DirectSum.coe_of_apply]
    split_ifs with h1 h2 h3
    · subst h2
      rw [GradedModule.proj_apply, DirectSum.decompose_of_mem_same (hx := z.2.1)]
    · rw [GradedModule.proj_apply, DirectSum.decompose_of_mem_ne (hx := z.2.1) (hij := h2)]
      rfl
    · subst h3
      simp only [DFinsupp.mem_support_toFun, ne_eq, not_not] at h1
      rw [Subtype.ext_iff, DirectSum.decompose_of_mem_same (hx := z.2.1)] at h1
      exact h1.symm
    · rfl
  · rw [(DirectSum.coeAddMonoidHom fun i ↦ KERGradedPiece ℳ x i).map_add, KER.decompose_add,
      ha, hb]

def KERDecomposition : DirectSum.Decomposition (fun i : ℕ ↦ KERGradedPiece ℳ x i) where
  decompose' := KER.decompose ℳ x deg_x
  left_inv := KER.decompose_leftInverse ℳ x deg_x
  right_inv := KER.decompose_rightInverse ℳ x deg_x

end induction.constructions

end HilbertSerre
