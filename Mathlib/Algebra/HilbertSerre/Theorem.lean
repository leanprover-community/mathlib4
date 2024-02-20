/-
Copyright (c) 2024 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/

import Mathlib.RingTheory.GradedAlgebra.Noetherian
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Algebra.HilbertSerre.AdditiveFunction
import Mathlib.Algebra.Category.FGModuleCat.Abelian
import Mathlib.RingTheory.GradedAlgebra.Subgrading

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

def KER : HomogeneousSubmodule A ℳ where
  carrier := {m : M | x • m = 0 }
  add_mem' := by aesop
  zero_mem' := by aesop
  smul_mem' := by intros; simp only [Set.mem_setOf_eq]; rw [smul_comm]; aesop
  is_homogeneous' i m (h : x • m = 0) := show x • _ = 0 by
    have := GradedModule.proj_smul_mem_left (j := i + d) 𝒜 ℳ x m deg_x
    rw [h, if_pos (by linarith), map_zero, GradedModule.proj_apply, Nat.add_sub_cancel] at this
    exact this.symm

lemma mem_KER_iff (a : M) : a ∈ KER ℳ x deg_x ↔ x • a = 0 := Iff.rfl

variable [(i : ℕ) → (x : ↥(ℳ i)) → Decidable (x ≠ 0)] [(a : M) → Decidable (a ∈ KER ℳ x deg_x)]

instance : DirectSum.Decomposition (KER ℳ x deg_x).grading :=
  HomogeneousSubmodule.decomposition _

open Pointwise

abbrev COKER.den : HomogeneousSubmodule A ℳ :=
{ toSubmodule := x • (⊤ : Submodule A M)
  is_homogeneous' := by
    intro i m hm
    obtain ⟨m, -, rfl⟩ := hm
    refine ⟨if d ≤ i then GradedModule.proj ℳ (i - d) m else 0, trivial, ?_⟩
    show x • _ = GradedModule.proj ℳ i (x • m)
    rw [GradedModule.proj_smul_mem_left 𝒜 ℳ x m deg_x]
    split_ifs <;> aesop }

abbrev COKER := M ⧸ (COKER.den ℳ x deg_x).toSubmodule

instance : DirectSum.Decomposition (COKER.den ℳ x deg_x).quotientGrading :=
  HomogeneousSubmodule.quotientDecomposition _

instance : SetLike.GradedSMul 𝒜 (COKER.den ℳ x deg_x).quotientGrading :=
  HomogeneousSubmodule.quotientGradedSMul _

@[simps]
def KER.componentEmb (n : ℕ) : (KER ℳ x deg_x).grading n →ₗ[𝒜 0] ℳ n where
  toFun a := ⟨a.1, a.2⟩
  map_add' := by intros; ext; rfl
  map_smul' := by intros; ext; rfl

@[simps]
def smulBy (n : ℕ) : ℳ n →ₗ[𝒜 0] ℳ (d + n) where
  toFun m := ⟨x • m, SetLike.GradedSMul.smul_mem deg_x m.2⟩
  map_add' := by aesop
  map_smul' r m := Subtype.ext <|
    show (x : A) • (r : A) • (m : M) = (r : A) • (x : A) • (m : M) from smul_comm _ _ _

instance (n : ℕ) : Module (𝒜 0) ((COKER.den ℳ x deg_x).quotientGrading n) :=
DirectSum.GradeZero.module_at_i 𝒜 (COKER.den ℳ x deg_x).quotientGrading n


def COKER.descComponent (n : ℕ) :
    ℳ n →ₗ[𝒜 0] (COKER.den ℳ x deg_x).quotientGrading n where
  toFun m := ⟨Quotient.mk'' m, by
    simp only [Submodule.Quotient.mk''_eq_mk, HomogeneousSubmodule.quotientGrading,
      HomogeneousSubmodule.quotientGradingEmb, Submodule.pointwise_smul_toAddSubgroup,
      Submodule.top_toAddSubgroup, AddMonoidHom.mem_range]
    use m
    erw [QuotientAddGroup.map_mk']
    rfl  ⟩
  map_add' := by intros; ext; rfl
  map_smul' := by intros; ext; rfl

-- `0 -> KERₘ -> ℳₙ` is exact
lemma KER.componentEmb_injective (n : ℕ) : Function.Injective (KER.componentEmb ℳ x deg_x n) := by
  intros a b h
  ext
  rw [Subtype.ext_iff, componentEmb_apply_coe, componentEmb_apply_coe] at h
  exact h

-- `KERₙ -> ℳₙ -> ℳ_{d + n}` is exact
lemma exact_KERComponentEmb_smulBy (n : ℕ) :
    LinearMap.range (KER.componentEmb ℳ x deg_x n) = LinearMap.ker (smulBy ℳ x deg_x n) := by
  ext m
  fconstructor
  · rintro ⟨⟨⟨m, (hm1 : x • m = 0)⟩, (hm2 : m ∈ ℳ n)⟩, rfl⟩
    simp only [LinearMap.mem_ker]
    ext
    simpa only [smulBy_apply_coe, KER.componentEmb_apply_coe, ZeroMemClass.coe_zero]
  · intro hm
    simp only [LinearMap.mem_ker, Subtype.ext_iff, smulBy_apply_coe, ZeroMemClass.coe_zero] at hm
    exact ⟨⟨⟨m, hm⟩, m.2⟩, rfl⟩

-- `ℳₙ -> ℳ_{d + n} -> COKER_{d + n}` is exact
lemma exact_smulBy_COKERDescComponent (n : ℕ) :
    LinearMap.range (smulBy ℳ x deg_x n) = LinearMap.ker (COKER.descComponent ℳ x deg_x (d + n)) := by
  ext m
  fconstructor
  · rintro ⟨m, rfl⟩
    simp only [LinearMap.mem_ker]
    ext
    erw [QuotientAddGroup.eq_zero_iff]
    simp only [smulBy_apply_coe, Submodule.pointwise_smul_toAddSubgroup,
      Submodule.top_toAddSubgroup]
    exact ⟨m, trivial, rfl⟩
  · intro hm
    erw [LinearMap.mem_ker, Subtype.ext_iff, QuotientAddGroup.eq_zero_iff] at hm
    obtain ⟨m', -, (hm' : x • m' = m.1)⟩ := hm
    refine ⟨⟨(DirectSum.decompose ℳ m' n), SetLike.coe_mem _⟩, ?_⟩
    ext
    simp only [Subtype.coe_eta, smulBy_apply_coe]
    have eq0 := GradedModule.proj_smul_mem_left (j := d + n) 𝒜 ℳ x m' deg_x
    rwa [if_pos (by linarith), GradedModule.proj_apply, GradedModule.proj_apply, add_comm,
      Nat.add_sub_cancel, DirectSum.decompose_of_mem_same, hm', eq_comm] at eq0
    convert m.2 using 1
    rw [add_comm]

-- `ℳ_{d + n} -> COKER_{d + n} ->` is exact
lemma COKER.descComponent_surjective (n : ℕ) :
    Function.Surjective (COKER.descComponent ℳ x deg_x (d + n)) := by
  rintro ⟨_, ⟨m, rfl⟩⟩
  induction' m using Quotient.inductionOn' with m
  exact ⟨m, rfl⟩

end induction.constructions

end HilbertSerre
