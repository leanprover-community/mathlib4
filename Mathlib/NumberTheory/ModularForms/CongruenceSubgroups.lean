/-
Copyright (c) 2022 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Integer
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-!
# Congruence subgroups

This defines congruence subgroups of `SL(2, ℤ)` such as `Γ(N)`, `Γ₀(N)` and `Γ₁(N)` for `N` a
natural number.

It also contains basic results about congruence subgroups.

-/

open Matrix.SpecialLinearGroup Matrix

open scoped MatrixGroups ModularGroup Real

variable (N : ℕ)

local notation "SLMOD(" N ")" =>
  @Matrix.SpecialLinearGroup.map (Fin 2) _ _ _ _ _ _ (Int.castRingHom (ZMod N))

@[simp]
theorem SL_reduction_mod_hom_val (γ : SL(2, ℤ)) (i j : Fin 2):
    SLMOD(N) γ i j = (γ i j : ZMod N) :=
  rfl

namespace CongruenceSubgroup

/-- The full level `N` congruence subgroup of `SL(2, ℤ)` of matrices that reduce to the identity
modulo `N`. -/
def Gamma : Subgroup SL(2, ℤ) :=
  SLMOD(N).ker

@[inherit_doc] scoped notation  "Γ(" n ")"  => Gamma n

theorem Gamma_mem' {N} {γ : SL(2, ℤ)} : γ ∈ Gamma N ↔ SLMOD(N) γ = 1 :=
  Iff.rfl

@[simp]
theorem Gamma_mem {N} {γ : SL(2, ℤ)} : γ ∈ Gamma N ↔ (γ 0 0 : ZMod N) = 1 ∧
    (γ 0 1 : ZMod N) = 0 ∧ (γ 1 0 : ZMod N) = 0 ∧ (γ 1 1 : ZMod N) = 1 := by
  rw [Gamma_mem']
  constructor
  · intro h
    simp [← SL_reduction_mod_hom_val N γ, h]
  · intro h
    ext i j
    rw [SL_reduction_mod_hom_val N γ]
    fin_cases i <;> fin_cases j <;> simp only [h]
    exacts [h.1, h.2.1, h.2.2.1, h.2.2.2]

theorem Gamma_normal : Subgroup.Normal (Gamma N) :=
  SLMOD(N).normal_ker

theorem Gamma_one_top : Gamma 1 = ⊤ := by
  ext
  simp [eq_iff_true_of_subsingleton]

lemma mem_Gamma_one (γ : SL(2, ℤ)) : γ ∈ Γ(1) := by
  simp only [Gamma_one_top, Subgroup.mem_top]

theorem Gamma_zero_bot : Gamma 0 = ⊥ := rfl

lemma ModularGroup_T_pow_mem_Gamma (N M : ℤ) (hNM : N ∣ M) :
    (ModularGroup.T ^ M) ∈ Gamma (Int.natAbs N) := by
  simp only [Gamma_mem, Fin.isValue, ModularGroup.coe_T_zpow, of_apply, cons_val', cons_val_zero,
    empty_val', cons_val_fin_one, Int.cast_one, cons_val_one, head_cons, head_fin_const,
    Int.cast_zero, and_self, and_true, true_and]
  refine Iff.mpr (ZMod.intCast_zmod_eq_zero_iff_dvd M (Int.natAbs N)) ?_
  simp only [Int.natCast_natAbs, abs_dvd, hNM]

instance instFiniteIndexGamma [NeZero N] : (Gamma N).FiniteIndex := Subgroup.finiteIndex_ker _

/-- The congruence subgroup of `SL(2, ℤ)` of matrices whose lower left-hand entry reduces to zero
modulo `N`. -/
def Gamma0 : Subgroup SL(2, ℤ) where
  carrier := { g | (g 1 0 : ZMod N) = 0 }
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq]
    have h := (Matrix.two_mul_expl a.1 b.1).2.2.1
    simp only [coe_matrix_coe, coe_mul, Int.coe_castRingHom, map_apply, Set.mem_setOf_eq] at *
    rw [h]
    simp [ha, hb]
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq]
    rw [SL2_inv_expl a]
    simp only [cons_val_zero, cons_val_one, head_cons, coe_matrix_coe,
      coe_mk, Int.coe_castRingHom, map_apply, Int.cast_neg, neg_eq_zero, Set.mem_setOf_eq] at *
    exact ha

@[simp]
theorem Gamma0_mem {N} {A : SL(2, ℤ)} : A ∈ Gamma0 N ↔ (A 1 0 : ZMod N) = 0 :=
  Iff.rfl

/-- The group homomorphism from `CongruenceSubgroup.Gamma0` to `ZMod N` given by
mapping a matrix to its lower right-hand entry. -/
def Gamma0Map (N : ℕ) : Gamma0 N →* ZMod N where
  toFun g := g.1 1 1
  map_one' := by simp
  map_mul' := by
    rintro ⟨A, hA⟩ ⟨B, _⟩
    simp only [MulMemClass.mk_mul_mk, Fin.isValue, coe_mul, (two_mul_expl A.1 B).2.2.2,
      Int.cast_add, Int.cast_mul, Gamma0_mem.mp hA, zero_mul, zero_add]

/-- The congruence subgroup `Gamma1` (as a subgroup of `Gamma0`) of matrices whose bottom
row is congruent to `(0, 1)` modulo `N`. -/
def Gamma1' (N : ℕ) : Subgroup (Gamma0 N) :=
  (Gamma0Map N).ker

@[simp]
theorem Gamma1_mem' {N} {γ : Gamma0 N} : γ ∈ Gamma1' N ↔ Gamma0Map N γ = 1 :=
  Iff.rfl

theorem Gamma1_to_Gamma0_mem {N} (A : Gamma0 N) :
    A ∈ Gamma1' N ↔
    ((A.1 0 0 : ℤ) : ZMod N) = 1 ∧ ((A.1 1 1 : ℤ) : ZMod N) = 1
      ∧ ((A.1 1 0 : ℤ) : ZMod N) = 0 := by
  constructor
  · intro ha
    have adet : (A.1.1.det : ZMod N) = 1 := by simp only [A.1.property, Int.cast_one]
    rw [Matrix.det_fin_two] at adet
    simp only [Gamma1_mem', Gamma0Map, MonoidHom.coe_mk, OneHom.coe_mk, Int.cast_sub,
      Int.cast_mul] at *
    simpa only [Gamma1_mem', Gamma0Map, MonoidHom.coe_mk, OneHom.coe_mk, Int.cast_sub,
      Int.cast_mul, ha, Gamma0_mem.mp A.property, and_self_iff, and_true, mul_one, mul_zero,
      sub_zero] using adet
  · intro ha
    simp only [Gamma1_mem', Gamma0Map, MonoidHom.coe_mk, coe_matrix_coe,
      Int.coe_castRingHom, map_apply]
    exact ha.2.1

/-- The congruence subgroup `Gamma1` of `SL(2, ℤ)` consisting of matrices
whose bottom row is congruent to `(0,1)` modulo `N`. -/
def Gamma1 (N : ℕ) : Subgroup SL(2, ℤ) :=
  Subgroup.map ((Gamma0 N).subtype.comp (Gamma1' N).subtype) ⊤

@[simp]
theorem Gamma1_mem (N : ℕ) (A : SL(2, ℤ)) : A ∈ Gamma1 N ↔
    (A 0 0 : ZMod N) = 1 ∧ (A 1 1 : ZMod N) = 1 ∧ (A 1 0 : ZMod N) = 0 := by
  constructor
  · intro ha
    simp_rw [Gamma1, Subgroup.mem_map] at ha
    obtain ⟨⟨x, hx⟩, hxx⟩ := ha
    rw [Gamma1_to_Gamma0_mem] at hx
    simp only [Subgroup.mem_top, true_and] at hxx
    rw [← hxx]
    convert hx
  · intro ha
    simp_rw [Gamma1, Subgroup.mem_map]
    have hA : A ∈ Gamma0 N := by simp [ha.right.right, Gamma0_mem]
    have HA : (⟨A, hA⟩ : Gamma0 N) ∈ Gamma1' N := by
      simp only [Gamma1_to_Gamma0_mem, Subgroup.coe_mk, coe_matrix_coe,
        Int.coe_castRingHom, map_apply]
      exact ha
    refine ⟨(⟨(⟨A, hA⟩ : Gamma0 N), HA⟩ : (Gamma1' N : Subgroup (Gamma0 N))), ?_⟩
    simp

theorem Gamma1_in_Gamma0 (N : ℕ) : Gamma1 N ≤ Gamma0 N := by
  intro x HA
  simp only [Gamma0_mem, Gamma1_mem, coe_matrix_coe, Int.coe_castRingHom, map_apply] at *
  exact HA.2.2

section CongruenceSubgroups

/-- A congruence subgroup is a subgroup of `SL(2, ℤ)` which contains some `Gamma N` for some
`N ≠ 0`. -/
def IsCongruenceSubgroup (Γ : Subgroup SL(2, ℤ)) : Prop :=
  ∃ N ≠ 0, Gamma N ≤ Γ

theorem isCongruenceSubgroup_trans (H K : Subgroup SL(2, ℤ)) (h : H ≤ K)
    (h2 : IsCongruenceSubgroup H) : IsCongruenceSubgroup K := by
  obtain ⟨N, hN⟩ := h2
  exact ⟨N, hN.1, hN.2.trans h⟩

theorem Gamma_is_cong_sub (N : ℕ) [NeZero N] : IsCongruenceSubgroup (Gamma N) :=
  ⟨N, NeZero.ne _, le_rfl⟩

theorem Gamma1_is_congruence (N : ℕ) [NeZero N] : IsCongruenceSubgroup (Gamma1 N) := by
  refine ⟨N, NeZero.ne _, fun A hA ↦ ?_⟩
  simp_all [Gamma1_mem, Gamma_mem]

theorem Gamma0_is_congruence (N : ℕ) [NeZero N] : IsCongruenceSubgroup (Gamma0 N) :=
  isCongruenceSubgroup_trans _ _ (Gamma1_in_Gamma0 N) (Gamma1_is_congruence N)

lemma IsCongruenceSubgroup.finiteIndex {Γ : Subgroup SL(2, ℤ)}
    (h : IsCongruenceSubgroup Γ) : Γ.FiniteIndex := by
  obtain ⟨N, hN⟩ := h
  have : NeZero N := ⟨hN.1⟩
  exact Subgroup.finiteIndex_of_le hN.2

instance instFiniteIndexGamma0 [NeZero N] : (Gamma0 N).FiniteIndex :=
  (Gamma0_is_congruence N).finiteIndex

instance instFiniteIndexGamma1 [NeZero N] : (Gamma1 N).FiniteIndex :=
  (Gamma1_is_congruence N).finiteIndex

end CongruenceSubgroups

section Conjugation

open Pointwise ConjAct

/-- The subgroup `SL(2, ℤ) ∩ g⁻¹ Γ g`, for `Γ` a subgroup of `SL(2, ℤ)` and `g ∈ GL(2, ℝ)`. -/
def conjGL (Γ : Subgroup SL(2, ℤ)) (g : GL (Fin 2) ℝ) : Subgroup SL(2, ℤ) :=
  ((toConjAct g⁻¹) • (Γ.map (SpecialLinearGroup.toGL.comp
    <| SpecialLinearGroup.map (Int.castRingHom ℝ)))).comap
    (SpecialLinearGroup.toGL.comp  <| SpecialLinearGroup.map (Int.castRingHom ℝ))

@[simp] lemma mem_conjGL {Γ : Subgroup SL(2, ℤ)} {g : GL (Fin 2) ℝ} {x : SL(2, ℤ)} :
    x ∈ conjGL Γ g ↔ ∃ y ∈ Γ, y = g * x * g⁻¹ := by
  simp [conjGL, Subgroup.mem_inv_pointwise_smul_iff, toConjAct_smul]

lemma mem_conjGL' {Γ : Subgroup SL(2, ℤ)} {g : GL (Fin 2) ℝ} {x : SL(2, ℤ)} :
    x ∈ conjGL Γ g ↔ ∃ y ∈ Γ, g⁻¹ * y * g = x := by
  rw [mem_conjGL]
  refine exists_congr fun y ↦ and_congr_right fun hy ↦ ?_
  rw [eq_mul_inv_iff_mul_eq, mul_assoc, inv_mul_eq_iff_eq_mul]

@[simp]
lemma conjGL_coe (Γ : Subgroup SL(2, ℤ)) (g : SL(2, ℤ)) :
    conjGL Γ g = (toConjAct g⁻¹) • Γ := by
  ext x
  simp_rw [mem_conjGL, ← map_inv, ← map_mul, toGL_injective.eq_iff, map_intCast_injective.eq_iff,
    exists_eq_right, toConjAct_inv, Subgroup.mem_inv_pointwise_smul_iff, toConjAct_smul]

@[deprecated (since := "2025-05-15")] alias conjGLPos := conjGL
@[deprecated (since := "2025-05-15")] alias conjGLPos_coe := conjGL_coe
@[deprecated (since := "2025-05-15")] alias mem_conjGLPos := mem_conjGL
@[deprecated (since := "2025-05-15")] alias mem_conjGLPos' := mem_conjGL'

theorem Gamma_cong_eq_self (N : ℕ) (g : ConjAct SL(2, ℤ)) : g • Gamma N = Gamma N := by
  apply Subgroup.Normal.conjAct (Gamma_normal N)

theorem conj_cong_is_cong (g : ConjAct SL(2, ℤ)) (Γ : Subgroup SL(2, ℤ))
    (h : IsCongruenceSubgroup Γ) : IsCongruenceSubgroup (g • Γ) := by
  obtain ⟨N, HN⟩ := h
  refine ⟨N, ?_⟩
  rw [← Gamma_cong_eq_self N g, Subgroup.pointwise_smul_le_pointwise_smul_iff]
  exact HN

/-- For any `g ∈ GL(2, ℚ)` and `M ≠ 0`, there exists `N` such that `g x g⁻¹ ∈ Γ(M)` for all
`x ∈ Γ(N)`. -/
theorem exists_Gamma_le_conj (g : GL (Fin 2) ℚ) (M : ℕ) [NeZero M] :
    ∃ N ≠ 0, ∀ x ∈ Gamma N, g * (x.map (Int.castRingHom ℚ)).toGL * g⁻¹ ∈
      (fun x : SL(2, ℤ) ↦ (x.map (Int.castRingHom ℚ)).toGL) '' (Gamma M) := by
  -- Give names to the numerators and denominators of `g` and `g⁻¹`
  let A₁ := g.1
  let A₂ := (g⁻¹).1
  have hA₁₂ : A₁ * A₂ = 1 := by simp only [← Matrix.GeneralLinearGroup.coe_mul,
    mul_inv_cancel, Matrix.GeneralLinearGroup.coe_one, A₁, A₂]
  let a₁ := A₁.den
  let a₂ := A₂.den
  -- we take `N = a₁ * a₂`
  refine ⟨a₁ * a₂ * M, mul_ne_zero (mul_ne_zero A₁.den_ne_zero A₂.den_ne_zero) (NeZero.ne _),
    fun ⟨y, hy⟩ hy' ↦ ?_⟩
  -- Show that `y` is of the form `1 + (a₁ * a₂) • k` for some integer matrix `k`.
  obtain ⟨k, hk⟩ : ∃ k, y = 1 + (a₁ * a₂ * M) • k := by
    replace hy' : y.map (Int.cast : ℤ → ZMod (a₁ * a₂ * M)) = 1 := by
      rw [CongruenceSubgroup.Gamma_mem', Subtype.ext_iff] at hy'
      simpa using hy'
    use Matrix.of fun i j ↦ (y - 1) i j / (a₁ * a₂ * M)
    rw [← sub_eq_iff_eq_add']
    ext i j
    simp_rw [Matrix.smul_apply, Matrix.of_apply, nsmul_eq_mul, Nat.cast_mul]
    refine (Int.mul_ediv_cancel_of_dvd ?_).symm
    rw [← Matrix.map_one Int.cast (by simp) (by simp), ← sub_eq_zero,
      ← Matrix.map_sub _ (by simp)] at hy'
    simpa only [Matrix.zero_apply, Matrix.map_apply, ZMod.intCast_zmod_eq_zero_iff_dvd,
      Nat.cast_mul] using congr_fun₂ hy' i j
  -- use this `k` to cook up a new integer matrix, which we will show comes from `SL(2, ℤ)`
  let z := 1 + M • (A₁.num * k * A₂.num)
  have hz_coe : z.map Int.cast = A₁ * (y.map Int.cast) * A₂ := by
    simp only [Matrix.map_add _ Int.cast_add, Matrix.map_one _ Int.cast_zero Int.cast_one, hk,
      mul_add, mul_one, add_mul, hA₁₂, add_right_inj, z]
    conv_rhs => rw [← A₁.inv_denom_smul_num, ← A₂.inv_denom_smul_num, Matrix.map_smul _ _ (by simp)]
    simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.map_smul (Int.cast : ℤ → ℚ) M (by simp),
      Matrix.map_mul_intCast]
    rw [← Nat.cast_smul_eq_nsmul ℚ (_ * M), ← MulAction.mul_smul, ← MulAction.mul_smul,
      mul_comm a₁ a₂, Nat.cast_mul, Nat.cast_mul, mul_assoc _ _ (M : ℚ), mul_comm _ (M : ℚ),
      inv_mul_cancel_left₀ (mod_cast A₂.den_ne_zero),
      mul_inv_cancel_right₀ (mod_cast A₁.den_ne_zero), Nat.cast_smul_eq_nsmul]
  have hz_det : z.det = 1 := by
    have := congr_arg Matrix.det hz_coe
    simp_rw [Matrix.det_mul, ← Int.cast_det] at this
    rwa [mul_right_comm, ← Matrix.det_mul, hA₁₂, Matrix.det_one, one_mul, hy, Int.cast_inj] at this
  refine ⟨⟨z, hz_det⟩, ?_, by simpa only [Subtype.ext_iff, Subgroup.coe_mul, Units.ext_iff,
    Units.val_mul] using hz_coe⟩
  rw [SetLike.mem_coe, CongruenceSubgroup.Gamma_mem', Subtype.ext_iff]
  ext i j
  simp_rw [map_apply_coe, z, map_add, map_one, RingHom.mapMatrix_apply, Int.coe_castRingHom,
    add_apply, map_apply, coe_one, add_eq_left, Matrix.smul_apply, nsmul_eq_mul, Int.cast_mul,
    Int.cast_natCast, ZMod.natCast_self M, zero_mul]

/-- For any `g ∈ GL(2, ℚ)` and `M ≠ 0`, there exists `N` such that `g Γ(N) g⁻¹ ≤ Γ(M)`. -/
theorem exists_Gamma_le_conj' (g : GL (Fin 2) ℚ) (M : ℕ) [NeZero M] :
    ∃ N ≠ 0, (toConjAct <| g.map (Rat.castHom ℝ)) • (Gamma N).map (mapGL ℝ)
      ≤ (Gamma M).map (mapGL ℝ) := by
  obtain ⟨N, hN, h⟩ := exists_Gamma_le_conj g M
  refine ⟨N, hN, fun y hy ↦ ?_⟩
  simp_rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, Subgroup.mem_map,
    eq_inv_smul_iff] at hy
  obtain ⟨x, hx, rfl⟩ := hy
  obtain ⟨z, hz, hz'⟩ := h x hx
  use z, hz
  simpa only [Subtype.ext_iff, Units.ext_iff, map_mul] using
    congr_arg (GeneralLinearGroup.map (Rat.castHom ℝ)) hz'

open Subgroup in
/-- If `Γ` has finite index in `SL(2, ℤ)`, then so does `g⁻¹ Γ g ∩ SL(2, ℤ)` for any
`g ∈ GL(2, ℚ)`. -/
lemma finiteIndex_conjGL (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (g : GL (Fin 2) ℚ) :
    (conjGL Γ (g.map <| Rat.castHom ℝ)).FiniteIndex := by
  constructor
  let t := (toConjAct <| g.map <| Rat.castHom ℝ)⁻¹
  let G := Γ.map (mapGL ℝ)
  let A := MonoidHom.range (mapGL ℝ : SL(2, ℤ) →* _)
  suffices (t • G ⊓ A).relindex A ≠ 0 by rwa [conjGL, index_comap, ← inf_relindex_right]
  apply relindex_ne_zero_trans (K := t • A ⊓ A)
  · -- Show that `[ (t • A ⊓ A) : (t • G ⊓ A)] < ∞`.
    apply relindex_inter_ne_zero
    rw [relindex_pointwise_smul, ← index_comap,
      comap_map_eq_self_of_injective mapGL_injective]
    exact FiniteIndex.index_ne_zero
  · -- Show that `[A : (t • A ⊓ A)] < ∞` (note this is independent of `Γ`)
    obtain ⟨N, hN, hN'⟩ := exists_Gamma_le_conj' g 1
    rw [Gamma_one_top, ← MonoidHom.range_eq_map] at hN'
    suffices Γ(N) ≤ (t • A ⊓ A).comap (mapGL ℝ) by
      haveI _ : NeZero N := ⟨hN⟩
      simpa only [index_comap] using (finiteIndex_of_le this).index_ne_zero
    intro k hk
    simpa [mem_pointwise_smul_iff_inv_smul_mem, A] using
      hN' <| smul_mem_pointwise_smul _ _ _ ⟨k, hk, rfl⟩

/-- If `Γ` is a congruence subgroup, then so is `g⁻¹ Γ g ∩ SL(2, ℤ)` for any `g ∈ GL(2, ℚ)`. -/
lemma IsCongruenceSubgroup.conjGL {Γ : Subgroup SL(2, ℤ)} (hΓ : IsCongruenceSubgroup Γ)
    (g : GL (Fin 2) ℚ) :
    IsCongruenceSubgroup (conjGL Γ (g.map <| Rat.castHom ℝ)) := by
  obtain ⟨M, hN, hΓM⟩ := hΓ
  haveI _ : NeZero M := ⟨hN⟩
  obtain ⟨N, hN, hN'⟩ := exists_Gamma_le_conj' g M
  rw [Subgroup.pointwise_smul_subset_iff] at hN'
  refine ⟨N, ‹_›, fun x hx ↦ ?_⟩
  obtain ⟨y, hy, hy'⟩ := Subgroup.mem_inv_pointwise_smul_iff.mp <| hN' ⟨x, hx, rfl⟩
  exact mem_conjGL.mpr ⟨y, hΓM hy, hy'⟩

end Conjugation

end CongruenceSubgroup
