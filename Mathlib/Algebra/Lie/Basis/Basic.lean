/-
Copyright (c) 2026 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
module

public import Mathlib.Algebra.Lie.Weights.Killing

/-!
# Bases of semisimple Lie algebras

In this file we define bases of semisimple Lie algebras. Given an indexing type `ι`, a basis of a
Lie algebra consists of a non-degenerate matrix of integers `A` indexed by `ι × ι` and generators
`h i`, `e i`, `f i` indexed by `ι`, each forming an `sl₂` triple, and satisfying the Chevalley-Serre
relations:
* `⁅h i, h j⁆ = 0`
* `⁅h j, e i⁆ =  A i j • e i`
* `⁅h j, f i⁆ = -A i j • f i`
* `⁅e i, f j⁆ = 0` (for `i ≠ j`)

This concept appears not to have a name in the informal literature and so we call it simply a basis.
With further axioms (constraining the structure constants which appear in products of the form
`⁅e i, e j⁆`, `⁅f i, f j⁆`) one obtains the concept of a Weyl or Chevalley basis.
See e.g., [serre1965](Ch. V, §4, §6).

## Main definitions / results:

* `LieAlgebra.Basis`: the concept of a basis for a Lie algebra.
* `LieAlgebra.Basis.cartanMatrix_base_eq`: the matrix of a `LieAlgebra.Basis` is the Cartan matrix
  of the associated based root system.

## TODO

* Show that every semisimple Lie algebra has a basis.
* Define Weyl, Chevalley bases.

-/

@[expose] public section

open Function LieSubalgebra Module Set

noncomputable section

namespace LieAlgebra

/-- A basis for a semisimple Lie algebra distinguishes a natural Cartan subalgebra and a base
for the associated root system. -/
@[ext]
structure Basis (ι : Type*) {R L : Type*} [Finite ι] [CommRing R] [LieRing L] [LieAlgebra R L]
    (H : LieSubalgebra R L) where
  /-- The Cartan matrix. -/
  A : Matrix ι ι ℤ
  /-- The basis for the Cartan subalgebra. -/
  h : ι → L
  /-- The generators of the upper Borel subalgebra. -/
  e : ι → L
  /-- The generators of the lower Borel subalgebra. -/
  f : ι → L
  cartan_eq_lieSpan : H = lieSpan R L (range h)
  span_ef : lieSpan R L (range e ∪ range f) = ⊤
  linInd : LinearIndependent R h
  nondegen : A.Nondegenerate -- TODO Replace with `(b.A.det : R) ≠ 0` to support positive char
  sl2 (i : ι) : IsSl2Triple (h i) (e i) (f i)
  lie_h_h (i j : ι) : ⁅h i, h j⁆ = 0
  lie_h_e (i j : ι) : ⁅h j, e i⁆ = A i j • e i
  lie_h_f (i j : ι) : ⁅h j, f i⁆ = -A i j • f i
  lie_e_f_ne (i j : ι) (hij : i ≠ j) : ⁅e i, f j⁆ = 0

namespace Basis

section CommRing

variable {ι R L : Type*} [Finite ι] [CommRing R] [LieRing L] [LieAlgebra R L]
  {H : LieSubalgebra R L} (b : Basis ι H)

@[simp] lemma A_diag_eq_two [IsAddTorsionFree L] (i : ι) : b.A i i = 2 := by
  have : NoZeroSMulDivisors ℤ L := IsAddTorsionFree.to_noZeroSMulDivisors_int
  have aux : (b.A i i - 2) • b.e i = 0 := by
    rw [sub_smul, ofNat_smul_eq_nsmul, ← (b.sl2 i).lie_h_e_nsmul, b.lie_h_e i i]; abel
  rwa [IsAddTorsionFree.zsmul_eq_zero_iff_left (b.sl2 i).e_ne_zero, sub_eq_zero] at aux

lemma coe_cartan_eq_span :
    H = Submodule.span R (range b.h) := by
  conv_lhs => rw [b.cartan_eq_lieSpan]
  apply coe_lieSpan_eq_span_of_forall_lie_eq_zero
  rintro - ⟨i, rfl⟩ - ⟨j, rfl⟩
  exact b.lie_h_h i j

include b in
theorem isLieAbelian_cartan : IsLieAbelian H := by
  rw [b.cartan_eq_lieSpan, isLieAbelian_lieSpan_iff]
  rintro - ⟨i, rfl⟩ - ⟨j, rfl⟩
  exact b.lie_h_h i j

/-- A basis has a natural involution obtained by interchanging the roles of `e` and `f` and
negating `h`. -/
@[simps -fullyApplied] def symm : Basis ι H where
  A := b.A
  h := -b.h
  e := b.f
  f := b.e
  cartan_eq_lieSpan := by
    rw [← neg_range', lieSpan_neg]
    exact b.cartan_eq_lieSpan
  nondegen := b.nondegen
  linInd := b.linInd.neg
  sl2 i := (b.sl2 i).symm
  lie_h_h i j := by rw [Pi.neg_apply, Pi.neg_apply, neg_lie, lie_neg, b.lie_h_h i j, neg_neg]
  lie_h_e i j := by rw [Pi.neg_apply, neg_lie, b.lie_h_f i j, neg_smul, neg_neg]
  lie_h_f i j := by rw [Pi.neg_apply, neg_lie, b.lie_h_e, neg_smul]
  lie_e_f_ne i j h := by rw [← lie_skew, neg_eq_zero, b.lie_e_f_ne j i h.symm]
  span_ef := by rw [union_comm, b.span_ef]

@[simp] lemma symm_symm : b.symm.symm = b := by aesop

/-- As shown in `LieAlgebra.Basis.coroot_eq_h'` this is a coroot. -/
def h' (i : ι) : H := ⟨b.h i, b.cartan_eq_lieSpan ▸ subset_lieSpan <| mem_range_self i⟩

@[simp] lemma symm_h' (i : ι) : (b.symm.h' i) = -b.h' i := rfl

private lemma cartan_lie_mem_lieSpan_e {x y : L}
    (hx : x ∈ H) (hy : y ∈ lieSpan R L (range b.e)) :
    ⁅x, y⁆ ∈ lieSpan R L (range b.e) := by
  induction hy using lieSpan_induction with
  | mem u hu =>
    obtain ⟨i, rfl⟩ := hu
    rw [← mem_toSubmodule, b.coe_cartan_eq_span] at hx
    induction hx using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨j, rfl⟩ := hv
      rw [b.lie_h_e]
      apply zsmul_mem <| subset_lieSpan <| mem_range_self i
    | zero => simp
    | add v w _ _ hv hw => simpa using add_mem hv hw
    | smul t v _ hv => simpa using LieSubalgebra.smul_mem _ t hv
  | zero => simp
  | add u v _ _ hu hv => simpa using add_mem hu hv
  | smul t u _ hu => simpa using LieSubalgebra.smul_mem _ t hu
  | lie u v hu hv hu' hv' =>
    rw [leibniz_lie, ← lie_skew _ v, neg_add_eq_sub]
    exact sub_mem (LieSubalgebra.lie_mem _ hu hv') (LieSubalgebra.lie_mem _ hv hu')

/-- The nilpotent part of the "upper" Borel subalgebra associated to a basis. -/
def borelUpper : LieSubmodule R H L where
  __ := lieSpan R L <| range b.e
  lie_mem {x y} hy := by
    obtain ⟨x, hx⟩ := x
    simpa using b.cartan_lie_mem_lieSpan_e hx hy

/-- The nilpotent part of the "lower" Borel subalgebra associated to a basis. -/
def borelLower : LieSubmodule R H L where
  __ := lieSpan R L <| range b.f
  lie_mem := b.symm.borelUpper.lie_mem

private lemma iSup_cartan_borelLower_borelUpper_eq_top_aux
    {y z : L} (hy : y ∈ lieSpan R L (range b.e)) (hz : z ∈ lieSpan R L (range b.f)) :
    ⁅y, z⁆ ∈ H.toLieSubmodule ⊔ b.borelLower ⊔ b.borelUpper := by
  have (i : ι) (x : L) (hx : x ∈ lieSpan R L (range b.f)) :
      ⁅b.e i, x⁆ ∈ H.toLieSubmodule ⊔ b.borelLower := by
    induction hx using LieSubalgebra.lieSpan_induction with
    | mem u hu =>
      obtain ⟨j, rfl⟩ := hu
      rcases eq_or_ne i j with rfl | hij
      · rw [(b.sl2 i).lie_e_f]
        apply LieSubmodule.mem_sup_left
        nth_rw 1 [mem_toLieSubmodule, b.cartan_eq_lieSpan]
        exact LieSubalgebra.subset_lieSpan <| mem_range_self i
      · simp [b.lie_e_f_ne _ _ hij]
    | zero => simp
    | add u v _ _ hu hv => rw [lie_add]; exact add_mem hu hv
    | smul t u _ hu => rw [lie_smul]; exact SMulMemClass.smul_mem t hu
    | lie u v hu hv hu' hv' =>
      obtain ⟨w₁, hw₁, w₂, hw₂, hwu⟩ : ∃ y ∈ H, ∃ z ∈ b.borelLower, y + z = ⁅b.e i, u⁆ := by
        simpa only [LieSubmodule.mem_sup] using! hu'
      obtain ⟨w₃, hw₃, w₄, hw₄, hwv⟩ : ∃ y ∈ H, ∃ z ∈ b.borelLower, y + z = ⁅b.e i, v⁆ := by
        simpa only [LieSubmodule.mem_sup] using! hv'
      rw [leibniz_lie, ← hwu, ← hwv, lie_add, add_lie, ← add_assoc]
      repeat apply add_mem
      · exact LieSubmodule.mem_sup_right <| b.borelLower.lie_mem (x := ⟨w₁, hw₁⟩) hv
      · exact LieSubmodule.mem_sup_right <| LieSubalgebra.lie_mem _ hw₂ hv
      · rw [← lie_skew, neg_mem_iff]
        exact LieSubmodule.mem_sup_right <| b.borelLower.lie_mem (x := ⟨w₃, hw₃⟩) hu
      · rw [← lie_skew, neg_mem_iff]
        exact LieSubmodule.mem_sup_right <| LieSubalgebra.lie_mem _ hw₄ hu
  induction hy using lieSpan_induction generalizing z with
  | mem u hu =>
    obtain ⟨i, rfl⟩ := hu
    exact LieSubmodule.mem_sup_left <| this i z hz
  | zero => simp
  | add u v _ _ hu hv => rw [add_lie]; exact add_mem (hu hz) (hv hz)
  | smul t u _ hu => rw [smul_lie]; exact SMulMemClass.smul_mem t (hu hz)
  | lie u v hu hv hu' hv' =>
    rw [lie_lie]
    apply sub_mem
    · obtain ⟨yc, hyc, yl, hyl, yu, hyu, aux⟩ :
        ∃ᵉ (yc ∈ H) (yl ∈ lieSpan R L (range b.f)) (yu ∈ lieSpan R L (range b.e)),
        yc + yl + yu = ⁅v, z⁆ := by simpa [LieSubmodule.mem_sup] using! hv' hz
      simp only [← aux, lie_add]
      repeat apply add_mem
      · rw [← lie_skew, neg_mem_iff]
        exact LieSubmodule.mem_sup_right <| b.borelUpper.lie_mem (x := ⟨yc, hyc⟩) hu
      · exact hu' hyl
      · rw [← lie_skew, neg_mem_iff]
        exact LieSubmodule.mem_sup_right <| LieSubalgebra.lie_mem _ hyu hu
    · obtain ⟨yc, hyc, yl, hyl, yu, hyu, aux⟩ :
        ∃ᵉ (yc ∈ H) (yl ∈ lieSpan R L (range b.f)) (yu ∈ lieSpan R L (range b.e)),
        yc + yl + yu = ⁅u, z⁆ := by simpa [LieSubmodule.mem_sup] using! hu' hz
      simp only [← aux, lie_add]
      repeat apply add_mem
      · rw [← lie_skew, neg_mem_iff]
        exact LieSubmodule.mem_sup_right <| b.borelUpper.lie_mem (x := ⟨yc, hyc⟩) hv
      · exact hv' hyl
      · rw [← lie_skew, neg_mem_iff]
        exact LieSubmodule.mem_sup_right <| LieSubalgebra.lie_mem _ hyu hv

/-- Lemma 4.5 from [Geck](Geck2017). -/
lemma iSup_cartan_borelLower_borelUpper_eq_top :
    iSup ![H.toLieSubmodule, b.borelLower, b.borelUpper] = ⊤ := by
  suffices H.toLieSubmodule ⊔ b.borelLower ⊔ b.borelUpper = ⊤ by simpa
  refine eq_top_iff.mpr fun x hx ↦ ?_
  replace hx : x ∈ lieSpan R L (range b.e ∪ range b.f) := by simp [b.span_ef]
  induction hx using lieSpan_induction with
  | mem u hu =>
    rcases (mem_union _ _ _).mpr hu with hu | hu
    · exact LieSubmodule.mem_sup_right <| subset_lieSpan hu
    · exact LieSubmodule.mem_sup_left <| LieSubmodule.mem_sup_right <| subset_lieSpan hu
  | zero => simp
  | add u v _ _ hu hv => exact add_mem hu hv
  | smul t u _ hu => exact SMulMemClass.smul_mem t hu
  | lie u v _ _ hu hv =>
    obtain ⟨yc, hyc, yl, hyl, yu, hyu, rfl⟩ :
        ∃ᵉ (yc ∈ H) (yl ∈ lieSpan R L (range b.f)) (yu ∈ lieSpan R L (range b.e)),
          yc + yl + yu = u := by simpa [LieSubmodule.mem_sup] using! hu
    obtain ⟨zc, hzc, zl, hzl, zu, hzu, rfl⟩ :
        ∃ᵉ (zc ∈ H) (zl ∈ lieSpan R L (range b.f)) (zu ∈ lieSpan R L (range b.e)),
          zc + zl + zu = v := by simpa [LieSubmodule.mem_sup] using! hv
    simp only [lie_add, add_lie, ← add_assoc]
    repeat apply add_mem
    · exact LieSubmodule.mem_sup_left <| LieSubmodule.mem_sup_left <| lie_mem _ hyc hzc
    · rw [← lie_skew, neg_mem_iff]
      exact LieSubmodule.mem_sup_left <| LieSubmodule.mem_sup_right <|
        b.borelLower.lie_mem (x := ⟨zc, hzc⟩) hyl
    · rw [← lie_skew, neg_mem_iff]
      exact LieSubmodule.mem_sup_right <| b.borelUpper.lie_mem (x := ⟨zc, hzc⟩) hyu
    · exact LieSubmodule.mem_sup_left <| LieSubmodule.mem_sup_right <|
        b.borelLower.lie_mem (x := ⟨yc, hyc⟩) hzl
    · exact LieSubmodule.mem_sup_left <| LieSubmodule.mem_sup_right <| lie_mem _ hyl hzl
    · exact b.iSup_cartan_borelLower_borelUpper_eq_top_aux hyu hzl
    · exact LieSubmodule.mem_sup_right <| b.borelUpper.lie_mem (x := ⟨yc, hyc⟩) hzu
    · rw [← lie_skew, neg_mem_iff]
      exact b.iSup_cartan_borelLower_borelUpper_eq_top_aux hzu hyl
    · exact LieSubmodule.mem_sup_right <| lie_mem _ hyu hzu

variable [Fintype ι]

/-- These elements constitute a base for the root system of the Lie algebra relative to the
associated Cartan subalgebra. -/
def baseSupp (i : ι) : Dual R H :=
  ∑ j, b.A i j •
    ((Basis.span b.linInd).map (LinearEquiv.ofEq _ _ b.coe_cartan_eq_span).symm).coord j

@[simp] lemma baseSupp_apply_h' (i j : ι) :
    b.baseSupp i (b.h' j) = b.A i j := by
  classical
  simp only [baseSupp, LinearMap.coe_sum, Finset.sum_apply]
  let e := LinearEquiv.ofEq _ _ b.coe_cartan_eq_span
  let f (k : ι) : R := b.A i k • (Basis.span b.linInd).repr (e <| b.h' j) k
  change ∑ k, f k = _
  have : f = fun k ↦ if j = k then (b.A i k : R) else 0 := by
    have : (Basis.span b.linInd).repr (e <| b.h' j) = .single j 1 := Basis.span_repr_eq_single _ _
    ext k
    simp [f, this, Finsupp.single_apply]
  simp [this]

set_option backward.isDefEq.respectTransparency.types false in
@[simp] lemma symm_baseSupp :
    b.symm.baseSupp = -b.baseSupp := by
  let b₁ : Module.Basis ι R H :=
    (Basis.span b.linInd).map (LinearEquiv.ofEq _ _ b.coe_cartan_eq_span).symm
  let b₂ : Module.Basis ι R H :=
    (Basis.span b.linInd.neg).map (LinearEquiv.ofEq _ _ b.symm.coe_cartan_eq_span).symm
  suffices b₁.coord = -b₂.coord by
    ext1 i
    change ∑ j, b.A i j • b₂.coord j = - ∑ j, b.A i j • b₁.coord j
    simp [this]
  simp only [b₁, b₂, Basis.span_neg b.linInd]
  aesop

lemma linearIndependent_baseSupp [IsDomain R] [CharZero R] :
    LinearIndependent R b.baseSupp := by
  classical
  have : ((Int.castRingHom R).mapMatrix b.A).Nondegenerate := by
    rw [Matrix.nondegenerate_iff_det_ne_zero, ← RingHom.map_det]
    simpa using! b.nondegen.det_ne_zero
  let v : ι → Dual R H :=
    ((Basis.span b.linInd).map (LinearEquiv.ofEq _ _ b.coe_cartan_eq_span).symm).coord
  have hv : LinearIndependent R v := Basis.linearIndependent_coord _
  simpa [Int.cast_smul_eq_zsmul] using! hv.sum_smul_of_nondegenerate this

@[simp] lemma baseSupp_apply_smul_e (i : ι) (x : H) :
    b.baseSupp i x • b.e i = ⁅x, b.e i⁆ := by
  obtain ⟨x, hx⟩ := x
  simp only [coe_bracket_of_module]
  have hx' : x ∈ Submodule.span R (range b.h) := by
    rwa [← LieSubalgebra.mem_toSubmodule, b.coe_cartan_eq_span] at hx
  induction hx' using Submodule.span_induction with
  | mem u hu =>
    obtain ⟨j, rfl⟩ := hu
    change b.baseSupp i (b.h' j) • _ = _
    simp [b.lie_h_e, Int.cast_smul_eq_zsmul]
  | zero => change b.baseSupp i 0 • _ = _; simp
  | add u v hu hv hu' hv' =>
    rw [← coe_cartan_eq_span, LieSubalgebra.mem_toSubmodule] at hu hv
    rw [← AddMemClass.mk_add_mk _ u v hu hv]
    simp only [map_add, add_smul, add_lie] at hu' hv' ⊢
    rw [hu', hv']
  | smul t u hu hv' =>
    rw [← coe_cartan_eq_span, LieSubalgebra.mem_toSubmodule] at hu
    rw [← SetLike.mk_smul_mk _ t u hu, map_smul, smul_assoc, hv', smul_lie]

@[simp] lemma baseSupp_apply_smul_f (i : ι) (x : H) :
    b.baseSupp i x • b.f i = -⁅x, b.f i⁆ := by
  rw [← neg_eq_iff_eq_neg, ← neg_smul, ← LinearMap.neg_apply]
  have := b.symm.baseSupp_apply_smul_e i x
  simp only [symm_baseSupp, Pi.neg_apply, symm_e] at this
  exact this

variable [IsDomain R] [CharZero R]

set_option backward.isDefEq.respectTransparency.types false in
/-- Lemma 4.4 from [Geck](Geck2017). -/
lemma borelUpper_le_biSup :
    letI := b.isLieAbelian_cartan
    b.borelUpper ≤ ⨆ (n : ι → ℕ) (_ : n ≠ 0), rootSpace H (∑ i, n i • b.baseSupp i) := by
  let := b.isLieAbelian_cartan
  classical
  intro x hx
  replace hx : x ∈ lieSpan R L (range b.e) := by simpa [borelUpper] using hx
  induction hx using lieSpan_induction with
  | mem u hu =>
    obtain ⟨i, rfl⟩ := hu
    apply LieSubmodule.mem_iSup_of_mem (Pi.single i 1)
    simp only [ne_eq, Pi.single_eq_zero_iff, one_ne_zero, not_false_eq_true, nsmul_eq_mul, iSup_pos,
      LieModule.mem_genWeightSpace, Finset.sum_apply, Pi.mul_apply, Pi.natCast_apply,
      Subtype.forall, toEnd_mk]
    exact fun y hy ↦ ⟨1, by simp [Pi.single_apply]⟩
  | zero => simp
  | add _ _ _ _ hu hv => exact add_mem hu hv
  | smul t _ _ hu => exact SMulMemClass.smul_mem t hu
  | lie u v _ _ hu hv =>
    let s : Set (H → R) := {χ | ∃ n : ι → ℕ, n ≠ 0 ∧ χ = ∑ i, n i • b.baseSupp i}
    have hs : ∀ χ₁ ∈ s, ∀ χ₂ ∈ s, χ₁ + χ₂ ∈ s := by
      rintro - ⟨n₁, hn₁, rfl⟩ - ⟨n₂, hn₂, rfl⟩
      refine ⟨n₁ + n₂, by simp [hn₁], ?_⟩
      ext; simp [add_smul, Finset.sum_add_distrib]
    let e : {n : ι → ℕ | n ≠ 0} ≃ s :=
      .ofBijective (fun n ↦ ⟨∑ i, n.val i • b.baseSupp i, n.val, n.property, by ext; simp⟩) <| by
      refine ⟨fun n₁ n₂ h ↦ ?_, fun χ ↦ ?_⟩
      · ext i
        have := b.linearIndependent_baseSupp.restrict_scalars' ℕ
        refine Fintype.linearIndependent_iffₛ.mp this n₁ n₂ ?_ i
        ext v
        rw [Subtype.mk.injEq] at h
        simpa using congr_fun h v
      · use ⟨χ.property.choose, χ.property.choose_spec.1⟩
        ext i
        simpa using congr_fun χ.property.choose_spec.2.symm i
    replace hu : u ∈ ⨆ χ, ⨆ (_ : χ ∈ s), rootSpace H χ := by
      convert! hu; rw [iSup_subtype', iSup_subtype', ← e.iSup_comp]; rfl
    replace hv : v ∈ ⨆ χ, ⨆ (_ : χ ∈ s), rootSpace H χ := by
      convert! hv; rw [iSup_subtype', iSup_subtype', ← e.iSup_comp]; rfl
    convert! mem_biSup_genWeightSpace_of hs hu hv
    rw [iSup_subtype', iSup_subtype', ← e.iSup_comp]; rfl

/-- Lemma 4.4 from [Geck](Geck2017). -/
lemma borelLower_le_biSup :
    letI := b.isLieAbelian_cartan
    b.borelLower ≤ ⨆ (n : ι → ℕ) (_ : n ≠ 0), rootSpace H (∑ i, n i • (-b.baseSupp) i) := by
  simpa only [symm_baseSupp] using! b.symm.borelUpper_le_biSup

private lemma cartan_borelLower_borelUpper_le :
    letI := b.isLieAbelian_cartan
    letI U := ⨆ (n : ι → ℕ) (_ : n ≠ 0), rootSpace H (∑ i, n i • (-b.baseSupp) i)
    letI V := ⨆ (n : ι → ℕ) (_ : n ≠ 0), rootSpace H (∑ i, n i • b.baseSupp i)
    ![H.toLieSubmodule, b.borelLower, b.borelUpper] ≤ ![rootSpace H 0, U, V] := by
  let := b.isLieAbelian_cartan
  intro i
  fin_cases i
  · exact toLieSubmodule_le_rootSpace_zero R L H
  · exact b.borelLower_le_biSup
  · exact b.borelUpper_le_biSup

variable [IsTorsionFree R L]

set_option backward.isDefEq.respectTransparency.types false in
lemma iSupIndep_rootSpace :
    letI := b.isLieAbelian_cartan
    letI U := ⨆ (n : ι → ℕ) (_ : n ≠ 0), rootSpace H (∑ i, n i • (-b.baseSupp) i)
    letI V := ⨆ (n : ι → ℕ) (_ : n ≠ 0), rootSpace H (∑ i, n i • b.baseSupp i)
    iSupIndep ![rootSpace H 0, U, V] := by
  let := b.isLieAbelian_cartan
  set U := ⨆ (n : ι → ℕ) (_ : n ≠ 0), rootSpace H (∑ i, n i • (-b.baseSupp) i) with hU
  set V := ⨆ (n : ι → ℕ) (_ : n ≠ 0), rootSpace H (∑ i, n i • b.baseSupp i) with hV
  set s0 : Set (H → R) := {0} with hs0
  set sU : Set (H → R) := {f | ∃ n : ι → ℕ, n ≠ 0 ∧ f = ∑ i, n i • (-b.baseSupp) i} with hsU
  set sV : Set (H → R) := {f | ∃ n : ι → ℕ, n ≠ 0 ∧ f = ∑ i, n i • b.baseSupp i} with hsV
  have hs0' : rootSpace H 0 = ⨆ i ∈ s0, LieModule.genWeightSpace L i := by simp [hs0]
  have hsU' : U = ⨆ i ∈ sU, LieModule.genWeightSpace L i := by
    simp only [hU, hsU, mem_ofPred_eq, iSup_exists, iSup_and, iSup_comm (ι := H → R),
      iSup_iSup_eq_left, LinearMap.coe_sum, LinearMap.coe_smul]
  have hsV' : V = ⨆ i ∈ sV, LieModule.genWeightSpace L i := by
    simp only [hV, hsV, mem_ofPred_eq, iSup_exists, iSup_and, iSup_comm (ι := H → R),
      iSup_iSup_eq_left, LinearMap.coe_sum, LinearMap.coe_smul]
  have hU0 : Disjoint s0 sU := by
    suffices ∀ g ∈ sU, g ≠ 0 by
      refine Set.disjoint_iff_forall_ne.mpr fun f hf g hg ↦ ?_
      obtain ⟨rfl⟩ : f = 0 := by simpa [hs0] using hf
      exact (this _ hg).symm
    intro g hg contra
    obtain ⟨n, hn, rfl⟩ : ∃ n : ι → ℕ, n ≠ 0 ∧ g = -∑ i, n i • b.baseSupp i := by
      simpa [hsU] using hg
    rw [neg_eq_zero, LinearMap.coe_zero_iff] at contra
    have := Fintype.linearIndependent_iff.mp b.linearIndependent_baseSupp ((↑) ∘ n)
      (by simpa [Nat.cast_smul_eq_nsmul])
    exact hn <| funext fun i ↦ by simpa using this i
  have hV0 : Disjoint s0 sV := by
    suffices ∀ g ∈ sV, g ≠ 0 by
      refine Set.disjoint_iff_forall_ne.mpr fun f hf g hg ↦ ?_
      obtain ⟨rfl⟩ : f = 0 := by simpa [hs0] using hf
      exact (this _ hg).symm
    intro g hg contra
    obtain ⟨n, hn, rfl⟩ : ∃ n : ι → ℕ, n ≠ 0 ∧ g = ∑ i, n i • b.baseSupp i := by
      simpa [hsV] using hg
    rw [LinearMap.coe_zero_iff] at contra
    have := Fintype.linearIndependent_iff.mp b.linearIndependent_baseSupp ((↑) ∘ n)
      (by simpa [Nat.cast_smul_eq_nsmul])
    exact hn <| funext fun i ↦ by simpa using this i
  have hUV : Disjoint sU sV := by
    refine Set.disjoint_iff_forall_ne.mpr fun f hf g hg ↦ ?_
    rintro rfl
    obtain ⟨n, hn, hn'⟩ : ∃ n : ι → ℕ, n ≠ 0 ∧ f = -∑ i, n i • b.baseSupp i := by
      simpa [hsU] using hf
    obtain ⟨m, hm, rfl⟩ : ∃ m : ι → ℕ, m ≠ 0 ∧ f = ∑ i, m i • b.baseSupp i := by
      simpa [hsV] using hg
    replace hn' : ∑ i, (((↑) : ℕ → R) ∘ (m + n)) i • b.baseSupp i = 0 := by
      rw [eq_neg_iff_add_eq_zero] at hn'
      change ⇑(∑ i, m i • b.baseSupp i + ∑ i, n i • b.baseSupp i) = 0 at hn'
      simp_rw [LinearMap.coe_zero_iff, ← Finset.sum_add_distrib, ← add_smul, ← Pi.add_apply,
        ← Nat.cast_smul_eq_nsmul R] at hn'
      exact hn'
    have := Fintype.linearIndependent_iff.mp b.linearIndependent_baseSupp ((↑) ∘ (m + n)) hn'
    refine hn <| funext fun i ↦ ?_
    specialize this i
    rw [comp_apply, Nat.cast_eq_zero, Pi.add_apply, Nat.add_eq_zero_iff] at this
    simpa using this.2
  have key := LieModule.iSupIndep_genWeightSpace R H L
  have h₀ : Disjoint (rootSpace H 0) (U ⊔ V) := by
    convert! key.disjoint_biSup_biSup (hU0.union_right hV0)
    rw [iSup_union, hsU', hsV']
  have h₁ : Disjoint U (V ⊔ rootSpace H 0) := by
    convert! key.disjoint_biSup_biSup (hUV.union_right hU0.symm)
    rw [iSup_union, hs0', hsV']
  have h₂ : Disjoint V (rootSpace H 0 ⊔ U) := by
    convert! key.disjoint_biSup_biSup (Disjoint.union_left hV0 hUV).symm
    rw [iSup_union, hs0', hsU']
  simp [iSupIndep_fin_three, h₀, h₁, h₂]

set_option linter.unusedFintypeInType false in
lemma cartan_eq :
    letI := b.isLieAbelian_cartan
    H.toLieSubmodule = rootSpace H 0 :=
  congr_fun ((b.iSupIndep_rootSpace.le_iff_eq_of_iSup_eq_top
    b.iSup_cartan_borelLower_borelUpper_eq_top).mp b.cartan_borelLower_borelUpper_le) 0

lemma borelLower_eq :
    letI := b.isLieAbelian_cartan
    b.borelLower = ⨆ (n : ι → ℕ) (_ : n ≠ 0), rootSpace H (∑ i, n i • (-b.baseSupp) i) :=
  congr_fun ((b.iSupIndep_rootSpace.le_iff_eq_of_iSup_eq_top
    b.iSup_cartan_borelLower_borelUpper_eq_top).mp b.cartan_borelLower_borelUpper_le) 1

lemma borelUpper_eq :
    letI := b.isLieAbelian_cartan
    b.borelUpper = ⨆ (n : ι → ℕ) (_ : n ≠ 0), rootSpace H (∑ i, n i • b.baseSupp i) :=
  congr_fun ((b.iSupIndep_rootSpace.le_iff_eq_of_iSup_eq_top
    b.iSup_cartan_borelLower_borelUpper_eq_top).mp b.cartan_borelLower_borelUpper_le) 2

set_option linter.unusedFintypeInType false in
include b in
lemma isCartanSubalgebra [IsNoetherian R L] : H.IsCartanSubalgebra := by
  let := b.isLieAbelian_cartan
  rw [← eq_rootSpace_zero_iff_isCartan, b.cartan_eq]

end CommRing

end Basis

end LieAlgebra
