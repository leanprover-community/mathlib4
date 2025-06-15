/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import Mathlib.Algebra.Polynomial.GroupRingAction
import Mathlib.Algebra.Ring.Action.Field
import Mathlib.Algebra.Ring.Action.Invariant
import Mathlib.FieldTheory.Finiteness
import Mathlib.FieldTheory.Normal.Defs
import Mathlib.FieldTheory.Separable
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix

/-!
# Fixed field under a group action.

This is the basis of the Fundamental Theorem of Galois Theory.
Given a (finite) group `G` that acts on a field `F`, we define `FixedPoints.subfield G F`,
the subfield consisting of elements of `F` fixed_points by every element of `G`.

This subfield is then normal and separable, and in addition if `G` acts faithfully on `F`
then `finrank (FixedPoints.subfield G F) F = Fintype.card G`.

## Main Definitions

- `FixedPoints.subfield G F`, the subfield consisting of elements of `F` fixed_points by every
element of `G`, where `G` is a group that acts on `F`.

-/


noncomputable section

open MulAction Finset Module

universe u v w

variable {M : Type u} [Monoid M]
variable (G : Type u) [Group G]
variable (F : Type v) [Field F] [MulSemiringAction M F] [MulSemiringAction G F] (m : M)

/-- The subfield of F fixed by the field endomorphism `m`. -/
def FixedBy.subfield : Subfield F where
  carrier := fixedBy F m
  zero_mem' := smul_zero m
  add_mem' hx hy := (smul_add m _ _).trans <| congr_arg₂ _ hx hy
  neg_mem' hx := (smul_neg m _).trans <| congr_arg _ hx
  one_mem' := smul_one m
  mul_mem' hx hy := (smul_mul' m _ _).trans <| congr_arg₂ _ hx hy
  inv_mem' x hx := (smul_inv'' m x).trans <| congr_arg _ hx

section InvariantSubfields

variable (M) {F}

/-- A typeclass for subrings invariant under a `MulSemiringAction`. -/
class IsInvariantSubfield (S : Subfield F) : Prop where
  smul_mem : ∀ (m : M) {x : F}, x ∈ S → m • x ∈ S

variable (S : Subfield F)

instance IsInvariantSubfield.toMulSemiringAction [IsInvariantSubfield M S] :
    MulSemiringAction M S where
  smul m x := ⟨m • x.1, IsInvariantSubfield.smul_mem m x.2⟩
  one_smul s := Subtype.eq <| one_smul M s.1
  mul_smul m₁ m₂ s := Subtype.eq <| mul_smul m₁ m₂ s.1
  smul_add m s₁ s₂ := Subtype.eq <| smul_add m s₁.1 s₂.1
  smul_zero m := Subtype.eq <| smul_zero m
  smul_one m := Subtype.eq <| smul_one m
  smul_mul m s₁ s₂ := Subtype.eq <| smul_mul' m s₁.1 s₂.1

instance [IsInvariantSubfield M S] : IsInvariantSubring M S.toSubring where
  smul_mem := IsInvariantSubfield.smul_mem

end InvariantSubfields

namespace FixedPoints

variable (M)

-- we use `Subfield.copy` so that the underlying set is `fixedPoints M F`
/-- The subfield of fixed points by a monoid action. -/
def subfield : Subfield F :=
  Subfield.copy (⨅ m : M, FixedBy.subfield F m) (fixedPoints M F)
    (by ext z; simp [fixedPoints, FixedBy.subfield, iInf, Subfield.mem_sInf]; rfl)

instance : IsInvariantSubfield M (FixedPoints.subfield M F) where
  smul_mem g x hx g' := by rw [hx, hx]

instance : SMulCommClass M (FixedPoints.subfield M F) F where
  smul_comm m f f' := show m • (↑f * f') = f * m • f' by rw [smul_mul', f.prop m]

instance smulCommClass' : SMulCommClass (FixedPoints.subfield M F) M F :=
  SMulCommClass.symm _ _ _

@[simp]
theorem smul (m : M) (x : FixedPoints.subfield M F) : m • x = x :=
  Subtype.eq <| x.2 m

-- Why is this so slow?
@[simp]
theorem smul_polynomial (m : M) (p : Polynomial (FixedPoints.subfield M F)) : m • p = p :=
  Polynomial.induction_on p (fun x => by rw [Polynomial.smul_C, smul])
    (fun p q ihp ihq => by rw [smul_add, ihp, ihq]) fun n x _ => by
    rw [smul_mul', Polynomial.smul_C, smul, smul_pow', Polynomial.smul_X]

instance : Algebra (FixedPoints.subfield M F) F := by infer_instance

theorem coe_algebraMap :
    algebraMap (FixedPoints.subfield M F) F = Subfield.subtype (FixedPoints.subfield M F) :=
  rfl

theorem linearIndependent_smul_of_linearIndependent {s : Finset F} :
    (LinearIndepOn (FixedPoints.subfield G F) id (s : Set F)) →
      LinearIndepOn F (MulAction.toFun G F) s := by
  classical
  have : IsEmpty ((∅ : Finset F) : Set F) := by simp
  refine Finset.induction_on s (fun _ => linearIndependent_empty_type) fun a s has ih hs => ?_
  rw [coe_insert] at hs ⊢
  rw [linearIndepOn_insert (mt mem_coe.1 has)] at hs
  rw [linearIndepOn_insert (mt mem_coe.1 has)]; refine ⟨ih hs.1, fun ha => ?_⟩
  rw [Finsupp.mem_span_image_iff_linearCombination] at ha; rcases ha with ⟨l, hl, hla⟩
  rw [Finsupp.linearCombination_apply_of_mem_supported F hl] at hla
  suffices ∀ i ∈ s, l i ∈ FixedPoints.subfield G F by
    replace hla := (sum_apply _ _ fun i => l i • toFun G F i).symm.trans (congr_fun hla 1)
    simp_rw [Pi.smul_apply, toFun_apply, one_smul] at hla
    refine hs.2 (hla ▸ Submodule.sum_mem _ fun c hcs => ?_)
    change (⟨l c, this c hcs⟩ : FixedPoints.subfield G F) • c ∈ _
    exact Submodule.smul_mem _ _ <| Submodule.subset_span <| by simpa
  intro i his g
  refine
    eq_of_sub_eq_zero
      (linearIndependent_iff'.1 (ih hs.1) s.attach (fun i => g • l i - l i) ?_ ⟨i, his⟩
          (mem_attach _ _) :
        _)
  refine (sum_attach s fun i ↦ (g • l i - l i) • MulAction.toFun G F i).trans ?_
  ext g'; dsimp only
  conv_lhs =>
    rw [sum_apply]
    congr
    · skip
    · ext
      rw [Pi.smul_apply, sub_smul, smul_eq_mul]
  rw [sum_sub_distrib, Pi.zero_apply, sub_eq_zero]
  conv_lhs =>
    congr
    · skip
    · ext x
      rw [toFun_apply, ← mul_inv_cancel_left g g', mul_smul, ← smul_mul', ← toFun_apply _ x]
  show
    (∑ x ∈ s, g • (fun y => l y • MulAction.toFun G F y) x (g⁻¹ * g')) =
      ∑ x ∈ s, (fun y => l y • MulAction.toFun G F y) x g'
  rw [← smul_sum, ← sum_apply _ _ fun y => l y • toFun G F y, ←
    sum_apply _ _ fun y => l y • toFun G F y]
  rw [hla, toFun_apply, toFun_apply, smul_smul, mul_inv_cancel_left]

section Fintype

variable [Fintype G] (x : F)

/-- `minpoly G F x` is the minimal polynomial of `(x : F)` over `FixedPoints.subfield G F`. -/
def minpoly : Polynomial (FixedPoints.subfield G F) :=
  (prodXSubSMul G F x).toSubring (FixedPoints.subfield G F).toSubring fun _ hc g =>
    let ⟨n, _, hn⟩ := Polynomial.mem_coeffs_iff.1 hc
    hn.symm ▸ prodXSubSMul.coeff G F x g n

namespace minpoly

theorem monic : (minpoly G F x).Monic := by
  simp only [minpoly]
  rw [Polynomial.monic_toSubring]
  exact prodXSubSMul.monic G F x

theorem eval₂ :
    Polynomial.eval₂ (Subring.subtype <| (FixedPoints.subfield G F).toSubring) x (minpoly G F x) =
      0 := by
  rw [← prodXSubSMul.eval G F x, Polynomial.eval₂_eq_eval_map]
  simp only [minpoly, Polynomial.map_toSubring]

theorem eval₂' :
    Polynomial.eval₂ (Subfield.subtype <| FixedPoints.subfield G F) x (minpoly G F x) = 0 :=
  eval₂ G F x

theorem ne_one : minpoly G F x ≠ (1 : Polynomial (FixedPoints.subfield G F)) := fun H =>
  have := eval₂ G F x
  (one_ne_zero : (1 : F) ≠ 0) <| by rwa [H, Polynomial.eval₂_one] at this

theorem of_eval₂ (f : Polynomial (FixedPoints.subfield G F))
    (hf : Polynomial.eval₂ (Subfield.subtype <| FixedPoints.subfield G F) x f = 0) :
    minpoly G F x ∣ f := by
  classical
  rw [← Polynomial.map_dvd_map' (Subfield.subtype <| FixedPoints.subfield G F), minpoly,
    ← Subfield.toSubring_subtype_eq_subtype, Polynomial.map_toSubring _ _, prodXSubSMul]
  refine
    Fintype.prod_dvd_of_coprime
      (Polynomial.pairwise_coprime_X_sub_C <| MulAction.injective_ofQuotientStabilizer G x) fun y =>
      QuotientGroup.induction_on y fun g => ?_
  rw [Polynomial.dvd_iff_isRoot, Polynomial.IsRoot.def, MulAction.ofQuotientStabilizer_mk,
    Polynomial.eval_smul',
    ← IsInvariantSubring.coe_subtypeHom' G (FixedPoints.subfield G F).toSubring,
    ← MulSemiringActionHom.coe_polynomial, ← MulSemiringActionHom.map_smul, smul_polynomial,
    MulSemiringActionHom.coe_polynomial, IsInvariantSubring.coe_subtypeHom',
    Polynomial.eval_map, Subfield.toSubring_subtype_eq_subtype, hf, smul_zero]

-- Why is this so slow?
theorem irreducible_aux (f g : Polynomial (FixedPoints.subfield G F)) (hf : f.Monic) (hg : g.Monic)
    (hfg : f * g = minpoly G F x) : f = 1 ∨ g = 1 := by
  have hf2 : f ∣ minpoly G F x := by rw [← hfg]; exact dvd_mul_right _ _
  have hg2 : g ∣ minpoly G F x := by rw [← hfg]; exact dvd_mul_left _ _
  have := eval₂ G F x
  rw [← hfg, Polynomial.eval₂_mul, mul_eq_zero] at this
  rcases this with this | this
  · right
    have hf3 : f = minpoly G F x :=
      Polynomial.eq_of_monic_of_associated hf (monic G F x)
        (associated_of_dvd_dvd hf2 <| @of_eval₂ G _ F _ _ _ x f this)
    rwa [← mul_one (minpoly G F x), hf3, mul_right_inj' (monic G F x).ne_zero] at hfg
  · left
    have hg3 : g = minpoly G F x :=
      Polynomial.eq_of_monic_of_associated hg (monic G F x)
        (associated_of_dvd_dvd hg2 <| @of_eval₂ G _ F _ _ _ x g this)
    rwa [← one_mul (minpoly G F x), hg3, mul_left_inj' (monic G F x).ne_zero] at hfg

theorem irreducible : Irreducible (minpoly G F x) :=
  (Polynomial.irreducible_of_monic (monic G F x) (ne_one G F x)).2 (irreducible_aux G F x)

end minpoly

end Fintype

theorem isIntegral [Finite G] (x : F) : IsIntegral (FixedPoints.subfield G F) x := by
  cases nonempty_fintype G; exact ⟨minpoly G F x, minpoly.monic G F x, minpoly.eval₂ G F x⟩

section Fintype

variable [Fintype G] (x : F)

theorem minpoly_eq_minpoly : minpoly G F x = _root_.minpoly (FixedPoints.subfield G F) x :=
  minpoly.eq_of_irreducible_of_monic (minpoly.irreducible G F x) (minpoly.eval₂ G F x)
    (minpoly.monic G F x)

theorem rank_le_card : Module.rank (FixedPoints.subfield G F) F ≤ Fintype.card G :=
  rank_le fun s hs => by
    simpa only [rank_fun', Cardinal.mk_coe_finset, Finset.coe_sort_coe, Cardinal.lift_natCast,
      Nat.cast_le] using
      (linearIndependent_smul_of_linearIndependent G F hs).cardinal_lift_le_rank

end Fintype

section Finite

variable [Finite G]

instance normal : Normal (FixedPoints.subfield G F) F where
  isAlgebraic x := (isIntegral G F x).isAlgebraic
  splits' x :=
    (Polynomial.splits_id_iff_splits _).1 <| by
      cases nonempty_fintype G
      rw [← minpoly_eq_minpoly, minpoly, coe_algebraMap, ← Subfield.toSubring_subtype_eq_subtype,
        Polynomial.map_toSubring _ (subfield G F).toSubring, prodXSubSMul]
      exact Polynomial.splits_prod _ fun _ _ => Polynomial.splits_X_sub_C _

instance isSeparable : Algebra.IsSeparable (FixedPoints.subfield G F) F := by
  classical
  exact ⟨fun x => by
    cases nonempty_fintype G
    rw [IsSeparable, ← minpoly_eq_minpoly,
      ← Polynomial.separable_map (FixedPoints.subfield G F).subtype, minpoly,
      ← Subfield.toSubring_subtype_eq_subtype, Polynomial.map_toSubring _ (subfield G F).toSubring]
    exact Polynomial.separable_prod_X_sub_C_iff.2 (injective_ofQuotientStabilizer G x)⟩

instance : FiniteDimensional (subfield G F) F := by
  cases nonempty_fintype G
  exact IsNoetherian.iff_fg.1
      (IsNoetherian.iff_rank_lt_aleph0.2 <| (rank_le_card G F).trans_lt <| Cardinal.nat_lt_aleph0 _)

end Finite

theorem finrank_le_card [Fintype G] : finrank (subfield G F) F ≤ Fintype.card G := by
  rw [← @Nat.cast_le Cardinal, finrank_eq_rank]
  apply rank_le_card

end FixedPoints

theorem linearIndependent_toLinearMap (R : Type u) (A : Type v) (B : Type w) [CommSemiring R]
    [Semiring A] [Algebra R A] [CommRing B] [IsDomain B] [Algebra R B] :
    LinearIndependent B (AlgHom.toLinearMap : (A →ₐ[R] B) → A →ₗ[R] B) :=
  have : LinearIndependent B (LinearMap.ltoFun R A B ∘ AlgHom.toLinearMap) :=
    ((linearIndependent_monoidHom A B).comp ((↑) : (A →ₐ[R] B) → A →* B) fun _ _ hfg =>
        AlgHom.ext fun _ => DFunLike.ext_iff.1 hfg _ :
      _)
  this.of_comp _

theorem cardinalMk_algHom (K : Type u) (V : Type v) (W : Type w) [Field K] [Ring V] [Algebra K V]
    [FiniteDimensional K V] [Field W] [Algebra K W] :
    Cardinal.mk (V →ₐ[K] W) ≤ finrank W (V →ₗ[K] W) :=
  (linearIndependent_toLinearMap K V W).cardinalMk_le_finrank

@[deprecated (since := "2024-11-10")] alias cardinal_mk_algHom := cardinalMk_algHom

noncomputable instance AlgEquiv.fintype (K : Type u) (V : Type v) [Field K] [Field V] [Algebra K V]
    [FiniteDimensional K V] : Fintype (V ≃ₐ[K] V) :=
  Fintype.ofEquiv (V →ₐ[K] V) (algEquivEquivAlgHom K V).symm

theorem finrank_algHom (K : Type u) (V : Type v) [Field K] [Field V] [Algebra K V]
    [FiniteDimensional K V] : Fintype.card (V →ₐ[K] V) ≤ finrank V (V →ₗ[K] V) :=
  (linearIndependent_toLinearMap K V V).fintype_card_le_finrank

theorem AlgHom.card_le {F K : Type*} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] :
    Fintype.card (K →ₐ[F] K) ≤ Module.finrank F K :=
  Module.finrank_linearMap_self F K K ▸ finrank_algHom F K

theorem AlgEquiv.card_le {F K : Type*} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] :
    Fintype.card (K ≃ₐ[F] K) ≤ Module.finrank F K :=
  Fintype.ofEquiv_card (algEquivEquivAlgHom F K).toEquiv.symm ▸ AlgHom.card_le

namespace FixedPoints

variable (G F : Type*) [Group G] [Field F] [MulSemiringAction G F]

/-- Let $F$ be a field. Let $G$ be a finite group acting faithfully on $F$.
Then $[F : F^G] = |G|$. -/
@[stacks 09I3 "second part"]
theorem finrank_eq_card [Fintype G] [FaithfulSMul G F] :
    finrank (FixedPoints.subfield G F) F = Fintype.card G :=
  le_antisymm (FixedPoints.finrank_le_card G F) <|
    calc
      Fintype.card G ≤ Fintype.card (F →ₐ[FixedPoints.subfield G F] F) :=
        Fintype.card_le_of_injective _ (MulSemiringAction.toAlgHom_injective _ F)
      _ ≤ finrank F (F →ₗ[FixedPoints.subfield G F] F) := finrank_algHom (subfield G F) F
      _ = finrank (FixedPoints.subfield G F) F := finrank_linearMap_self _ _ _

/-- `MulSemiringAction.toAlgHom` is bijective. -/
theorem toAlgHom_bijective [Finite G] [FaithfulSMul G F] :
    Function.Bijective (MulSemiringAction.toAlgHom _ _ : G → F →ₐ[subfield G F] F) := by
  cases nonempty_fintype G
  rw [Fintype.bijective_iff_injective_and_card]
  constructor
  · exact MulSemiringAction.toAlgHom_injective _ F
  · apply le_antisymm
    · exact Fintype.card_le_of_injective _ (MulSemiringAction.toAlgHom_injective _ F)
    · rw [← finrank_eq_card G F]
      exact LE.le.trans_eq (finrank_algHom _ F) (finrank_linearMap_self _ _ _)

/-- Bijection between `G` and algebra endomorphisms of `F` that fix the fixed points. -/
def toAlgHomEquiv [Finite G] [FaithfulSMul G F] : G ≃ (F →ₐ[FixedPoints.subfield G F] F) :=
  Equiv.ofBijective _ (toAlgHom_bijective G F)

/-- `MulSemiringAction.toAlgAut` is bijective. -/
theorem toAlgAut_bijective [Finite G] [FaithfulSMul G F] :
    Function.Bijective (MulSemiringAction.toAlgAut G (FixedPoints.subfield G F) F) := by
  refine ⟨fun _ _ h ↦ (FixedPoints.toAlgHom_bijective G F).injective ?_,
    fun f ↦ ((FixedPoints.toAlgHom_bijective G F).surjective f).imp (fun _ h ↦ ?_)⟩ <;>
      rwa [DFunLike.ext_iff] at h ⊢

/-- Bijection between `G` and algebra automorphisms of `F` that fix the fixed points. -/
def toAlgAutMulEquiv [Finite G] [FaithfulSMul G F] : G ≃* (F ≃ₐ[FixedPoints.subfield G F] F) :=
  MulEquiv.ofBijective _ (toAlgAut_bijective G F)

/-- `MulSemiringAction.toAlgAut` is surjective. -/
theorem toAlgAut_surjective [Finite G] :
    Function.Surjective (MulSemiringAction.toAlgAut G (FixedPoints.subfield G F) F) := by
  let f : G →* F ≃ₐ[FixedPoints.subfield G F] F :=
    MulSemiringAction.toAlgAut G (FixedPoints.subfield G F) F
  let Q := G ⧸ f.ker
  let _ : MulSemiringAction Q F := MulSemiringAction.compHom _ (QuotientGroup.kerLift f)
  have : FaithfulSMul Q F := ⟨by
    intro q₁ q₂
    refine Quotient.inductionOn₂' q₁ q₂ (fun g₁ g₂ h ↦ QuotientGroup.eq.mpr ?_)
    rwa [MonoidHom.mem_ker, map_mul, map_inv, inv_mul_eq_one, AlgEquiv.ext_iff]⟩
  intro f
  obtain ⟨q, hq⟩ := (toAlgAut_bijective Q F).surjective
    (AlgEquiv.ofRingEquiv (f := f) (fun ⟨x, hx⟩ ↦ f.commutes' ⟨x, fun g ↦ hx g⟩))
  revert hq
  refine QuotientGroup.induction_on q (fun g hg ↦ ⟨g, ?_⟩)
  rwa [AlgEquiv.ext_iff] at hg ⊢

end FixedPoints
