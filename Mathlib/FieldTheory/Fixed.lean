/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import Mathlib.Algebra.GroupRingAction.Invariant
import Mathlib.Algebra.Polynomial.GroupRingAction
import Mathlib.FieldTheory.Normal
import Mathlib.FieldTheory.Separable
import Mathlib.FieldTheory.Tower

#align_import field_theory.fixed from "leanprover-community/mathlib"@"039a089d2a4b93c761b234f3e5f5aeb752bac60f"

/-!
# Fixed field under a group action.

This is the basis of the Fundamental Theorem of Galois Theory.
Given a (finite) group `G` that acts on a field `F`, we define `FixedPoints.subfield G F`,
the subfield consisting of elements of `F` fixed_points by every element of `G`.

This subfield is then normal and separable, and in addition (TODO) if `G` acts faithfully on `F`
then `finrank (FixedPoints.subfield G F) F = Fintype.card G`.

## Main Definitions

- `FixedPoints.subfield G F`, the subfield consisting of elements of `F` fixed_points by every
element of `G`, where `G` is a group that acts on `F`.

-/


noncomputable section

open scoped Classical BigOperators

open MulAction Finset FiniteDimensional

universe u v w

variable {M : Type u} [Monoid M]

variable (G : Type u) [Group G]

variable (F : Type v) [Field F] [MulSemiringAction M F] [MulSemiringAction G F] (m : M)

/-- The subfield of F fixed by the field endomorphism `m`. -/
def FixedBy.subfield : Subfield F where
  carrier := fixedBy M F m
  zero_mem' := smul_zero m
  add_mem' hx hy := (smul_add m _ _).trans <| congr_arg₂ _ hx hy
  neg_mem' hx := (smul_neg m _).trans <| congr_arg _ hx
  one_mem' := smul_one m
  mul_mem' hx hy := (smul_mul' m _ _).trans <| congr_arg₂ _ hx hy
  inv_mem' x hx := (smul_inv'' m x).trans <| congr_arg _ hx
#align fixed_by.subfield FixedBy.subfield

section InvariantSubfields

variable (M) {F}

/-- A typeclass for subrings invariant under a `MulSemiringAction`. -/
class IsInvariantSubfield (S : Subfield F) : Prop where
  smul_mem : ∀ (m : M) {x : F}, x ∈ S → m • x ∈ S
#align is_invariant_subfield IsInvariantSubfield

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
#align is_invariant_subfield.to_mul_semiring_action IsInvariantSubfield.toMulSemiringAction

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
        -- ⊢ z ∈ fixedPoints M F ↔ z ∈ ↑(⨅ (m : M), FixedBy.subfield F m)
               -- ⊢ (∀ (m : M), m • z = z) ↔ ∀ (i : M), z ∈ { toSubmonoid := { toSubsemigroup := …
                                                                              -- 🎉 no goals
#align fixed_points.subfield FixedPoints.subfield

instance : IsInvariantSubfield M (FixedPoints.subfield M F) where
  smul_mem g x hx g' := by rw [hx, hx]
                           -- 🎉 no goals

instance : SMulCommClass M (FixedPoints.subfield M F) F where
  smul_comm m f f' := show m • (↑f * f') = f * m • f' by rw [smul_mul', f.prop m]
                                                         -- 🎉 no goals

instance smulCommClass' : SMulCommClass (FixedPoints.subfield M F) M F :=
  SMulCommClass.symm _ _ _
#align fixed_points.smul_comm_class' FixedPoints.smulCommClass'

@[simp]
theorem smul (m : M) (x : FixedPoints.subfield M F) : m • x = x :=
  Subtype.eq <| x.2 m
#align fixed_points.smul FixedPoints.smul

-- Why is this so slow?
@[simp]
theorem smul_polynomial (m : M) (p : Polynomial (FixedPoints.subfield M F)) : m • p = p :=
  Polynomial.induction_on p (fun x => by rw [Polynomial.smul_C, smul])
                                         -- 🎉 no goals
    (fun p q ihp ihq => by rw [smul_add, ihp, ihq]) fun n x _ => by
                           -- 🎉 no goals
    rw [smul_mul', Polynomial.smul_C, smul, smul_pow', Polynomial.smul_X]
    -- 🎉 no goals
#align fixed_points.smul_polynomial FixedPoints.smul_polynomial

instance : Algebra (FixedPoints.subfield M F) F := by infer_instance
                                                      -- 🎉 no goals

theorem coe_algebraMap :
    algebraMap (FixedPoints.subfield M F) F = Subfield.subtype (FixedPoints.subfield M F) :=
  rfl
#align fixed_points.coe_algebra_map FixedPoints.coe_algebraMap

theorem linearIndependent_smul_of_linearIndependent {s : Finset F} :
    (LinearIndependent (FixedPoints.subfield G F) fun i : (s : Set F) => (i : F)) →
      LinearIndependent F fun i : (s : Set F) => MulAction.toFun G F i := by
  haveI : IsEmpty ((∅ : Finset F) : Set F) := by simp
  -- ⊢ (LinearIndependent { x // x ∈ subfield G F } fun i => ↑i) → LinearIndependen …
  refine' Finset.induction_on s (fun _ => linearIndependent_empty_type) fun a s has ih hs => _
  -- ⊢ LinearIndependent F fun i => ↑(toFun G F) ↑i
  rw [coe_insert] at hs ⊢
  -- ⊢ LinearIndependent F fun i => ↑(toFun G F) ↑i
  rw [linearIndependent_insert (mt mem_coe.1 has)] at hs
  -- ⊢ LinearIndependent F fun i => ↑(toFun G F) ↑i
  rw [linearIndependent_insert' (mt mem_coe.1 has)]; refine' ⟨ih hs.1, fun ha => _⟩
  -- ⊢ (LinearIndependent F fun x => ↑(toFun G F) ↑x) ∧ ¬↑(toFun G F) a ∈ Submodule …
                                                     -- ⊢ False
  rw [Finsupp.mem_span_image_iff_total] at ha; rcases ha with ⟨l, hl, hla⟩
  -- ⊢ False
                                               -- ⊢ False
  rw [Finsupp.total_apply_of_mem_supported F hl] at hla
  -- ⊢ False
  suffices ∀ i ∈ s, l i ∈ FixedPoints.subfield G F by
    replace hla := (sum_apply _ _ fun i => l i • toFun G F i).symm.trans (congr_fun hla 1)
    simp_rw [Pi.smul_apply, toFun_apply, one_smul] at hla
    refine' hs.2 (hla ▸ Submodule.sum_mem _ fun c hcs => _)
    change (⟨l c, this c hcs⟩ : FixedPoints.subfield G F) • c ∈ _
    exact Submodule.smul_mem _ _ (Submodule.subset_span <| mem_coe.2 hcs)
  intro i his g
  -- ⊢ g • ↑l i = ↑l i
  refine'
    eq_of_sub_eq_zero
      (linearIndependent_iff'.1 (ih hs.1) s.attach (fun i => g • l i - l i) _ ⟨i, his⟩
          (mem_attach _ _) :
        _)
  refine' (@sum_attach _ _ s _ fun i => (g • l i - l i) • MulAction.toFun G F i).trans _
  -- ⊢ ∑ x in s, (g • ↑l x - ↑l x) • ↑(toFun G F) x = 0
  ext g'; dsimp only
  -- ⊢ Finset.sum s (fun x => (g • ↑l x - ↑l x) • ↑(toFun G F) x) g' = OfNat.ofNat  …
          -- ⊢ Finset.sum s (fun x => (g • ↑l x - ↑l x) • ↑(toFun G F) x) g' = OfNat.ofNat  …
  conv_lhs =>
    rw [sum_apply]
    congr
    · skip
    · ext
      rw [Pi.smul_apply, sub_smul, smul_eq_mul]
  rw [sum_sub_distrib, Pi.zero_apply, sub_eq_zero]
  -- ⊢ ∑ x in s, g • ↑l x * ↑(toFun G F) x g' = ∑ x in s, ↑l x • ↑(toFun G F) x g'
  conv_lhs =>
    congr
    · skip
    · ext x
      rw [toFun_apply, ← mul_inv_cancel_left g g', mul_smul, ← smul_mul', ← toFun_apply _ x]
  show
    (∑ x in s, g • (fun y => l y • MulAction.toFun G F y) x (g⁻¹ * g')) =
      ∑ x in s, (fun y => l y • MulAction.toFun G F y) x g'
  rw [← smul_sum, ← sum_apply _ _ fun y => l y • toFun G F y, ←
    sum_apply _ _ fun y => l y • toFun G F y]
  dsimp only
  -- ⊢ g • Finset.sum s (fun c => ↑l c • ↑(toFun G F) c) (g⁻¹ * g') = Finset.sum s  …
  rw [hla, toFun_apply, toFun_apply, smul_smul, mul_inv_cancel_left]
  -- 🎉 no goals
#align fixed_points.linear_independent_smul_of_linear_independent FixedPoints.linearIndependent_smul_of_linearIndependent

section Fintype

variable [Fintype G] (x : F)

/-- `minpoly G F x` is the minimal polynomial of `(x : F)` over `FixedPoints.subfield G F`. -/
def minpoly : Polynomial (FixedPoints.subfield G F) :=
  (prodXSubSmul G F x).toSubring (FixedPoints.subfield G F).toSubring fun _ hc g =>
    let ⟨n, _, hn⟩ := Polynomial.mem_frange_iff.1 hc
    hn.symm ▸ prodXSubSmul.coeff G F x g n
#align fixed_points.minpoly FixedPoints.minpoly

namespace minpoly

theorem monic : (minpoly G F x).Monic := by
  simp only [minpoly, Polynomial.monic_toSubring];
  -- ⊢ Polynomial.Monic (prodXSubSmul G F x)
  exact prodXSubSmul.monic G F x
  -- 🎉 no goals
#align fixed_points.minpoly.monic FixedPoints.minpoly.monic

theorem eval₂ :
    Polynomial.eval₂ (Subring.subtype <| (FixedPoints.subfield G F).toSubring) x (minpoly G F x) =
      0 := by
  rw [← prodXSubSmul.eval G F x, Polynomial.eval₂_eq_eval_map]
  -- ⊢ Polynomial.eval x (Polynomial.map (Subring.subtype (subfield G F).toSubring) …
  simp only [minpoly, Polynomial.map_toSubring]
  -- 🎉 no goals
#align fixed_points.minpoly.eval₂ FixedPoints.minpoly.eval₂

theorem eval₂' :
    Polynomial.eval₂ (Subfield.subtype <| FixedPoints.subfield G F) x (minpoly G F x) = 0 :=
  eval₂ G F x
#align fixed_points.minpoly.eval₂' FixedPoints.minpoly.eval₂'

theorem ne_one : minpoly G F x ≠ (1 : Polynomial (FixedPoints.subfield G F)) := fun H =>
  have := eval₂ G F x
  (one_ne_zero : (1 : F) ≠ 0) <| by rwa [H, Polynomial.eval₂_one] at this
                                    -- 🎉 no goals
#align fixed_points.minpoly.ne_one FixedPoints.minpoly.ne_one

theorem of_eval₂ (f : Polynomial (FixedPoints.subfield G F))
    (hf : Polynomial.eval₂ (Subfield.subtype <| FixedPoints.subfield G F) x f = 0) :
    minpoly G F x ∣ f := by
-- Porting note: the two `have` below were not needed.
  have : (subfield G F).subtype = (subfield G F).toSubring.subtype := rfl
  -- ⊢ minpoly G F x ∣ f
  have h : Polynomial.map (MulSemiringActionHom.toRingHom (IsInvariantSubring.subtypeHom G
    (subfield G F).toSubring)) f = Polynomial.map
    ((IsInvariantSubring.subtypeHom G (subfield G F).toSubring)) f := rfl
  erw [← Polynomial.map_dvd_map' (Subfield.subtype <| FixedPoints.subfield G F), minpoly, this,
    Polynomial.map_toSubring _ _, prodXSubSmul]
  refine'
    Fintype.prod_dvd_of_coprime
      (Polynomial.pairwise_coprime_X_sub_C <| MulAction.injective_ofQuotientStabilizer G x) fun y =>
      QuotientGroup.induction_on y fun g => _
  rw [Polynomial.dvd_iff_isRoot, Polynomial.IsRoot.def, MulAction.ofQuotientStabilizer_mk,
    Polynomial.eval_smul', ← this, ← Subfield.toSubring_subtype_eq_subtype, ←
    IsInvariantSubring.coe_subtypeHom' G (FixedPoints.subfield G F).toSubring, h,
    ← MulSemiringActionHom.coe_polynomial, ← MulSemiringActionHom.map_smul, smul_polynomial,
    MulSemiringActionHom.coe_polynomial, ← h, IsInvariantSubring.coe_subtypeHom',
    Polynomial.eval_map, Subfield.toSubring_subtype_eq_subtype, hf, smul_zero]
#align fixed_points.minpoly.of_eval₂ FixedPoints.minpoly.of_eval₂

-- Why is this so slow?
theorem irreducible_aux (f g : Polynomial (FixedPoints.subfield G F)) (hf : f.Monic) (hg : g.Monic)
    (hfg : f * g = minpoly G F x) : f = 1 ∨ g = 1 := by
  have hf2 : f ∣ minpoly G F x := by rw [← hfg]; exact dvd_mul_right _ _
  -- ⊢ f = 1 ∨ g = 1
  have hg2 : g ∣ minpoly G F x := by rw [← hfg]; exact dvd_mul_left _ _
  -- ⊢ f = 1 ∨ g = 1
  have := eval₂ G F x
  -- ⊢ f = 1 ∨ g = 1
  rw [← hfg, Polynomial.eval₂_mul, mul_eq_zero] at this
  -- ⊢ f = 1 ∨ g = 1
  cases' this with this this
  -- ⊢ f = 1 ∨ g = 1
  · right
    -- ⊢ g = 1
    have hf3 : f = minpoly G F x :=
      Polynomial.eq_of_monic_of_associated hf (monic G F x)
        (associated_of_dvd_dvd hf2 <| @of_eval₂ G _ F _ _ _ x f this)
    rwa [← mul_one (minpoly G F x), hf3, mul_right_inj' (monic G F x).ne_zero] at hfg
    -- 🎉 no goals
  · left
    -- ⊢ f = 1
    have hg3 : g = minpoly G F x :=
      Polynomial.eq_of_monic_of_associated hg (monic G F x)
        (associated_of_dvd_dvd hg2 <| @of_eval₂ G _ F _ _ _ x g this)
    rwa [← one_mul (minpoly G F x), hg3, mul_left_inj' (monic G F x).ne_zero] at hfg
    -- 🎉 no goals
#align fixed_points.minpoly.irreducible_aux FixedPoints.minpoly.irreducible_aux

theorem irreducible : Irreducible (minpoly G F x) :=
  (Polynomial.irreducible_of_monic (monic G F x) (ne_one G F x)).2 (irreducible_aux G F x)
#align fixed_points.minpoly.irreducible FixedPoints.minpoly.irreducible

end minpoly

end Fintype

theorem isIntegral [Finite G] (x : F) : IsIntegral (FixedPoints.subfield G F) x := by
  cases nonempty_fintype G; exact ⟨minpoly G F x, minpoly.monic G F x, minpoly.eval₂ G F x⟩
  -- ⊢ IsIntegral { x // x ∈ subfield G F } x
                            -- 🎉 no goals
#align fixed_points.is_integral FixedPoints.isIntegral

section Fintype

variable [Fintype G] (x : F)

theorem minpoly_eq_minpoly : minpoly G F x = _root_.minpoly (FixedPoints.subfield G F) x :=
  minpoly.eq_of_irreducible_of_monic (minpoly.irreducible G F x) (minpoly.eval₂ G F x)
    (minpoly.monic G F x)
#align fixed_points.minpoly_eq_minpoly FixedPoints.minpoly_eq_minpoly

theorem rank_le_card : Module.rank (FixedPoints.subfield G F) F ≤ Fintype.card G :=
  rank_le fun s hs => by
    simpa only [rank_fun', Cardinal.mk_coe_finset, Finset.coe_sort_coe, Cardinal.lift_natCast,
      Cardinal.natCast_le] using
      cardinal_lift_le_rank_of_linearIndependent'
        (linearIndependent_smul_of_linearIndependent G F hs)
#align fixed_points.rank_le_card FixedPoints.rank_le_card

end Fintype

section Finite

variable [Finite G]

instance normal : Normal (FixedPoints.subfield G F) F :=
  ⟨fun x => (isIntegral G F x).isAlgebraic _, fun x =>
    (Polynomial.splits_id_iff_splits _).1 <| by
      cases nonempty_fintype G
      -- ⊢ Polynomial.Splits (RingHom.id F) (Polynomial.map (algebraMap { x // x ∈ subf …
      rw [← minpoly_eq_minpoly, minpoly, coe_algebraMap, ← Subfield.toSubring_subtype_eq_subtype,
        Polynomial.map_toSubring _ (subfield G F).toSubring, prodXSubSmul]
      exact Polynomial.splits_prod _ fun _ _ => Polynomial.splits_X_sub_C _⟩
      -- 🎉 no goals
#align fixed_points.normal FixedPoints.normal

instance separable : IsSeparable (FixedPoints.subfield G F) F :=
  ⟨isIntegral G F, fun x => by
    cases nonempty_fintype G
    -- ⊢ Polynomial.Separable (_root_.minpoly { x // x ∈ subfield G F } x)
    -- this was a plain rw when we were using unbundled subrings
    erw [← minpoly_eq_minpoly, ← Polynomial.separable_map (FixedPoints.subfield G F).subtype,
      minpoly, Polynomial.map_toSubring _ (subfield G F).toSubring]
    exact Polynomial.separable_prod_X_sub_C_iff.2 (injective_ofQuotientStabilizer G x)⟩
    -- 🎉 no goals
#align fixed_points.separable FixedPoints.separable

instance : FiniteDimensional (subfield G F) F := by
  cases nonempty_fintype G
  -- ⊢ FiniteDimensional { x // x ∈ subfield G F } F
  exact IsNoetherian.iff_fg.1
      (IsNoetherian.iff_rank_lt_aleph0.2 <| (rank_le_card G F).trans_lt <| Cardinal.nat_lt_aleph0 _)

end Finite

theorem finrank_le_card [Fintype G] : finrank (subfield G F) F ≤ Fintype.card G := by
  rw [← Cardinal.natCast_le, finrank_eq_rank]
  -- ⊢ Module.rank { x // x ∈ subfield G F } F ≤ ↑(Fintype.card G)
  apply rank_le_card
  -- 🎉 no goals
#align fixed_points.finrank_le_card FixedPoints.finrank_le_card

end FixedPoints

theorem linearIndependent_toLinearMap (R : Type u) (A : Type v) (B : Type w) [CommSemiring R]
    [Ring A] [Algebra R A] [CommRing B] [IsDomain B] [Algebra R B] :
    LinearIndependent B (AlgHom.toLinearMap : (A →ₐ[R] B) → A →ₗ[R] B) :=
  have : LinearIndependent B (LinearMap.ltoFun R A B ∘ AlgHom.toLinearMap) :=
    ((linearIndependent_monoidHom A B).comp ((↑) : (A →ₐ[R] B) → A →* B) fun _ _ hfg =>
        AlgHom.ext <| fun _ => FunLike.ext_iff.1 hfg _ :
      _)
  this.of_comp _
#align linear_independent_to_linear_map linearIndependent_toLinearMap

theorem cardinal_mk_algHom (K : Type u) (V : Type v) (W : Type w) [Field K] [Field V] [Algebra K V]
    [FiniteDimensional K V] [Field W] [Algebra K W] [FiniteDimensional K W] :
    Cardinal.mk (V →ₐ[K] W) ≤ finrank W (V →ₗ[K] W) :=
  cardinal_mk_le_finrank_of_linearIndependent <| linearIndependent_toLinearMap K V W
#align cardinal_mk_alg_hom cardinal_mk_algHom

noncomputable instance AlgEquiv.fintype (K : Type u) (V : Type v) [Field K] [Field V] [Algebra K V]
    [FiniteDimensional K V] : Fintype (V ≃ₐ[K] V) :=
  Fintype.ofEquiv (V →ₐ[K] V) (algEquivEquivAlgHom K V).symm
#align alg_equiv.fintype AlgEquiv.fintype

theorem finrank_algHom (K : Type u) (V : Type v) [Field K] [Field V] [Algebra K V]
    [FiniteDimensional K V] : Fintype.card (V →ₐ[K] V) ≤ finrank V (V →ₗ[K] V) :=
  fintype_card_le_finrank_of_linearIndependent <| linearIndependent_toLinearMap K V V
#align finrank_alg_hom finrank_algHom

namespace FixedPoints

theorem finrank_eq_card (G : Type u) (F : Type v) [Group G] [Field F] [Fintype G]
    [MulSemiringAction G F] [FaithfulSMul G F] :
    finrank (FixedPoints.subfield G F) F = Fintype.card G :=
  le_antisymm (FixedPoints.finrank_le_card G F) <|
    calc
      Fintype.card G ≤ Fintype.card (F →ₐ[FixedPoints.subfield G F] F) :=
        Fintype.card_le_of_injective _ (MulSemiringAction.toAlgHom_injective _ F)
      _ ≤ finrank F (F →ₗ[FixedPoints.subfield G F] F) := (finrank_algHom (subfield G F) F)
      _ = finrank (FixedPoints.subfield G F) F := finrank_linear_map' _ _ _
#align fixed_points.finrank_eq_card FixedPoints.finrank_eq_card

/-- `MulSemiringAction.toAlgHom` is bijective. -/
theorem toAlgHom_bijective (G : Type u) (F : Type v) [Group G] [Field F] [Finite G]
    [MulSemiringAction G F] [FaithfulSMul G F] :
    Function.Bijective (MulSemiringAction.toAlgHom _ _ : G → F →ₐ[subfield G F] F) := by
  cases nonempty_fintype G
  -- ⊢ Function.Bijective (MulSemiringAction.toAlgHom { x // x ∈ subfield G F } F)
  rw [Fintype.bijective_iff_injective_and_card]
  -- ⊢ Function.Injective (MulSemiringAction.toAlgHom { x // x ∈ subfield G F } F)  …
  constructor
  -- ⊢ Function.Injective (MulSemiringAction.toAlgHom { x // x ∈ subfield G F } F)
  · exact MulSemiringAction.toAlgHom_injective _ F
    -- 🎉 no goals
  · apply le_antisymm
    -- ⊢ Fintype.card G ≤ Fintype.card (F →ₐ[{ x // x ∈ subfield G F }] F)
    · exact Fintype.card_le_of_injective _ (MulSemiringAction.toAlgHom_injective _ F)
      -- 🎉 no goals
    · rw [← finrank_eq_card G F]
      -- ⊢ Fintype.card (F →ₐ[{ x // x ∈ subfield G F }] F) ≤ finrank { x // x ∈ subfie …
      exact LE.le.trans_eq (finrank_algHom _ F) (finrank_linear_map' _ _ _)
      -- 🎉 no goals
#align fixed_points.to_alg_hom_bijective FixedPoints.toAlgHom_bijective

/-- Bijection between G and algebra homomorphisms that fix the fixed points -/
def toAlgHomEquiv (G : Type u) (F : Type v) [Group G] [Field F] [Fintype G] [MulSemiringAction G F]
    [FaithfulSMul G F] : G ≃ (F →ₐ[FixedPoints.subfield G F] F) :=
  Equiv.ofBijective _ (toAlgHom_bijective G F)
#align fixed_points.to_alg_hom_equiv FixedPoints.toAlgHomEquiv

end FixedPoints
