/-
Copyright (c) 2024 Brendan Murphy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brendan Murphy
-/
import Mathlib.RingTheory.Regular.IsSMulRegular
import Mathlib.RingTheory.Artinian
import Mathlib.Logic.Equiv.TransferInstance
import Mathlib.RingTheory.Ideal.LocalRing

/-!
# Regular sequences and weakly regular sequences

The notion of a regular sequence is fundamental in commutative algebra.
Properties of regular sequences encode information about a singularities of a
ring and regularity of a sequence can be tested homologically.
However the notion of a regular sequence is only really sensible for Noetherian local rings.

TODO: Koszul regular sequences, H_1-regular sequences, quasi-regular sequences, depth.

## Tags

module, regular element, regular sequence, commutative algebra
-/

universe u v

namespace RingTheory.Sequence

open scoped Pointwise TensorProduct
open Function Submodule

variable (R : Type u) {S : Type*} (M : Type v) {M' M'' : Type*}

section

variable [CommSemiring R] [CommSemiring S] [Algebra R S]
    [AddCommMonoid M] [Module R M] [Module S M] [IsScalarTower R S M]
    [AddCommMonoid M'] [Module R M']

-- We need to choose whether we want the defeq `(r :: rs) • N = r • N + rs • N` or
-- `[r₁, …, rₙ] • N = r₁ • N + ⋯ + rₙ • N`. For now we pick the first
instance smulSubmodule : SMul (List R) (Submodule R M) where
  smul rs N := rs.foldr (fun r N' => r • N ⊔ N') ⊥

variable {M}

@[simp] lemma nil_smul (N : Submodule R M) : ([] : List R) • N = ⊥ := rfl

variable {R}

@[simp] lemma cons_smul (r : R) (rs : List R) (N : Submodule R M) :
    (r :: rs) • N = r • N ⊔ rs • N := rfl

lemma singleton_smul (r : R) (N : Submodule R M) : [r] • N = r • N :=
  Eq.trans (cons_smul r [] N) (add_zero (r • N))

-- better for reasoning about sometimes but worse def eqs
-- argument order is reverse of `singleton_set_smul`
lemma sequence_smul_eq_set_smul (rs : List R) (N : Submodule R M) :
    rs • N = { r | r ∈ rs } • N := by
  induction rs with
  | nil => simp_rw [List.not_mem_nil, Set.setOf_false, empty_set_smul, nil_smul]
  | cons r rs ih =>
    simp_rw [cons_smul, ih, ← singleton_set_smul, ← sup_set_smul, List.mem_cons]
    rfl

instance : CovariantClass (List R) (Submodule R M) HSMul.hSMul LE.le where
  elim _ _ _ := by
    simp_rw [sequence_smul_eq_set_smul]
    apply smul_mono_right

lemma sequence_smul_eq_ideal_span_smul (rs : List R) (N : Submodule R M) :
    rs • N = Ideal.span { r | r ∈ rs } • N :=
  Eq.trans (sequence_smul_eq_set_smul rs N) (span_smul_eq _ _).symm

@[simp] lemma append_smul (rs₁ rs₂ : List R) (N : Submodule R M) :
    (rs₁ ++ rs₂) • N = rs₁ • N ⊔ rs₂ • N := by
  simp_rw [sequence_smul_eq_ideal_span_smul, List.mem_append, ← sup_smul]
  exact congrArg (· • N) (Ideal.span_union _ _)

lemma _root_.Submodule.map_sequence_smul (rs : List R) (N : Submodule R M)
    (f : M →ₗ[R] M') : map f (rs • N) = rs • map f N :=
  by simpa only [sequence_smul_eq_ideal_span_smul] using map_smul'' _ N f

lemma restrictScalars_map_algebraMap_smul_eq_smul_restrictScalars
    (rs : List R) (N : Submodule S M) :
    (rs.map (algebraMap R S) • N).restrictScalars R = rs • N.restrictScalars R := by
  simp_rw [sequence_smul_eq_ideal_span_smul, List.mem_map,
    ← Ideal.smul_restrictScalars, Ideal.map_span, Set.image, Set.mem_setOf]

lemma smul_le_ideal_smul_of_forall_mem {I : Ideal R} {rs : List R}
    (N : Submodule R M) (h : ∀ r ∈ rs, r ∈ I) : rs • N ≤ I • N :=
  le_of_eq_of_le (sequence_smul_eq_ideal_span_smul rs N) <|
    Submodule.smul_mono_left <| Ideal.span_le.mpr h

end

variable {R M} [CommRing R] [CommRing S] [AddCommGroup M] [AddCommGroup M']
    [AddCommGroup M''] [Module R M] [Module R M'] [Module R M'']

lemma eq_bot_of_sequence_smul_eq_of_subset_jacobson_annihilator {rs : List R}
    {N : Submodule R M} (hN : FG N) (hrsN : N = rs • N)
    (hrsJac : ∀ r ∈ rs, r ∈ N.annihilator.jacobson) : N = ⊥ :=
  eq_bot_of_set_smul_eq_of_subset_jacobson_annihilator hN
    (Eq.trans hrsN (sequence_smul_eq_set_smul rs N)) hrsJac

lemma top_ne_ideal_smul_of_le_jacobson_annihilator [Nontrivial M]
    [Module.Finite R M] {I} (h : I ≤ (Module.annihilator R M).jacobson) :
    (⊤ : Submodule R M) ≠ I • ⊤ := fun H => top_ne_bot <|
  eq_bot_of_eq_ideal_smul_of_le_jacobson_annihilator Module.Finite.out H <|
    (congrArg (I ≤ Ideal.jacobson ·) annihilator_top).mpr h

lemma top_ne_set_smul_of_subset_jacobson_annihilator [Nontrivial M]
    [Module.Finite R M] {s : Set R}
    (h : s ⊆ (Module.annihilator R M).jacobson) :
    (⊤ : Submodule R M) ≠ s • ⊤ :=
  ne_of_ne_of_eq (top_ne_ideal_smul_of_le_jacobson_annihilator (span_le.mpr h))
    (span_smul_eq _ _)

lemma top_ne_pointwise_smul_of_mem_jacobson_annihilator [Nontrivial M]
    [Module.Finite R M] {r} (h : r ∈ (Module.annihilator R M).jacobson) :
    (⊤ : Submodule R M) ≠ r • ⊤ :=
  ne_of_ne_of_eq (top_ne_set_smul_of_subset_jacobson_annihilator <|
                    Set.singleton_subset_iff.mpr h) (singleton_set_smul ⊤ r)

lemma sequence_smul_ne_top_of_subset_jacobson_annihilator [Nontrivial M]
    [Module.Finite R M] {rs : List R}
    (h : ∀ r ∈ rs, r ∈ (Module.annihilator R M).jacobson) :
    (⊤ : Submodule R M) ≠ rs • ⊤ :=
  ne_of_ne_of_eq (top_ne_set_smul_of_subset_jacobson_annihilator h)
    (sequence_smul_eq_set_smul rs ⊤).symm

variable (M)

-- Should there be a typeclass for this? Smth about a natural action on submodules?
-- or maybe we should develop the API for ideals first and foremost?
/-- An abbreviation for `M⧸(r₁, …, rₙ)M` that keeps us from having to write
`(⊤ : Submodule R M)` over and over to satisfy the typechecker. -/
protected abbrev ModSMulBy (rs : List R) := M ⧸ (rs • ⊤ : Submodule R M)

namespace ModSMulBy

/-- Reducing a module modulo `r₁,…,rₙ` is the same as left tensoring with `R/(r₁,…,rₙ)`. -/
protected noncomputable def equivQuotTensor (rs : List R) :
    Sequence.ModSMulBy M rs ≃ₗ[R] (R⧸Ideal.span { r | r ∈ rs }) ⊗[R] M :=
  quotEquivOfEq _ _ (sequence_smul_eq_ideal_span_smul _ _) ≪≫ₗ
   (quotTensorEquivQuotSMul M _).symm

/-- Reducing a module modulo `r₁,…,rₙ` is the same as right tensoring with `R/(r₁,…,rₙ)`. -/
protected noncomputable def equivTensorQuot (rs : List R) :
    Sequence.ModSMulBy M rs ≃ₗ[R] M ⊗[R] (R⧸Ideal.span { r | r ∈ rs }) :=
  quotEquivOfEq _ _ (sequence_smul_eq_ideal_span_smul _ _) ≪≫ₗ
   (tensorQuotEquivQuotSMul M _).symm

variable (R)

/-- Reducing mod no elements is isomorphic to the original module. -/
def nilEquivSelf : Sequence.ModSMulBy M ([] : List R) ≃ₗ[R] M :=
  quotEquivOfEqBot ([] • ⊤) rfl

variable {R}

/-- The equivalence `M⧸(r₀,r₁,…,rₙ)M ≃ (M⧸r₀M)⧸(r₁,…,rₙ)M`. -/
def consEquivQuotTailQuotHead (r : R) (rs : List R) :
    Sequence.ModSMulBy M (r :: rs) ≃ₗ[R] Sequence.ModSMulBy (ModSMulBy M r) rs :=
  (quotientQuotientEquivQuotientSup (r • ⊤) (rs • ⊤)).symm ≪≫ₗ
    quotEquivOfEq _ _ (by rw [map_sequence_smul, Submodule.map_top, range_mkQ])

/-- The equivalence `M⧸(r₁,…,rₙ,s₁,…,sₘ)M ≃ (M⧸(r₁,…,rₙ)M)⧸(s₁,…,sₘ)M`. -/
def appendEquivQuotQuot (rs₁ rs₂ : List R) :
    Sequence.ModSMulBy M (rs₁ ++ rs₂) ≃ₗ[R]
      Sequence.ModSMulBy (Sequence.ModSMulBy M rs₁) rs₂ :=
  quotEquivOfEq _ _ (append_smul rs₁ rs₂ ⊤) ≪≫ₗ
    (quotientQuotientEquivQuotientSup _ _).symm ≪≫ₗ
      quotEquivOfEq _ _ (by rw [map_sequence_smul, Submodule.map_top, range_mkQ])

/-- Reducing modulo a list is independent of order and multiplicity. -/
def equivOfSubsetSubset {rs₁ rs₂ : List R} (h₁₂ : rs₁ ⊆ rs₂) (h₂₁ : rs₂ ⊆ rs₁) :
    Sequence.ModSMulBy M rs₁ ≃ₗ[R] Sequence.ModSMulBy M rs₂ :=
  quotEquivOfEq _ _ <| by
    simp_rw [sequence_smul_eq_set_smul]; congr; exact subset_antisymm h₁₂ h₂₁

/-- An important special case of `equiv_of_subset_subset`. -/
def equivOfPerm {rs₁ rs₂ : List R} (h : List.Perm rs₁ rs₂) :
    Sequence.ModSMulBy M rs₁ ≃ₗ[R] Sequence.ModSMulBy M rs₂ :=
  equivOfSubsetSubset M h.subset h.symm.subset

variable {M}

/-- The action of the functor `Sequence.ModSMulBy · rs` on morphisms. -/
def map (rs : List R) :
    (M →ₗ[R] M') → Sequence.ModSMulBy M rs →ₗ[R] Sequence.ModSMulBy M' rs :=
  Submodule.mapQLinear _ _ ∘ₗ LinearMap.id.codRestrict _ fun _ =>
    map_le_iff_le_comap.mp <| le_of_eq_of_le (map_sequence_smul _ _ _) <|
      smul_mono_right rs le_top

@[simp]
lemma map_apply (rs : List R) (f : M →ₗ[R] M') (x : M) :
    map rs f (Submodule.Quotient.mk x) =
      (Submodule.Quotient.mk (f x) : Sequence.ModSMulBy M' rs) := rfl

lemma map_comp_mkQ (rs : List R) (f : M →ₗ[R] M') :
    map rs f ∘ₗ mkQ (rs • ⊤) = mkQ (rs • ⊤) ∘ₗ f := rfl

variable (M)

@[simp]
lemma map_id (rs : List R) : map rs (LinearMap.id : M →ₗ[R] M) = .id :=
  DFunLike.ext _ _ <| (mkQ_surjective _).forall.mpr fun _ => rfl

variable {M}

@[simp]
lemma map_comp (rs : List R) (g : M' →ₗ[R] M'') (f : M →ₗ[R] M') :
    map rs (g ∘ₗ f) = map rs g ∘ₗ map rs f :=
  DFunLike.ext _ _ <| (mkQ_surjective _).forall.mpr fun _ => rfl

lemma equivQuotTensor_naturality_apply (rs : List R) (f : M →ₗ[R] M') (x : M) :
    Sequence.ModSMulBy.equivQuotTensor M' rs (map rs f (Submodule.Quotient.mk x)) =
      f.lTensor (R⧸Ideal.span {r | r ∈ rs})
        (Sequence.ModSMulBy.equivQuotTensor M rs (Submodule.Quotient.mk x)) := by
  simp only [Sequence.ModSMulBy.equivQuotTensor, LinearMap.coe_comp, comp_apply,
    mkQ_apply, LinearEquiv.trans_apply, quotEquivOfEq_mk, LinearMap.lTensor_tmul,
    map_apply, LinearEquiv.coe_coe, quotTensorEquivQuotSMul_symm_mk]

lemma equivQuotTensor_naturality (rs : List R) (f : M →ₗ[R] M') :
    Sequence.ModSMulBy.equivQuotTensor M' rs ∘ₗ map rs f =
      f.lTensor (R⧸Ideal.span {r | r ∈ rs}) ∘ₗ
        Sequence.ModSMulBy.equivQuotTensor M rs :=
  by ext x; exact equivQuotTensor_naturality_apply rs f x

lemma equivTensorQuot_naturality_apply (rs : List R) (f : M →ₗ[R] M') (x : M) :
    Sequence.ModSMulBy.equivTensorQuot M' rs (map rs f (Submodule.Quotient.mk x)) =
      f.rTensor (R⧸Ideal.span {r | r ∈ rs})
        (Sequence.ModSMulBy.equivTensorQuot M rs (Submodule.Quotient.mk x)) := by
  simp only [Sequence.ModSMulBy.equivTensorQuot, LinearMap.coe_comp, comp_apply,
    mkQ_apply, LinearEquiv.trans_apply, quotEquivOfEq_mk, LinearMap.rTensor_tmul,
    map_apply, LinearEquiv.coe_coe, tensorQuotEquivQuotSMul_symm_mk]

lemma equivTensorQuot_naturality (rs : List R) (f : M →ₗ[R] M') :
    Sequence.ModSMulBy.equivTensorQuot M' rs ∘ₗ map rs f =
      f.rTensor (R⧸Ideal.span {r | r ∈ rs}) ∘ₗ
        Sequence.ModSMulBy.equivTensorQuot M rs :=
  by ext x; exact equivTensorQuot_naturality_apply rs f x

lemma nilEquivSelf_naturality (f : M →ₗ[R] M') :
    nilEquivSelf R M' ∘ₗ map [] f = f ∘ₗ nilEquivSelf R M :=
  by ext; rfl

lemma consEquivQuotTailQuotHead_naturality (r : R) (rs : List R) (f : M →ₗ[R] M') :
    consEquivQuotTailQuotHead M' r rs ∘ₗ map (r :: rs) f =
      map rs (_root_.ModSMulBy.map r f) ∘ₗ consEquivQuotTailQuotHead M r rs :=
  by ext; rfl

lemma append_equiv_mod_mod_naturality (rs₁ rs₂ : List R) (f : M →ₗ[R] M') :
    appendEquivQuotQuot M' rs₁ rs₂ ∘ₗ map (rs₁ ++ rs₂) f =
      map rs₂ (map rs₁ f) ∘ₗ appendEquivQuotQuot M rs₁ rs₂ :=
  by ext; rfl

lemma equiv_of_subset_subset_naturality {rs₁ rs₂} (h₁₂ : rs₁ ⊆ rs₂)
    (h₂₁ : rs₂ ⊆ rs₁) (f : M →ₗ[R] M') :
    equivOfSubsetSubset M' h₁₂ h₂₁ ∘ₗ map rs₁ f =
      map rs₂ f ∘ₗ equivOfSubsetSubset M h₁₂ h₂₁ :=
  by ext; rfl

lemma equiv_of_perm_naturality {rs₁ rs₂} (h : List.Perm rs₁ rs₂)
    (f : M →ₗ[R] M') :
    equivOfPerm M' h ∘ₗ map rs₁ f = map rs₂ f ∘ₗ equivOfPerm M h :=
  by ext; rfl

lemma map_surjective (rs : List R) {f : M →ₗ[R] M'} (hf : Surjective f) :
    Surjective (map rs f) :=
  @Surjective.of_comp _ _ _ _ (mkQ (rs • ⊤)) <|
    show Surjective ⇑(map rs f ∘ₗ mkQ (rs • ⊤)) from
    Eq.mpr (congrArg (Surjective ∘ DFunLike.coe) (liftQ_mkQ _ _ _)) <|
      (mkQ_surjective _).comp hf

lemma map_exact (rs : List R) {f : M →ₗ[R] M'} {g : M' →ₗ[R] M''}
    (hfg : Exact f g) (hg : Surjective g) : Exact (map rs f) (map rs g) :=
  (Exact.iff_of_ladder_linearEquiv
      (equivQuotTensor_naturality rs f).symm
      (equivQuotTensor_naturality rs g).symm).mp
    (lTensor_exact (R ⧸ Ideal.span {r | r ∈ rs}) hfg hg)

end ModSMulBy

-- Should we have a default argument `(M := R)`, so that `IsWeaklyRegular rs`
-- means regular on `R` (like in standard mathematical language)?
/-- A sequence `[r₁, …, rₙ]` is weakly regular on `M` iff `rᵢ` is regular on
`M⧸(r₁, …, rᵢ₋₁)M` for all `1 ≤ i ≤ n`. -/
@[mk_iff]
structure IsWeaklyRegular (rs : List R) : Prop where
  regular_mod_prev : ∀ i (h : i < rs.length),
    IsSMulRegular (Sequence.ModSMulBy M (rs.take i)) rs[i]

section Congr

variable {M} [Module S M'] {σ : R →+* S} {σ' : S →+* R}
    [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]

lemma _root_.AddEquiv.isWeaklyRegular_congr {e : M ≃+ M'} {as bs}
    (h : List.Forall₂ (fun (r : R) (s : S) => ∀ x, e (r • x) = s • e x) as bs) :
    IsWeaklyRegular M as ↔ IsWeaklyRegular M' bs :=
  have H₁ i := by
    replace h := List.forall₂_take i h
    generalize as.take i = as' at h ⊢; generalize bs.take i = bs' at h ⊢
    induction h with
    | nil => exact AddSubgroup.map_bot _
    | cons h _ ih =>
      change ∀ x, (e : M →+ M').comp (DistribMulAction.toAddMonoidEnd R M _) x =
                    (DistribMulAction.toAddMonoidEnd S M' _).comp e x at h
      simp_rw [cons_smul, sup_toAddSubgroup, pointwise_smul_toAddSubgroup,
        top_toAddSubgroup, AddSubgroup.pointwise_smul_def, AddSubgroup.map_sup,
        ih, AddSubgroup.map_map, DFunLike.ext _ _ h, ← AddSubgroup.map_map,
        AddSubgroup.map_top_of_surjective e e.surjective]
  have H₂ i :=
    let e' : Sequence.ModSMulBy M (as.take i) ≃+ Sequence.ModSMulBy M' (bs.take i) :=
      QuotientAddGroup.congr _ _ e (H₁ i)
    forall_prop_congr
      (q' := fun h' => have := h.length_eq ▸ h'; IsSMulRegular _ bs[i])
      (fun _ => e'.isSMulRegular_congr <| (mkQ_surjective _).forall.mpr (by
        dsimp only [e']; refine congrArg (mkQ _) ?_; exact h.get _ _ ·))
      (iff_of_eq (congrArg _ h.length_eq))
  (isWeaklyRegular_iff _ _).trans <|
    (forall_congr' H₂).trans (isWeaklyRegular_iff _ _).symm

lemma _root_.LinearEquiv.isWeaklyRegular_congr' (e : M ≃ₛₗ[σ] M') (rs : List R) :
    IsWeaklyRegular M rs ↔ IsWeaklyRegular M' (rs.map σ) :=
  e.toAddEquiv.isWeaklyRegular_congr <| List.forall₂_map_right_iff.mpr <|
    List.forall₂_same.mpr fun r _ x => e.map_smul' r x

lemma _root_.LinearEquiv.isWeaklyRegular_congr (e : M ≃ₗ[R] M') (rs : List R) :
    IsWeaklyRegular M rs ↔ IsWeaklyRegular M' rs :=
  Iff.trans (e.isWeaklyRegular_congr' rs) <| iff_of_eq <| congrArg _ rs.map_id

end Congr

namespace IsWeaklyRegular

variable (R)

lemma nil : IsWeaklyRegular M ([] : List R) :=
  .mk (False.elim <| Nat.not_lt_zero · ·)

variable {R M}

lemma isWeaklyRegular_iff_isWeaklyRegular_over_quotient_by_torsion_ideal
    {I : Ideal R} (h : Module.IsTorsionBySet R M I) (rs : List R) :
      letI := h.module
      IsWeaklyRegular M rs ↔
        IsWeaklyRegular M (rs.map (Ideal.Quotient.mk I)) := by
  letI := h.module
  simp only [isWeaklyRegular_iff, List.getElem_eq_get, List.length_map, List.get_map]
  refine forall₂_congr ?_
  intro i h
  refine LinearEquiv.isSMulRegular_congr ?_ _
  refine ?_ ≪≫ₗ Quotient.restrictScalarsEquiv R ((rs.map _).take i • ⊤)
  refine quotEquivOfEq _ _ (Eq.symm ?_)
  rw [← List.map_take]
  exact restrictScalars_map_algebraMap_smul_eq_smul_restrictScalars _ _

variable (M)

lemma isWeaklyRegular_cons_iff (r : R) (rs : List R) :
    IsWeaklyRegular M (r :: rs) ↔
      IsSMulRegular M r ∧ IsWeaklyRegular (ModSMulBy M r) rs := by
  simp_rw [isWeaklyRegular_iff]
  refine Iff.trans Nat.and_forall_succ.symm ?_
  simp only [Nat.zero_lt_succ, forall_true_left,
    Nat.succ_lt_succ_iff, List.length_cons, Nat.zero_lt_succ]
  refine and_congr ?_ <| forall₂_congr fun i h => ?_ <;>
    apply LinearEquiv.isSMulRegular_congr
  · exact quotEquivOfEqBot ⊥ rfl
  · exact ModSMulBy.consEquivQuotTailQuotHead M r (rs.take i)

lemma isWeaklyRegular_cons_iff' (r : R) (rs : List R) :
    IsWeaklyRegular M (r :: rs) ↔
      IsSMulRegular M r ∧
        IsWeaklyRegular (ModSMulBy M r)
          (rs.map (Ideal.Quotient.mk (Ideal.span {r}))) :=
  have H := (Module.isTorsionBySet_span_singleton_iff r).mpr <|
    Module.isTorsionBy_quotient_element_smul M r
  Iff.trans (isWeaklyRegular_cons_iff M r rs) <| and_congr_right' <|
    isWeaklyRegular_iff_isWeaklyRegular_over_quotient_by_torsion_ideal H rs

-- TODO: Define `append_iff'` analogous to `cons_iff'`; this requires creating
-- and instance `Module (R⧸Ideal.span {r | r ∈ rs}) (ModSMulBy M rs)`
lemma isWeaklyRegular_append_iff (rs₁ rs₂ : List R) :
    IsWeaklyRegular M (rs₁ ++ rs₂) ↔
      IsWeaklyRegular M rs₁ ∧
        IsWeaklyRegular (Sequence.ModSMulBy M rs₁) rs₂ := by
  induction rs₁ generalizing M with
  | nil =>
    simp only [List.nil_append, IsWeaklyRegular.nil, true_and]
    exact ((ModSMulBy.nilEquivSelf R M).isWeaklyRegular_congr rs₂).symm
  | cons r rs₁ ih =>
    simp_rw [List.cons_append, isWeaklyRegular_cons_iff, ih, ← and_assoc]
    let e := ModSMulBy.consEquivQuotTailQuotHead M r rs₁
    exact and_congr_right' (e.isWeaklyRegular_congr rs₂).symm

variable {M}

lemma cons {r : R} {rs : List R} (h1 : IsSMulRegular M r)
    (h2 : IsWeaklyRegular (ModSMulBy M r) rs) : IsWeaklyRegular M (r :: rs) :=
  (isWeaklyRegular_cons_iff M r rs).mpr ⟨h1, h2⟩

lemma cons' {r : R} {rs : List R} (h1 : IsSMulRegular M r)
    (h2 : IsWeaklyRegular (ModSMulBy M r)
            (rs.map (Ideal.Quotient.mk (Ideal.span {r})))) :
    IsWeaklyRegular M (r :: rs) :=
  (isWeaklyRegular_cons_iff' M r rs).mpr ⟨h1, h2⟩

/-- Weakly regular sequences can be inductively characterized by:
* The empty sequence is weakly regular on any module.
* If `r` is regular on `M` and `rs` is a weakly regular sequence on `M⧸rM` then
the sequence obtained from `rs` by prepending `r` is weakly regular on `M`.

This is the induction principle produced by the inductive definition above.
The motive will usually be valued in `Prop`, but `Sort*` works too. -/
@[induction_eliminator]
def recIterModByRegular
    {motive : (M : Type v) → [AddCommGroup M] → [Module R M] → (rs : List R) →
      IsWeaklyRegular M rs → Sort*}
    (nil : (M : Type v) → [AddCommGroup M] → [Module R M] → motive M [] (nil R M))
    (cons : {M : Type v} → [AddCommGroup M] → [Module R M] → (r : R) →
      (rs : List R) → (h1 : IsSMulRegular M r) →
      (h2 : IsWeaklyRegular (ModSMulBy M r) rs) → (ih : motive (ModSMulBy M r) rs h2) →
      motive M (r :: rs) (cons h1 h2)) :
    {M : Type v} → [AddCommGroup M] → [Module R M] → {rs : List R} →
    (h : IsWeaklyRegular M rs) → motive M rs h
  | M, _, _, [], _ => nil M
  | M, _, _, r :: rs, h =>
    let ⟨h1, h2⟩ := (isWeaklyRegular_cons_iff M r rs).mp h
    cons r rs h1 h2 (recIterModByRegular nil cons h2)

/-- A simplified version of `IsWeaklyRegular.recIterModByRegular` where the
motive is not allowed to depend on the proof of `IsWeaklyRegular`. -/
def ndrecIterModByRegular
    {motive : (M : Type v) → [AddCommGroup M] → [Module R M] → (rs : List R) → Sort*}
    (nil : (M : Type v) → [AddCommGroup M] → [Module R M] → motive M [])
    (cons : {M : Type v} → [AddCommGroup M] → [Module R M] → (r : R) →
      (rs : List R) → IsSMulRegular M r → IsWeaklyRegular (ModSMulBy M r) rs →
      motive (ModSMulBy M r) rs → motive M (r :: rs))
    {M} [AddCommGroup M] [Module R M] {rs} :
    IsWeaklyRegular M rs → motive M rs :=
  recIterModByRegular (motive := (fun M _ _ rs _ => motive M rs)) nil cons

/-- An alternate induction principle from `IsWeaklyRegular.recIterModByRegular`
where we mod out by successive elements in both the module and the base ring.
This is useful for propogating certain properties of the initial `M`, e.g.
faithfulness or freeness, throughout the induction. -/
def recIterModByRegularWithRing
    {motive : (R : Type u) → [CommRing R] → (M : Type v) → [AddCommGroup M] →
      [Module R M] → (rs : List R) → IsWeaklyRegular M rs → Sort*}
    (nil : (R : Type u) → [CommRing R] → (M : Type v) → [AddCommGroup M] →
      [Module R M] → motive R M [] (nil R M))
    (cons : {R : Type u} → [CommRing R] → {M : Type v} → [AddCommGroup M] →
      [Module R M] → (r : R) → (rs : List R) → (h1 : IsSMulRegular M r) →
      (h2 : IsWeaklyRegular (ModSMulBy M r)
              (rs.map (Ideal.Quotient.mk (Ideal.span {r})))) →
      (ih : motive (R⧸Ideal.span {r}) (ModSMulBy M r)
              (rs.map (Ideal.Quotient.mk (Ideal.span {r}))) h2) →
            motive R M (r :: rs) (cons' h1 h2)) :
    {R : Type u} → [CommRing R] → {M : Type v} → [AddCommGroup M] →
    [Module R M] → {rs : List R} → (h : IsWeaklyRegular M rs) → motive R M rs h
  | R, _, M, _, _, [], _ => nil R M
  | R, _, M, _, _, r :: rs, h =>
    let ⟨h1, h2⟩ := (isWeaklyRegular_cons_iff' M r rs).mp h
    cons r rs h1 h2 (recIterModByRegularWithRing nil cons h2)
  termination_by _ _ _ _ _ rs => List.length rs

/-- A simplified version of `IsWeaklyRegular.recIterModByRegularWithRing` where
the motive is not allowed to depend on the proof of `IsWeaklyRegular`. -/
def ndrecWithRing
    {motive : (R : Type u) → [CommRing R] → (M : Type v) →
      [AddCommGroup M] → [Module R M] → (rs : List R) → Sort*}
    (nil : (R : Type u) → [CommRing R] → (M : Type v) →
      [AddCommGroup M] → [Module R M] → motive R M [])
    (cons : {R : Type u} → [CommRing R] → {M : Type v} →
      [AddCommGroup M] → [Module R M] → (r : R) → (rs : List R) →
      IsSMulRegular M r →
      IsWeaklyRegular (ModSMulBy M r)
        (rs.map (Ideal.Quotient.mk (Ideal.span {r}))) →
      motive (R⧸Ideal.span {r}) (ModSMulBy M r)
        (rs.map (Ideal.Quotient.mk (Ideal.span {r}))) →
      motive R M (r :: rs))
    {R} [CommRing R] {M} [AddCommGroup M] [Module R M] {rs} :
    IsWeaklyRegular M rs → motive R M rs :=
  recIterModByRegularWithRing (motive := (fun R _ M _ _ rs _ => motive R M rs))
    nil cons

end IsWeaklyRegular

/-- A weakly regular sequence `rs` on `M` is regular if also `M/rsM ≠ 0`. -/
@[mk_iff]
structure IsRegular (rs : List R) extends IsWeaklyRegular M rs : Prop where
  top_ne_smul : (⊤ : Submodule R M) ≠ rs • ⊤

namespace IsRegular

variable (R)

lemma nil [Nontrivial M] : IsRegular M ([] : List R) where
  toIsWeaklyRegular := IsWeaklyRegular.nil R M
  top_ne_smul h := not_subsingleton M <|
    (quotEquivOfEqBot _ rfl).toEquiv.subsingleton_congr.mp <|
      subsingleton_quotient_iff_eq_top.mpr h.symm

variable {R M}

private lemma top_eq_cons_smul_iff {r : R} {rs} :
    (⊤ : Submodule R M) = (r :: rs) • ⊤ ↔
      (⊤ : Submodule R (ModSMulBy M r)) = rs • ⊤ := by
  rw [← range_mkQ, ← Submodule.map_top, ← map_sequence_smul]
  refine Iff.trans ?_ (comap_injective_of_surjective (mkQ_surjective _)).eq_iff
  rw [comap_map_mkQ, comap_map_mkQ, sup_top_eq, cons_smul]

variable (M)

lemma isRegular_cons_iff (r : R) (rs : List R) :
    IsRegular M (r :: rs) ↔
      IsSMulRegular M r ∧ IsRegular (ModSMulBy M r) rs := by
  simp_rw [isRegular_iff, IsWeaklyRegular.isWeaklyRegular_cons_iff M r rs,
    ne_eq, top_eq_cons_smul_iff, and_assoc]

lemma isRegular_cons_iff' (r : R) (rs : List R) :
    IsRegular M (r :: rs) ↔
      IsSMulRegular M r ∧ IsRegular (ModSMulBy M r)
          (rs.map (Ideal.Quotient.mk (Ideal.span {r}))) := by
  simp_rw [isRegular_iff, IsWeaklyRegular.isWeaklyRegular_cons_iff', ne_eq,
    ← restrictScalars_inj R (R⧸Ideal.span {r}), ← Ideal.Quotient.algebraMap_eq,
    restrictScalars_map_algebraMap_smul_eq_smul_restrictScalars]
  exact Iff.trans (and_congr_right' top_eq_cons_smul_iff.not) and_assoc

variable {M}

lemma cons {r : R} {rs : List R} (h1 : IsSMulRegular M r)
    (h2 : IsRegular (ModSMulBy M r) rs) : IsRegular M (r :: rs) :=
  (isRegular_cons_iff M r rs).mpr ⟨h1, h2⟩

lemma cons' {r : R} {rs : List R} (h1 : IsSMulRegular M r)
    (h2 : IsRegular (ModSMulBy M r) (rs.map (Ideal.Quotient.mk (Ideal.span {r})))) :
    IsRegular M (r :: rs) :=
  (isRegular_cons_iff' M r rs).mpr ⟨h1, h2⟩

/-- Regular sequences can be inductively characterized by:
* The empty sequence is regular on any nonzero module.
* If `r` is regular on `M` and `rs` is a regular sequence on `M⧸rM` then the
sequence obtained from `rs` by prepending `r` is regular on `M`.

This is the induction principle produced by the inductive definition above.
The motive will usually be valued in `Prop`, but `Sort*` works too. -/
@[induction_eliminator]
def recIterModByRegular
    {motive : (M : Type v) → [AddCommGroup M] → [Module R M] → (rs : List R) →
      IsRegular M rs → Sort*}
    (nil : (M : Type v) → [AddCommGroup M] → [Module R M] → [Nontrivial M] →
      motive M [] (nil R M))
    (cons : {M : Type v} → [AddCommGroup M] → [Module R M] → (r : R) →
      (rs : List R) → (h1 : IsSMulRegular M r) → (h2 : IsRegular (ModSMulBy M r) rs) →
      (ih : motive (ModSMulBy M r) rs h2) → motive M (r :: rs) (cons h1 h2))
    {M} [AddCommGroup M] [Module R M] {rs} (h : IsRegular M rs) : motive M rs h :=
  h.toIsWeaklyRegular.recIterModByRegular
    (motive := fun N _ _ rs' h' => ∀ h'', motive N rs' ⟨h', h''⟩)
    (fun N _ _ h' =>
      haveI := (Submodule.nontrivial_iff R).mp (nontrivial_of_ne _ _ h')
      nil N)
    (fun r rs' h1 h2 h3 h4 =>
      have h5 := (isRegular_cons_iff _ _ _).mp ⟨IsWeaklyRegular.cons h1 h2, h4⟩
      cons r rs' h5.left h5.right <| h3 h5.right.top_ne_smul)
    h.top_ne_smul

/-- A simplified version of `IsRegular.recIterModByRegular` where the motive is
not allowed to depend on the proof of `IsRegular`. -/
def ndrecIterModByRegular
    {motive : (M : Type v) → [AddCommGroup M] → [Module R M] → (rs : List R) → Sort*}
    (nil : (M : Type v) → [AddCommGroup M] → [Module R M] → [Nontrivial M] → motive M [])
    (cons : {M : Type v} → [AddCommGroup M] → [Module R M] → (r : R) →
      (rs : List R) → IsSMulRegular M r → IsRegular (ModSMulBy M r) rs →
      motive (ModSMulBy M r) rs → motive M (r :: rs))
    {M} [AddCommGroup M] [Module R M] {rs} : IsRegular M rs → motive M rs :=
  recIterModByRegular (motive := (fun M _ _ rs _ => motive M rs)) nil cons

/-- An alternate induction principle from `IsRegular.recIterModByRegular` where
we mod out by successive elements in both the module and the base ring. This is
useful for propogating certain properties of the initial `M`, e.g. faithfulness
or freeness, throughout the induction. -/
def recIterModByRegularWithRing
    {motive : (R : Type u) → [CommRing R] → (M : Type v) → [AddCommGroup M] →
      [Module R M] → (rs : List R) → IsRegular M rs → Sort*}
    (nil : (R : Type u) → [CommRing R] → (M : Type v) → [AddCommGroup M] →
      [Module R M] → [Nontrivial M] → motive R M [] (nil R M))
    (cons : {R : Type u} → [CommRing R] → {M : Type v} → [AddCommGroup M] →
      [Module R M] → (r : R) → (rs : List R) → (h1 : IsSMulRegular M r) →
      (h2 : IsRegular (ModSMulBy M r)
              (rs.map (Ideal.Quotient.mk (Ideal.span {r})))) →
      (ih : motive (R⧸Ideal.span {r}) (ModSMulBy M r)
              (rs.map (Ideal.Quotient.mk (Ideal.span {r}))) h2) →
            motive R M (r :: rs) (cons' h1 h2))
    {R} [CommRing R] {M} [AddCommGroup M] [Module R M] {rs}
    (h : IsRegular M rs) : motive R M rs h :=
  h.toIsWeaklyRegular.recIterModByRegularWithRing
    (motive := fun R _ N _ _ rs' h' => ∀ h'', motive R N rs' ⟨h', h''⟩)
    (fun R _ N _ _ h' =>
      haveI := (Submodule.nontrivial_iff R).mp (nontrivial_of_ne _ _ h')
      nil R N)
    (fun r rs' h1 h2 h3 h4 =>
      have h5 := (isRegular_cons_iff' _ _ _).mp ⟨IsWeaklyRegular.cons' h1 h2, h4⟩
      cons r rs' h5.left h5.right <| h3 h5.right.top_ne_smul)
    h.top_ne_smul

/-- A simplified version of `IsRegular.recIterModByRegularWithRing` where the
motive is not allowed to depend on the proof of `IsRegular`. -/
def ndrecIterModByRegularWithRing
    {motive : (R : Type u) → [CommRing R] → (M : Type v) →
      [AddCommGroup M] → [Module R M] → (rs : List R) → Sort*}
    (nil : (R : Type u) → [CommRing R] → (M : Type v) →
      [AddCommGroup M] → [Module R M] → [Nontrivial M] → motive R M [])
    (cons : {R : Type u} → [CommRing R] → {M : Type v} →
      [AddCommGroup M] → [Module R M] → (r : R) → (rs : List R) →
      IsSMulRegular M r →
      IsRegular (ModSMulBy M r)
        (rs.map (Ideal.Quotient.mk (Ideal.span {r}))) →
      motive (R⧸Ideal.span {r}) (ModSMulBy M r)
        (rs.map (Ideal.Quotient.mk (Ideal.span {r}))) →
      motive R M (r :: rs))
    {R} [CommRing R] {M} [AddCommGroup M] [Module R M] {rs} :
    IsRegular M rs → motive R M rs :=
  recIterModByRegularWithRing (motive := (fun R _ M _ _ rs _ => motive R M rs))
    nil cons

lemma ModSMulBy_nontrivial {rs : List R} (h : IsRegular M rs) :
    Nontrivial (Sequence.ModSMulBy M rs) :=
  Submodule.Quotient.nontrivial_of_lt_top _ h.top_ne_smul.symm.lt_top

lemma nontrivial {rs : List R} (h : IsRegular M rs) : Nontrivial M :=
  haveI := ModSMulBy_nontrivial h
  (mkQ_surjective (rs • ⊤ : Submodule R M)).nontrivial

end IsRegular

variable {M}

lemma isRegular_iff_isWeaklyRegular_of_subset_jacobson_annihilator
    [Nontrivial M] [Module.Finite R M] {rs : List R}
    (h : ∀ r ∈ rs, r ∈ Ideal.jacobson (Module.annihilator R M)) :
    IsRegular M rs ↔ IsWeaklyRegular M rs :=
  Iff.trans (isRegular_iff M rs) <| and_iff_left <|
    sequence_smul_ne_top_of_subset_jacobson_annihilator h

lemma _root_.LocalRing.isRegular_iff_isWeaklyRegular_of_subset_maximalIdeal
    [LocalRing R] [Nontrivial M] [Module.Finite R M] {rs : List R}
    (h : ∀ r ∈ rs, r ∈ LocalRing.maximalIdeal R) :
    IsRegular M rs ↔ IsWeaklyRegular M rs :=
  have H h' := bot_ne_top.symm <|
    annihilator_eq_top_iff.mp (Eq.trans annihilator_top h')
  isRegular_iff_isWeaklyRegular_of_subset_jacobson_annihilator fun r hr =>
    LocalRing.jacobson_eq_maximalIdeal (Module.annihilator R M) H ▸ h r hr

lemma eq_nil_of_isRegular_on_artinian [IsArtinian R M] :
    {rs : List R} → IsRegular M rs → rs = []
  | [], _ => rfl
  | _ :: _, h =>
    Not.elim (ne_of_lt (lt_of_le_of_lt le_sup_left (h.top_ne_smul.symm.lt_top))) <|
      Eq.trans (map_top _) <| LinearMap.range_eq_top.mpr <|
        IsArtinian.surjective_of_injective_endomorphism _ <|
          And.left <| (IsRegular.isRegular_cons_iff _ _ _).mp h

variable (M')

lemma IsWeaklyRegular.isWeaklyRegular_lTensor [Module.Flat R M']
    {rs : List R} (h : IsWeaklyRegular M rs) :
    IsWeaklyRegular (M' ⊗[R] M) rs := by
  induction h with
  | nil N => exact nil R (M' ⊗[R] N)
  | @cons N _ _ r rs' h1 _ ih =>
    refine cons (h1.lTensor M') ?_
    refine (LinearEquiv.isWeaklyRegular_congr ?_ rs').mp ih
    exact ModSMulBy.tensorModSMulByEquivModSMulBy M' N r

lemma IsWeaklyRegular.isWeaklyRegular_rTensor [Module.Flat R M']
    {rs : List R} (h : IsWeaklyRegular M rs) :
    IsWeaklyRegular (M ⊗[R] M') rs := by
  induction h with
  | nil N => exact nil R (N ⊗[R] M')
  | @cons N _ _ r rs' h1 _ ih =>
    refine cons (h1.rTensor M') ?_
    refine (LinearEquiv.isWeaklyRegular_congr ?_ rs').mp ih
    exact ModSMulBy.modSMulByTensorEquivModSMulBy M' N r

-- TODO: apply the above to localization and completion (Corollary 1.1.3 in B&H)

variable {M'}

lemma ModSMulBy.map_first_exact_on_four_term_right_exact_of_isSMulRegular_last
    {M₂ M₃} [AddCommGroup M₂] [Module R M₂] [AddCommGroup M₃] [Module R M₃]
    {rs : List R} {f₁ : M →ₗ[R] M'} {f₂ : M' →ₗ[R] M₂} {f₃ : M₂ →ₗ[R] M₃}
    (h₁₂ : Exact f₁ f₂) (h₂₃ : Exact f₂ f₃) (h₃ : Surjective f₃)
    (h : IsWeaklyRegular M₃ rs) : Exact (map rs f₁) (map rs f₂) := by
  induction' h with _ _ _ N _ _ r rs h _ ih generalizing M M' M₂
  · have H₁ := (nilEquivSelf_naturality f₁).symm
    have H₂ := (nilEquivSelf_naturality f₂).symm
    exact (Exact.iff_of_ladder_linearEquiv H₁ H₂).mp h₁₂
  · specialize ih
      (_root_.ModSMulBy.map_first_exact_on_four_term_exact_of_isSMulRegular_last h₁₂ h₂₃ h)
      (_root_.ModSMulBy.map_exact r h₂₃ h₃) (_root_.ModSMulBy.map_surjective r h₃)
    have H₁ := (consEquivQuotTailQuotHead_naturality r rs f₁).symm
    have H₂ := (consEquivQuotTailQuotHead_naturality r rs f₂).symm
    exact (Exact.iff_of_ladder_linearEquiv H₁ H₂).mp ih

-- todo: modding out a complex by a regular sequence (prop 1.1.5 in B&H)

open LinearMap in
private lemma IsWeaklyRegular.swap {a b : R} (h1 : IsWeaklyRegular M [a, b])
    (h2 : torsionBy R M b = a • torsionBy R M b → torsionBy R M b = ⊥) :
    IsWeaklyRegular M [b, a] := by
  simp_rw [isWeaklyRegular_cons_iff, and_iff_left (nil _ _)] at h1 ⊢
  obtain ⟨ha, hb⟩ := h1
  rw [← isSMulRegular_iff_torsionBy_eq_bot] at h2
  specialize h2 (le_antisymm ?_ (smul_le_self_of_tower a (torsionBy R M b)))
  · refine le_of_eq_of_le ?_ <|
      IsSMulRegular.smul_top_inf_eq_smul_of_isSMulRegular_on_quot <|
        ha.of_injective _ <| ker_eq_bot.mp <| ker_liftQ_eq_bot' _ (lsmul R M b) rfl
    rw [← (IsSMulRegular.isSMulRegular_on_quot_iff_lsmul_comap_eq _ _).mp hb]
    exact (inf_eq_right.mpr (ker_le_comap _)).symm
  · rwa [ha.isSMulRegular_on_quot_iff_smul_top_inf_eq_smul_of_isSMulRegular, inf_comm, smul_comm,
      ← h2.isSMulRegular_on_quot_iff_smul_top_inf_eq_smul_of_isSMulRegular, and_iff_left hb]

-- TODO: Equivalence of permutability of regular sequences to regularity of
-- subsequences and regularity on poly ring. See [07DW] in stacks project
-- We need a theory of multivariate polynomial modules first

open ModSMulBy List in
lemma IsWeaklyRegular.prototype_perm {rs : List R} (h : IsWeaklyRegular M rs)
    {rs'} (h'' : rs ~ rs') (h' : ∀ a b rs', (a :: b :: rs') <+~ rs →
      let K := torsionBy R (Sequence.ModSMulBy M rs') b; K = a • K → K = ⊥) :
    IsWeaklyRegular M rs' :=
  ((nilEquivSelf R M).isWeaklyRegular_congr rs').mp <|
    (aux [] h'' (.refl rs) (h''.symm.subperm)) <|
      ((nilEquivSelf R M).isWeaklyRegular_congr rs).mpr h
  where aux {rs₁ rs₂} (rs₀ : List R)
    (h₁₂ : rs₁ ~ rs₂) (H₁ : rs₀ ++ rs₁ <+~ rs) (H₃ : rs₀ ++ rs₂ <+~ rs)
    (h : IsWeaklyRegular (Sequence.ModSMulBy M rs₀) rs₁) :
    IsWeaklyRegular (Sequence.ModSMulBy M rs₀) rs₂ := by {
  induction h₁₂ generalizing rs₀ with
  | nil => exact .nil R _
  | cons r _ ih =>
    let e := (equivOfPerm M (perm_append_singleton r rs₀).symm) ≪≫ₗ
      appendEquivQuotQuot _ _ _ ≪≫ₗ quotEquivOfEq _ _ (singleton_smul r ⊤)
    simp only [isWeaklyRegular_cons_iff, ← e.isWeaklyRegular_congr] at h ⊢
    refine h.imp_right (ih (r :: rs₀) ?_ ?_)
    <;> refine perm_middle.subperm_right.mp ?_ <;> assumption
  | swap a b =>
    erw [isWeaklyRegular_append_iff _ [_, _]] at h ⊢
    rw [(equivOfPerm _ (.swap a b [])).isWeaklyRegular_congr] at h
    rw [append_cons, append_cons, append_assoc _ [b] [a]] at H₁
    apply (sublist_append_left (rs₀ ++ [b, a]) _).subperm.trans at H₁
    apply perm_append_comm.subperm.trans at H₁
    exact h.imp_left (swap · (h' b a rs₀ H₁))
  | trans h₁₂ _ ih₁₂ ih₂₃ =>
    have H₂ := (h₁₂.append_left rs₀).subperm_right.mp H₁
    exact ih₂₃ rs₀ H₂ H₃ (ih₁₂ rs₀ H₁ H₂ h) }

-- putting `{rs' : List R}` and `h2` after `h3` would be better for partial
-- application, but this argument order seems nicer overall
lemma IsWeaklyRegular.of_perm_of_subset_jacobson_annihilator [IsNoetherian R M]
    {rs rs' : List R} (h1 : IsWeaklyRegular M rs) (h2 : List.Perm rs rs')
    (h3 : ∀ r ∈ rs, r ∈ (Module.annihilator R M).jacobson) :
    IsWeaklyRegular M rs' :=
  h1.prototype_perm h2 fun r _ xs h h' =>
    have h4 : Module.annihilator R M ≤ Module.annihilator R (M ⧸ xs • ⊤) :=
      LinearMap.annihilator_le_of_surjective _ (mkQ_surjective _)
    eq_bot_of_eq_pointwise_smul_of_mem_jacobson_annihilator
      (IsNoetherian.noetherian _) h'
      (Ideal.jacobson_mono
        (le_trans h4 (LinearMap.annihilator_le_of_injective _ (injective_subtype _)))
        (h3 r (h.subset (List.mem_cons_self _ _))))

lemma IsRegular.of_perm_of_subset_jacobson_annihilator [IsNoetherian R M]
    {rs rs' : List R} (h1 : IsRegular M rs) (h2 : List.Perm rs rs')
    (h3 : ∀ r ∈ rs, r ∈ (Module.annihilator R M).jacobson) : IsRegular M rs' :=
  ⟨h1.toIsWeaklyRegular.of_perm_of_subset_jacobson_annihilator h2 h3,
    letI := h1.nontrivial
    sequence_smul_ne_top_of_subset_jacobson_annihilator (h3 · ∘ h2.mem_iff.mpr)⟩

lemma _root_.LocalRing.isWeaklyRegular_of_perm_of_subset_maximalIdeal
    [LocalRing R] [IsNoetherian R M] {rs rs' : List R}
    (h1 : IsWeaklyRegular M rs) (h2 : List.Perm rs rs')
    (h3 : ∀ r ∈ rs, r ∈ LocalRing.maximalIdeal R) : IsWeaklyRegular M rs' :=
  IsWeaklyRegular.of_perm_of_subset_jacobson_annihilator h1 h2 fun r hr =>
    LocalRing.maximalIdeal_le_jacobson _ (h3 r hr)

lemma _root_.LocalRing.isRegular_of_perm [LocalRing R] [IsNoetherian R M]
    {rs rs' : List R} (h1 : IsRegular M rs) (h2 : List.Perm rs rs') :
    IsRegular M rs' := by
  obtain ⟨h3, h4⟩ := h1
  refine ⟨LocalRing.isWeaklyRegular_of_perm_of_subset_maximalIdeal h3 h2 ?_, ?_⟩
  · intro x (h6 : x ∈ { r | r ∈ rs })
    refine LocalRing.le_maximalIdeal (fun H => h4 ?_) (Ideal.subset_span h6)
    rw [sequence_smul_eq_ideal_span_smul, H, top_smul]
  · refine ne_of_ne_of_eq h4 ?_
    simp_rw [sequence_smul_eq_set_smul]
    exact congrArg (· • ⊤) <| Set.ext (fun _ => h2.mem_iff)

end RingTheory.Sequence
