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

open scoped Pointwise

open Submodule

variable (R : Type u) {S : Type*} (M : Type v) {M' M'' : Type*}

section

variable [CommSemiring R] [CommSemiring S] [Algebra R S]
    [AddCommMonoid M] [Module R M] [Module S M] [IsScalarTower R S M]
    [AddCommMonoid M'] [Module R M']

-- We need to choose whether we want the defeq `(r::rs) • N = r • N + rs • N` or
-- `[r₁, …, rₙ] • N = r₁ • N + ⋯ + rₙ • N`. For now we pick the first
instance smulSubmodule : SMul (List R) (Submodule R M) where
  smul rs N := rs.foldr (fun r N' => r • N ⊔ N') ⊥

variable {M}

@[simp] lemma nil_smul (N : Submodule R M) : ([] : List R) • N = ⊥ := rfl

variable {R}

@[simp] lemma cons_smul (r : R) (rs : List R) (N : Submodule R M) :
    (r::rs) • N = r • N ⊔ rs • N := rfl

lemma singleton_smul (r : R) (N : Submodule R M) : [r] • N = r • N :=
  Eq.trans (cons_smul r [] N) (add_zero (r • N))

-- better for reasoning about sometimes but worse def eqs
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

@[simp]
lemma restrictScalars_map_algebraMap_smul_eq_smul_restrictScalars
    (rs : List R) (N : Submodule S M) :
    (rs.map (algebraMap R S) • N).restrictScalars R = rs • N.restrictScalars R := by
  simp_rw [sequence_smul_eq_ideal_span_smul, List.mem_map,
    Ideal.smul_restrictScalars_eq_restrictScalars_map_smul, Ideal.map_span]
  rfl

lemma smul_le_ideal_smul_of_forall_mem {I : Ideal R} {rs : List R}
    (N : Submodule R M) (h : ∀ r ∈ rs, r ∈ I) : rs • N ≤ I • N :=
  le_of_eq_of_le (sequence_smul_eq_ideal_span_smul rs N) <|
    Submodule.smul_mono_left <| Ideal.span_le.mpr h

end

variable {R M} [CommRing R] [CommRing S] [AddCommGroup M] [AddCommGroup M']
    [AddCommGroup M''] [Module R M] [Module R M'] [Module R M'']

lemma eq_bot_of_ideal_smul_eq_of_FG_of_le_jacobson_annihilator {I N}
    (h1 : I • N = N) (h2 : I ≤ N.annihilator.jacobson) (h3 : FG (M := M) N) :
    N = (⊥ : Submodule R M) :=
  Eq.trans (eq_smul_of_le_smul_of_le_jacobson h3 (ge_of_eq h1) h2)
    N.annihilator_smul

lemma eq_bot_of_element_smul_eq_of_FG_of_mem_jacobson_annihilator {r N}
    (h1 : r • N = N) (h2 : r ∈ N.annihilator.jacobson) (h3 : FG N) :
    N = (⊥ : Submodule R M) :=
  eq_bot_of_ideal_smul_eq_of_FG_of_le_jacobson_annihilator
    (Eq.trans (ideal_span_singleton_smul r N) h1)
    ((span_singleton_le_iff_mem r _).mpr h2) h3

lemma eq_bot_of_set_smul_eq_of_FG_of_subset_jacobson_annihilator {s : Set R}
    {N : Submodule R M} (h1 : s • N = N) (h2 : s ⊆ N.annihilator.jacobson)
    (h3 : FG N) : N = ⊥ :=
  eq_bot_of_ideal_smul_eq_of_FG_of_le_jacobson_annihilator
    (Eq.trans (span_smul_eq s N) h1) (span_le.mpr h2) h3

lemma eq_bot_of_sequence_smul_eq_of_FG_of_subset_jacobson_annihilator
    {rs : List R} {N : Submodule R M} (h1 : rs • N = N)
    (h2 : ∀ r ∈ rs, r ∈ N.annihilator.jacobson) (h3 : FG N) : N = ⊥ :=
  eq_bot_of_set_smul_eq_of_FG_of_subset_jacobson_annihilator
    (Eq.trans (sequence_smul_eq_set_smul rs N).symm h1) h2 h3

lemma ideal_smul_ne_top_of_le_jacobson_annihilator [Nontrivial M]
    [Module.Finite R M] {I} (h : I ≤ (Module.annihilator R M).jacobson) :
    I • ⊤ ≠ (⊤ : Submodule R M) := fun H =>
  top_ne_bot <| eq_bot_of_ideal_smul_eq_of_FG_of_le_jacobson_annihilator H
    ((congrArg (I ≤ Ideal.jacobson ·) annihilator_top).mpr h) Module.Finite.out

lemma element_smul_ne_top_of_mem_jacobson_annihilator [Nontrivial M]
    [Module.Finite R M] {r} (h : r ∈ (Module.annihilator R M).jacobson) :
    r • ⊤ ≠ (⊤ : Submodule R M) := fun H =>
  top_ne_bot <| eq_bot_of_element_smul_eq_of_FG_of_mem_jacobson_annihilator H
    ((congrArg (r ∈ Ideal.jacobson ·) annihilator_top).mpr h) Module.Finite.out

lemma set_smul_ne_top_of_subset_jacobson_annihilator [Nontrivial M]
    [Module.Finite R M] {s : Set R}
    (h : s ⊆ (Module.annihilator R M).jacobson) :
    s • ⊤ ≠ (⊤ : Submodule R M) := fun H =>
  top_ne_bot <| eq_bot_of_set_smul_eq_of_FG_of_subset_jacobson_annihilator H
    ((congrArg (fun I : Ideal R => s ⊆ I.jacobson) annihilator_top).mpr h)
    Module.Finite.out

lemma sequence_smul_ne_top_of_subset_jacobson_annihilator [Nontrivial M]
    [Module.Finite R M] {rs : List R}
    (h : ∀ r ∈ rs, r ∈ (Module.annihilator R M).jacobson) :
    rs • ⊤ ≠ (⊤ : Submodule R M) := fun H =>
  top_ne_bot <| eq_bot_of_sequence_smul_eq_of_FG_of_subset_jacobson_annihilator
    H ((congrArg (∀ r ∈ rs, r ∈ Ideal.jacobson ·) annihilator_top).mpr h)
    Module.Finite.out

variable (M)

-- Should there be a typeclass for this? Smth about a natural action on submodules?
-- or maybe we should develop the API for ideals first and foremost?
/-- An abbreviation for `M⧸(r₁, …, rₙ)M` that keeps us from having to write
`(⊤ : Submodule R M)` over and over to satisfy the typechecker. -/
protected abbrev ModSMulBy (rs : List R) := M ⧸ rs • (⊤ : Submodule R M)

namespace ModSMulBy

open Submodule Function

open TensorProduct in
noncomputable def equiv_lTensor_ring_mod (rs : List R) :
    Sequence.ModSMulBy M rs ≃ₗ[R] ((R⧸Ideal.span { r | r ∈ rs }) ⊗[R] M) :=
  quotEquivOfEq _ _ (sequence_smul_eq_ideal_span_smul _ _) ≪≫ₗ
   (lTensor_ring_mod_ideal_equiv_mod_ideal_smul M _).symm

variable (R)

def nil_equiv_self : Sequence.ModSMulBy M ([] : List R) ≃ₗ[R] M :=
  quotEquivOfEqBot ([] • ⊤) rfl

variable {R}

def cons_equiv_mod_tail_mod_head (r : R) (rs : List R) :
    Sequence.ModSMulBy M (r::rs) ≃ₗ[R] Sequence.ModSMulBy (ModSMulBy M r) rs :=
  (quotientQuotientEquivQuotientSup (r • ⊤) (rs • ⊤)).symm ≪≫ₗ
    quotEquivOfEq _ _ (by rw [map_sequence_smul, Submodule.map_top, range_mkQ])

def append_equiv_mod_mod (rs₁ rs₂ : List R) :
    Sequence.ModSMulBy M (rs₁ ++ rs₂) ≃ₗ[R]
      Sequence.ModSMulBy (Sequence.ModSMulBy M rs₁) rs₂ :=
  quotEquivOfEq _ _ (append_smul rs₁ rs₂ ⊤) ≪≫ₗ
    (quotientQuotientEquivQuotientSup _ _).symm ≪≫ₗ
      quotEquivOfEq _ _ (by rw [map_sequence_smul, Submodule.map_top, range_mkQ])

def equiv_of_subset_subset {rs₁ rs₂ : List R} (h₁₂ : rs₁ ⊆ rs₂) (h₂₁ : rs₂ ⊆ rs₁) :
    Sequence.ModSMulBy M rs₁ ≃ₗ[R] Sequence.ModSMulBy M rs₂ :=
  quotEquivOfEq _ _ <| by
    simp_rw [sequence_smul_eq_set_smul]; congr; exact subset_antisymm h₁₂ h₂₁

def equiv_of_perm {rs₁ rs₂ : List R} (h : List.Perm rs₁ rs₂) :
    Sequence.ModSMulBy M rs₁ ≃ₗ[R] Sequence.ModSMulBy M rs₂ :=
  equiv_of_subset_subset M h.subset h.symm.subset

variable {M}

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

lemma equiv_lTensor_ring_mod_naturality_apply (rs : List R) (f : M →ₗ[R] M') (x : M) :
    equiv_lTensor_ring_mod M' rs (map rs f (Submodule.Quotient.mk x)) =
      f.lTensor (R⧸Ideal.span {r | r ∈ rs})
        (equiv_lTensor_ring_mod M rs (Submodule.Quotient.mk x)) := by
  simp only [equiv_lTensor_ring_mod, LinearMap.coe_comp, comp_apply, mkQ_apply,
    LinearEquiv.trans_apply, quotEquivOfEq_mk, LinearMap.lTensor_tmul, map_apply,
    LinearEquiv.coe_coe, lTensor_ring_mod_ideal_equiv_mod_ideal_smul_symm_apply]

lemma equiv_lTensor_ring_mod_naturality (rs : List R) (f : M →ₗ[R] M') :
    equiv_lTensor_ring_mod M' rs ∘ₗ map rs f =
      f.lTensor (R⧸Ideal.span {r | r ∈ rs}) ∘ₗ equiv_lTensor_ring_mod M rs :=
  by ext x; exact equiv_lTensor_ring_mod_naturality_apply rs f x

lemma nil_equiv_self_naturality (f : M →ₗ[R] M') :
    nil_equiv_self R M' ∘ₗ map [] f = f ∘ₗ nil_equiv_self R M :=
  by ext; rfl

lemma cons_equiv_mod_tail_mod_head_naturality (r : R) (rs : List R)
    (f : M →ₗ[R] M') :
    cons_equiv_mod_tail_mod_head M' r rs ∘ₗ map (r::rs) f =
      map rs (_root_.ModSMulBy.map r f) ∘ₗ cons_equiv_mod_tail_mod_head M r rs :=
  by ext; rfl

lemma append_equiv_mod_mod_naturality (rs₁ rs₂ : List R) (f : M →ₗ[R] M') :
    append_equiv_mod_mod M' rs₁ rs₂ ∘ₗ map (rs₁ ++ rs₂) f =
      map rs₂ (map rs₁ f) ∘ₗ append_equiv_mod_mod M rs₁ rs₂ :=
  by ext; rfl

lemma equiv_of_subset_subset_naturality {rs₁ rs₂} (h₁₂ : rs₁ ⊆ rs₂)
    (h₂₁ : rs₂ ⊆ rs₁) (f : M →ₗ[R] M') :
    equiv_of_subset_subset M' h₁₂ h₂₁ ∘ₗ map rs₁ f =
      map rs₂ f ∘ₗ equiv_of_subset_subset M h₁₂ h₂₁ :=
  by ext; rfl

lemma equiv_of_perm_naturality {rs₁ rs₂} (h : List.Perm rs₁ rs₂)
    (f : M →ₗ[R] M') :
    equiv_of_perm M' h ∘ₗ map rs₁ f = map rs₂ f ∘ₗ equiv_of_perm M h :=
  by ext; rfl

lemma map_surjective (rs : List R) {f : M →ₗ[R] M'} (hf : Surjective f) :
    Surjective (map rs f) :=
  @Surjective.of_comp _ _ _ _ (mkQ (rs • ⊤)) <|
    show Surjective ⇑(map rs f ∘ₗ mkQ (rs • ⊤)) from
    Eq.mpr (congrArg (Surjective ∘ DFunLike.coe) (liftQ_mkQ _ _ _)) <|
      (mkQ_surjective _).comp hf

lemma map_exact (rs : List R) {f : M →ₗ[R] M'} {g : M' →ₗ[R] M''}
    (hfg : Exact f g) (hg : Surjective g) : Exact (map rs f) (map rs g) :=
  (Exact.iff_of_ladder_linear_equiv
      (equiv_lTensor_ring_mod_naturality rs f).symm
      (equiv_lTensor_ring_mod_naturality rs g).symm).mp
    (lTensor_exact (R⧸Ideal.span {r | r ∈ rs}) hfg hg)

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

open DistribMulAction renaming toAddMonoidEnd → toEnd in
lemma _root_.AddEquiv.isWeaklyRegular_congr {e : M ≃+ M'} {as bs}
    (h : List.Forall₂ (fun (r : R) (s : S) => ∀ x, e (r • x) = s • e x) as bs) :
    IsWeaklyRegular M as ↔ IsWeaklyRegular M' bs :=
  have H₁ i := by
    replace h := List.forall₂_take i h
    generalize as.take i = as' at h ⊢; generalize bs.take i = bs' at h ⊢
    induction h with
    | nil => exact AddSubgroup.map_bot _
    | cons h _ ih =>
      change ∀ x, (e : M →+ M').comp (toEnd R M _) x = (toEnd S M' _).comp e x at h
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
    IsWeaklyRegular M (r::rs) ↔
      IsSMulRegular M r ∧ IsWeaklyRegular (ModSMulBy M r) rs := by
  simp_rw [isWeaklyRegular_iff]
  refine Iff.trans Nat.and_forall_succ.symm ?_
  simp only [Nat.zero_lt_succ, forall_true_left,
    Nat.succ_lt_succ_iff, List.length_cons, Nat.zero_lt_succ]
  refine and_congr ?_ <| forall₂_congr fun i h => ?_ <;>
    apply LinearEquiv.isSMulRegular_congr
  · exact quotEquivOfEqBot ⊥ rfl
  · exact ModSMulBy.cons_equiv_mod_tail_mod_head M r (rs.take i)

lemma isWeaklyRegular_cons_iff' (r : R) (rs : List R) :
    IsWeaklyRegular M (r::rs) ↔
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
    exact ((ModSMulBy.nil_equiv_self R M).isWeaklyRegular_congr rs₂).symm
  | cons r rs₁ ih =>
    simp_rw [List.cons_append, isWeaklyRegular_cons_iff, ih, ← and_assoc]
    refine and_congr_right' ?_
    exact ((ModSMulBy.cons_equiv_mod_tail_mod_head M r rs₁).isWeaklyRegular_congr rs₂).symm

variable {M}

lemma cons {r : R} {rs : List R} (h1 : IsSMulRegular M r)
    (h2 : IsWeaklyRegular (ModSMulBy M r) rs) :
    IsWeaklyRegular M (r::rs) :=
  (isWeaklyRegular_cons_iff M r rs).mpr ⟨h1, h2⟩

lemma cons' {r : R} {rs : List R} (h1 : IsSMulRegular M r)
    (h2 : IsWeaklyRegular (ModSMulBy M r)
            (rs.map (Ideal.Quotient.mk (Ideal.span {r})))) :
    IsWeaklyRegular M (r::rs) :=
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
      motive M (r::rs) (cons h1 h2)) :
    {M : Type v} → [AddCommGroup M] → [Module R M] → {rs : List R} →
    (h : IsWeaklyRegular M rs) → motive M rs h
  | M, _, _, [], _ => nil M
  | M, _, _, (r::rs), h =>
    let ⟨h1, h2⟩ := (isWeaklyRegular_cons_iff M r rs).mp h
    cons r rs h1 h2 (recIterModByRegular nil cons h2)

/-- A simplified version of `IsWeaklyRegular.recIterModByRegular` where the
motive is not allowed to depend on the proof of `IsWeaklyRegular`. -/
def ndrecIterModByRegular
    {motive : (M : Type v) → [AddCommGroup M] → [Module R M] → (rs : List R) → Sort*}
    (nil : (M : Type v) → [AddCommGroup M] → [Module R M] → motive M [])
    (cons : {M : Type v} → [AddCommGroup M] → [Module R M] → (r : R) →
      (rs : List R) → IsSMulRegular M r → IsWeaklyRegular (ModSMulBy M r) rs →
      motive (ModSMulBy M r) rs → motive M (r::rs))
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
            motive R M (r::rs) (cons' h1 h2)) :
    {R : Type u} → [CommRing R] → {M : Type v} → [AddCommGroup M] →
    [Module R M] → {rs : List R} → (h : IsWeaklyRegular M rs) → motive R M rs h
  | R, _, M, _, _, [], _ => nil R M
  | R, _, M, _, _, (r::rs), h =>
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
      motive R M (r::rs))
    {R} [CommRing R] {M} [AddCommGroup M] [Module R M] {rs} :
    IsWeaklyRegular M rs → motive R M rs :=
  recIterModByRegularWithRing (motive := (fun R _ M _ _ rs _ => motive R M rs))
    nil cons

end IsWeaklyRegular

/-- A weakly regular sequence `rs` on `M` is regular if also `M/rsM ≠ 0`. -/
@[mk_iff]
structure IsRegular (rs : List R) extends IsWeaklyRegular M rs : Prop where
  smul_ne_top : rs • ⊤ ≠ (⊤ : Submodule R M)

namespace IsRegular

variable (R)

lemma nil [Nontrivial M] : IsRegular M ([] : List R) where
  toIsWeaklyRegular := IsWeaklyRegular.nil R M
  smul_ne_top h := not_subsingleton M <|
    (quotEquivOfEqBot _ rfl).toEquiv.subsingleton_congr.mp <|
      subsingleton_quotient_iff_eq_top.mpr h

variable {R}

private lemma cons_smul_eq_top_iff {r : R} {rs} :
    (r::rs) • (⊤ : Submodule R M) = ⊤ ↔
      rs • (⊤ : Submodule R (ModSMulBy M r)) = ⊤ := by
  rw [← range_mkQ, ← Submodule.map_top, ← map_sequence_smul]
  refine Iff.trans ?_ (comap_injective_of_surjective (mkQ_surjective _)).eq_iff
  rw [comap_map_mkQ, comap_map_mkQ, sup_top_eq, cons_smul]

lemma isRegular_cons_iff (r : R) (rs : List R) :
    IsRegular M (r::rs) ↔
      IsSMulRegular M r ∧ IsRegular (ModSMulBy M r) rs := by
  simp_rw [isRegular_iff, IsWeaklyRegular.isWeaklyRegular_cons_iff M r rs,
    ne_eq, cons_smul_eq_top_iff M, and_assoc]

lemma isRegular_cons_iff' (r : R) (rs : List R) :
    IsRegular M (r::rs) ↔
      IsSMulRegular M r ∧ IsRegular (ModSMulBy M r)
          (rs.map (Ideal.Quotient.mk (Ideal.span {r}))) := by
  simp_rw [isRegular_iff, IsWeaklyRegular.isWeaklyRegular_cons_iff', ne_eq,
    ← restrictScalars_inj R (R⧸Ideal.span {r}), ← Ideal.Quotient.algebraMap_eq,
    restrictScalars_map_algebraMap_smul_eq_smul_restrictScalars]
  exact Iff.trans (and_congr_right' (cons_smul_eq_top_iff M).not) and_assoc

variable {M}

lemma cons {r : R} {rs : List R} (h1 : IsSMulRegular M r)
    (h2 : IsRegular (ModSMulBy M r) rs) :
    IsRegular M (r::rs) :=
  (isRegular_cons_iff M r rs).mpr ⟨h1, h2⟩

lemma cons' {r : R} {rs : List R} (h1 : IsSMulRegular M r)
    (h2 : IsRegular (ModSMulBy M r) (rs.map (Ideal.Quotient.mk (Ideal.span {r})))) :
    IsRegular M (r::rs) :=
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
      (ih : motive (ModSMulBy M r) rs h2) → motive M (r::rs) (cons h1 h2))
    {M} [AddCommGroup M] [Module R M] {rs} (h : IsRegular M rs) : motive M rs h :=
  h.toIsWeaklyRegular.recIterModByRegular
    (motive := fun N _ _ rs' h' => ∀ h'', motive N rs' ⟨h', h''⟩)
    (fun N _ _ h' =>
      haveI := (Submodule.nontrivial_iff R).mp (nontrivial_of_ne _ _ h')
      nil N)
    (fun r rs' h1 h2 h3 h4 =>
      have h5 := (isRegular_cons_iff _ _ _).mp ⟨IsWeaklyRegular.cons h1 h2, h4⟩
      cons r rs' h5.left h5.right <| h3 h5.right.smul_ne_top)
    h.smul_ne_top

/-- A simplified version of `IsRegular.recIterModByRegular` where the motive is
not allowed to depend on the proof of `IsRegular`. -/
def ndrecIterModByRegular
    {motive : (M : Type v) → [AddCommGroup M] → [Module R M] → (rs : List R) → Sort*}
    (nil : (M : Type v) → [AddCommGroup M] → [Module R M] → [Nontrivial M] → motive M [])
    (cons : {M : Type v} → [AddCommGroup M] → [Module R M] → (r : R) →
      (rs : List R) → IsSMulRegular M r → IsRegular (ModSMulBy M r) rs →
      motive (ModSMulBy M r) rs → motive M (r::rs))
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
            motive R M (r::rs) (cons' h1 h2))
    {R} [CommRing R] {M} [AddCommGroup M] [Module R M] {rs}
    (h : IsRegular M rs) : motive R M rs h :=
  h.toIsWeaklyRegular.recIterModByRegularWithRing
    (motive := fun R _ N _ _ rs' h' => ∀ h'', motive R N rs' ⟨h', h''⟩)
    (fun R _ N _ _ h' =>
      haveI := (Submodule.nontrivial_iff R).mp (nontrivial_of_ne _ _ h')
      nil R N)
    (fun r rs' h1 h2 h3 h4 =>
      have h5 := (isRegular_cons_iff' _ _ _).mp ⟨IsWeaklyRegular.cons' h1 h2, h4⟩
      cons r rs' h5.left h5.right <| h3 h5.right.smul_ne_top)
    h.smul_ne_top

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
      motive R M (r::rs))
    {R} [CommRing R] {M} [AddCommGroup M] [Module R M] {rs} :
    IsRegular M rs → motive R M rs :=
  recIterModByRegularWithRing (motive := (fun R _ M _ _ rs _ => motive R M rs))
    nil cons

lemma ModSMulBy_nontrivial {rs : List R} (h : IsRegular M rs) :
    Nontrivial (Sequence.ModSMulBy M rs) :=
  Submodule.Quotient.nontrivial_of_lt_top _ h.smul_ne_top.lt_top

lemma nontrivial {rs : List R} (h : IsRegular M rs) : Nontrivial M :=
  haveI := ModSMulBy_nontrivial h
  (mkQ_surjective (rs • (⊤ : Submodule R M))).nontrivial

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

lemma eq_nil_of_isRegular_on_nontrivial_artinian [Nontrivial M]
    [IsArtinian R M] : {rs : List R} → IsRegular M rs → rs = []
  | [], _ => rfl
  | _::_, h =>
    Not.elim (ne_of_lt (lt_of_le_of_lt le_sup_left (h.smul_ne_top.lt_top))) <|
      Eq.trans (map_top _) <| LinearMap.range_eq_top.mpr <|
        IsArtinian.surjective_of_injective_endomorphism _ <|
          And.left <| (IsRegular.isRegular_cons_iff _ _ _).mp h

variable (M M')

open scoped TensorProduct in
open LinearMap in
noncomputable def lTensor_ModSMulBy_equiv_ModSMulBy (r : R) :
    M ⊗[R] ModSMulBy M' r ≃ₗ[R] ModSMulBy (M ⊗[R] M') r :=
  have h := congrArg _ (lTensor_smul_action M M' r)
  LinearEquiv.lTensor M (quotEquivOfEq _ _ (Submodule.map_top _)) ≪≫ₗ
    (lTensor.equiv M (exact_map_mkQ_range _) (mkQ_surjective _)).symm ≪≫ₗ
      quotEquivOfEq _ _ (Eq.trans h (Submodule.map_top _).symm)

open scoped TensorProduct in
open LinearMap in
noncomputable def rTensor_ModSMulBy_equiv_ModSMulBy (r : R) :
    ModSMulBy M' r ⊗[R] M ≃ₗ[R] ModSMulBy (M' ⊗[R] M) r :=
  have h := congrArg _ (rTensor_smul_action M M' r)
  (quotEquivOfEq _ _ (Submodule.map_top _)).rTensor M ≪≫ₗ
    (rTensor.equiv M (exact_map_mkQ_range _) (mkQ_surjective _)).symm ≪≫ₗ
      quotEquivOfEq _ _ (Eq.trans h (Submodule.map_top _).symm)

variable {M}

open scoped TensorProduct in
lemma IsWeaklyRegular.isWeaklyRegular_lTensor [Module.Flat R M']
    {rs : List R} (h : IsWeaklyRegular M rs) :
    IsWeaklyRegular (M' ⊗[R] M) rs := by
  induction h with
  | nil N => exact nil R (M' ⊗[R] N)
  | @cons N _ _ r rs' h1 _ ih =>
    refine cons (h1.isSMulRegular_lTensor M' N r) ?_
    refine (LinearEquiv.isWeaklyRegular_congr ?_ rs').mp ih
    exact lTensor_ModSMulBy_equiv_ModSMulBy M' N r

open scoped TensorProduct in
lemma IsWeaklyRegular.isWeaklyRegular_rTensor [Module.Flat R M']
    {rs : List R} (h : IsWeaklyRegular M rs) :
    IsWeaklyRegular (M ⊗[R] M') rs := by
  induction h with
  | nil N => exact nil R (N ⊗[R] M')
  | @cons N _ _ r rs' h1 _ ih =>
    refine cons (h1.isSMulRegular_rTensor M' N r) ?_
    refine (LinearEquiv.isWeaklyRegular_congr ?_ rs').mp ih
    exact rTensor_ModSMulBy_equiv_ModSMulBy M' N r

-- TODO: apply the above to localization and completion (Corollary 1.1.3 in B&H)

variable {M'}

open Function in
lemma ModSMulBy.map_first_exact_on_four_term_right_exact_of_isSMulRegular_last
    {M₂ M₃} [AddCommGroup M₂] [Module R M₂] [AddCommGroup M₃] [Module R M₃]
    {rs : List R} {f₁ : M →ₗ[R] M'} {f₂ : M' →ₗ[R] M₂} {f₃ : M₂ →ₗ[R] M₃}
    (h₁₂ : Exact f₁ f₂) (h₂₃ : Exact f₂ f₃) (h₃ : Surjective f₃)
    (h : IsWeaklyRegular M₃ rs) : Exact (map rs f₁) (map rs f₂) := by
  induction' h with _ _ _ N _ _ r rs h _ ih generalizing M M' M₂
  · apply (Exact.iff_of_ladder_linear_equiv (Eq.symm ?_) (Eq.symm ?_)).mp h₁₂
    any_goals apply nil_equiv_self_naturality
  · specialize ih
      (_root_.ModSMulBy.map_first_exact_on_four_term_exact_of_isSMulRegular_last h₁₂ h₂₃ h)
      (_root_.ModSMulBy.map_exact r h₂₃ h₃) (_root_.ModSMulBy.map_surjective r h₃)
    apply (Exact.iff_of_ladder_linear_equiv (Eq.symm ?_) (Eq.symm ?_)).mp ih
    any_goals apply cons_equiv_mod_tail_mod_head_naturality
-- todo: modding out a complex by a regular sequence (prop 1.1.5 in B&H)

open LinearMap in
private lemma IsWeaklyRegular.swap {a b : R} (h1 : IsWeaklyRegular M [a, b])
    (h2 : torsionBy R M b = a • torsionBy R M b → torsionBy R M b = ⊥) :
    IsWeaklyRegular M [b, a] := by
  simp_rw [isWeaklyRegular_cons_iff, and_iff_left (nil _ _)] at h1 ⊢
  obtain ⟨ha, hb⟩ := h1
  rw [← IsSMulRegular.isSMulRegular_iff_torsionBy_top_eq_bot] at h2
  specialize h2 (le_antisymm ?_ (smul_le_self_of_tower a (torsionBy R M b)))
  · refine le_of_eq_of_le (inf_eq_right.mpr (ker_le_comap (p := a • ⊤) _)).symm ?_
    rw [(IsSMulRegular.isSMulRegular_on_quot_iff_smul_comap_eq _ _).mp hb]
    refine IsSMulRegular.smul_top_inf_eq_smul_of_isSMulRegular_on_quot ?_
    have := ker_liftQ_eq_bot' _ (DistribMulAction.toLinearMap R M b) rfl
    exact ha.isSMulRegular_of_injective_of_isSMulRegular _ (ker_eq_bot.mp this)
  · rwa [ha.isSMulRegular_on_quot_iff_smul_top_inf_eq_smul_of_isSMulRegular, inf_comm, smul_comm,
      ← h2.isSMulRegular_on_quot_iff_smul_top_inf_eq_smul_of_isSMulRegular, and_iff_left hb]

-- TODO: Equivalence of permutability of regular sequences to regularity of
-- subsequences and regularity on poly ring. See [07DW] in stacks project

open ModSMulBy in open scoped List in
lemma IsWeaklyRegular.prototype_perm {rs : List R} (h : IsWeaklyRegular M rs)
    {rs'} (h'' : rs ~ rs') (h' : ∀ a b rs', (a :: b :: rs') <+~ rs →
      let K := torsionBy R (Sequence.ModSMulBy M rs') b; K = a • K → K = ⊥) :
    IsWeaklyRegular M rs' :=
  ((ModSMulBy.nil_equiv_self R M).isWeaklyRegular_congr rs').mp <|
    aux [] h'' (.refl rs) (h''.symm.subperm) <|
      ((ModSMulBy.nil_equiv_self R M).isWeaklyRegular_congr rs).mpr h
  where aux {rs₁ rs₂} (rs₀ : List R)
    (h₁₂ : rs₁ ~ rs₂) (H₁ : rs₀ ++ rs₁ <+~ rs) (H₃ : rs₀ ++ rs₂ <+~ rs)
    (h : IsWeaklyRegular (Sequence.ModSMulBy M rs₀) rs₁) :
    IsWeaklyRegular (Sequence.ModSMulBy M rs₀) rs₂ := by {
  induction h₁₂ generalizing rs₀ with
  | nil => exact .nil R _
  | cons r _ ih =>
    let e := (equiv_of_perm M (List.perm_append_singleton r rs₀).symm) ≪≫ₗ
      append_equiv_mod_mod _ _ _ ≪≫ₗ quotEquivOfEq _ _ (singleton_smul r ⊤)
    simp only [isWeaklyRegular_cons_iff, ← e.isWeaklyRegular_congr] at h ⊢
    refine h.imp_right (ih (r::rs₀) ?_ ?_)
    <;> refine List.perm_middle.subperm_right.mp ?_ <;> assumption
  | swap a b =>
    erw [isWeaklyRegular_append_iff _ [_, _]] at h ⊢
    rw [(equiv_of_perm _ (.swap a b [])).isWeaklyRegular_congr] at h
    rw [List.append_cons, List.append_cons, List.append_assoc _ [b] [a]] at H₁
    apply (List.sublist_append_left (rs₀ ++ [b, a]) _).subperm.trans at H₁
    apply List.perm_append_comm.subperm.trans at H₁
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
  h1.prototype_perm h2 fun r _ _ h h' =>
    eq_bot_of_element_smul_eq_of_FG_of_mem_jacobson_annihilator h'.symm
      (Ideal.jacobson_mono
        (le_trans (LinearMap.annihilator_le_of_surjective _ (mkQ_surjective _))
          (LinearMap.annihilator_le_of_injective _ (injective_subtype _)))
        (h3 r (h.subset (List.mem_cons_self _ _)))) (IsNoetherian.noetherian _)

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
  IsWeaklyRegular.of_perm_of_subset_jacobson_annihilator h1 h2 <| fun r hr =>
    LocalRing.maximalIdeal_le_jacobson _ (h3 r hr)

lemma _root_.LocalRing.isRegular_of_perm [LocalRing R] [IsNoetherian R M]
    {rs rs' : List R} (h1 : IsRegular M rs) (h2 : List.Perm rs rs') :
    IsRegular M rs' := by
  obtain ⟨h3, h4⟩ := h1
  refine ⟨LocalRing.isWeaklyRegular_of_perm_of_subset_maximalIdeal h3 h2 ?_, ?_⟩
  · intro x (h6 : x ∈ { r | r ∈ rs })
    refine LocalRing.le_maximalIdeal (fun H => h4 ?_) (Ideal.subset_span h6)
    rw [sequence_smul_eq_ideal_span_smul, H, top_smul]
  · refine ne_of_eq_of_ne ?_ h4
    simp_rw [sequence_smul_eq_set_smul]
    exact congrArg (· • ⊤) <| Set.ext (fun _ => h2.symm.mem_iff)

end RingTheory.Sequence
