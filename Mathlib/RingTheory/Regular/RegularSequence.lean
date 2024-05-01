/-
Copyright (c) 2024 Brendan Murphy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brendan Murphy
-/
import Mathlib.RingTheory.Regular.IsSMulRegular
import Mathlib.RingTheory.Artinian
import Mathlib.RingTheory.Flat.Basic
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.Logic.Equiv.TransferInstance

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

variable (R : Type u) {S : Type*} (M : Type v) {M' : Type*}

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

lemma sequence_smul_eq_ideal_span_smul (rs : List R) (N : Submodule R M) :
    rs • N = Ideal.span { r | r ∈ rs } • N :=
  Eq.trans (sequence_smul_eq_set_smul rs N) (span_smul_eq _ _).symm

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

section

variable {R M} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup M'] [Module R M']

/-- Modding out by a sequence is the same as taking iterated quotients by each term. -/
def _root_.Submodule.quotientConsSmulEquivQuotientQuotientTailSmul
    (N : Submodule R M) (r : R) (rs : List R) :
    (M ⧸ (r::rs) • N) ≃ₗ[R] (M ⧸ r • N) ⧸ rs • N.map (r • N).mkQ :=
  have h1 := congrArg (r • N ⊔ ·) (sequence_smul_eq_ideal_span_smul rs N)
  have h2 := by rw [Submodule.map_sup, mkQ_map_self, bot_sup_eq, map_smul'',
    sequence_smul_eq_ideal_span_smul]
  quotEquivOfEq _ _ h1 ≪≫ₗ
    (quotientQuotientEquivQuotient _ _ le_sup_left).symm ≪≫ₗ
      quotEquivOfEq _ _ h2

variable (M)

/-- A sequence `[r₁, …, rₙ]` is weakly regular on `M` iff `rᵢ` is regular on
`M⧸(r₁, …, rᵢ₋₁)M` for all `1 ≤ i ≤ n`. -/
@[mk_iff]
structure IsWeaklyRegular (rs : List R) : Prop where
  regular_mod_prev : ∀ i (h : i < rs.length),
    IsSMulRegular (M⧸(rs.take i • (⊤ : Submodule R M))) rs[i]

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
      IsSMulRegular M r ∧
        IsWeaklyRegular (M⧸(r • (⊤ : Submodule R M))) rs := by
  simp_rw [isWeaklyRegular_iff]
  refine Iff.trans Nat.and_forall_succ.symm ?_
  simp only [Nat.zero_lt_succ, forall_true_left,
    Nat.succ_lt_succ_iff, List.length_cons, Nat.zero_lt_succ]
  refine and_congr ?_ <| forall₂_congr fun i h => ?_ <;>
    apply LinearEquiv.isSMulRegular_congr
  · exact quotEquivOfEqBot ⊥ rfl
  · refine quotientConsSmulEquivQuotientQuotientTailSmul _ _ _ ≪≫ₗ ?_
    refine quotEquivOfEq _ _ (congrArg _ ?_)
    exact Eq.trans (map_top _) (range_mkQ _)

lemma isWeaklyRegular_cons_iff' (r : R) (rs : List R) :
    IsWeaklyRegular M (r::rs) ↔
      IsSMulRegular M r ∧
        IsWeaklyRegular (M⧸(r • (⊤ : Submodule R M)))
          (rs.map (Ideal.Quotient.mk (Ideal.span {r}))) :=
  have H := (Module.isTorsionBySet_span_singleton_iff r).mpr <|
    Module.isTorsionBy_quotient_element_smul M r
  Iff.trans (isWeaklyRegular_cons_iff M r rs) <| and_congr_right' <|
    isWeaklyRegular_iff_isWeaklyRegular_over_quotient_by_torsion_ideal H rs

variable {M}

lemma cons {r : R} {rs : List R} (h1 : IsSMulRegular M r)
    (h2 : IsWeaklyRegular (M⧸(r • (⊤ : Submodule R M))) rs) :
    IsWeaklyRegular M (r::rs) :=
  (isWeaklyRegular_cons_iff M r rs).mpr ⟨h1, h2⟩

lemma cons' {r : R} {rs : List R} (h1 : IsSMulRegular M r)
    (h2 : IsWeaklyRegular (M⧸(r • (⊤ : Submodule R M)))
            (rs.map (Ideal.Quotient.mk (Ideal.span {r})))) :
    IsWeaklyRegular M (r::rs) :=
  (isWeaklyRegular_cons_iff' M r rs).mpr ⟨h1, h2⟩

/-- Weakly regular sequences can be inductively characterized by:
* The empty sequence is weakly regular on any module.
* If `r` is regular on `M` and `rs` is a weakly regular sequence on `M⧸rM` then
the sequence obtained from `rs` by prepending `r` is weakly regular on `M`.

This is the induction principle produced by the inductive definition above.
The motive will usually be valued in `Prop`, but `Sort*` works too. -/
@[eliminator]
def recIterModByRegular
    {motive : (M : Type v) → [AddCommGroup M] → [Module R M] → (rs : List R) →
      IsWeaklyRegular M rs → Sort*}
    (nil : (M : Type v) → [AddCommGroup M] → [Module R M] → motive M [] (nil R M))
    (cons : {M : Type v} → [AddCommGroup M] → [Module R M] → (r : R) →
      (rs : List R) → (h1 : IsSMulRegular M r) →
      (h2 : IsWeaklyRegular (M⧸r • ⊤) rs) → (ih : motive (M⧸r • ⊤) rs h2) →
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
    (cons : {M : Type v} → [AddCommGroup M] → [Module R M] → (r : R) → (rs : List R) →
      IsSMulRegular M r → IsWeaklyRegular (M⧸r • (⊤ : Submodule R M)) rs →
      motive (M⧸r • (⊤ : Submodule R M)) rs → motive M (r::rs))
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
      (h2 : IsWeaklyRegular (M⧸r • ⊤)
              (rs.map (Ideal.Quotient.mk (Ideal.span {r})))) →
      (ih : motive (R⧸Ideal.span {r}) (M⧸r • ⊤)
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
      IsWeaklyRegular (M⧸r • (⊤ : Submodule R M))
        (rs.map (Ideal.Quotient.mk (Ideal.span {r}))) →
      motive (R⧸Ideal.span {r}) (M⧸r • (⊤ : Submodule R M))
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
      rs • (⊤ : Submodule R (M⧸r • (⊤ : Submodule R M))) = ⊤ := by
  rw [← range_mkQ, ← Submodule.map_top, ← map_sequence_smul]
  refine Iff.trans ?_ (comap_injective_of_surjective (mkQ_surjective _)).eq_iff
  rw [comap_map_mkQ, comap_map_mkQ, sup_top_eq, cons_smul]

lemma isRegular_cons_iff (r : R) (rs : List R) :
    IsRegular M (r::rs) ↔
      IsSMulRegular M r ∧ IsRegular (M⧸(r • (⊤ : Submodule R M))) rs := by
  simp_rw [isRegular_iff, IsWeaklyRegular.isWeaklyRegular_cons_iff M r rs,
    ne_eq, cons_smul_eq_top_iff M, and_assoc]

lemma isRegular_cons_iff' (r : R) (rs : List R) :
    IsRegular M (r::rs) ↔
      IsSMulRegular M r ∧ IsRegular (M⧸(r • (⊤ : Submodule R M)))
          (rs.map (Ideal.Quotient.mk (Ideal.span {r}))) := by
  simp_rw [isRegular_iff, IsWeaklyRegular.isWeaklyRegular_cons_iff', ne_eq,
    ← restrictScalars_inj R (R⧸_), ← Ideal.Quotient.algebraMap_eq,
    restrictScalars_map_algebraMap_smul_eq_smul_restrictScalars]
  exact Iff.trans (and_congr_right' (cons_smul_eq_top_iff M).not) and_assoc

variable {M}

lemma cons {r : R} {rs : List R} (h1 : IsSMulRegular M r)
    (h2 : IsRegular (M⧸(r • (⊤ : Submodule R M))) rs) :
    IsRegular M (r::rs) :=
  (isRegular_cons_iff M r rs).mpr ⟨h1, h2⟩

lemma cons' {r : R} {rs : List R} (h1 : IsSMulRegular M r)
    (h2 : IsRegular (M⧸(r • (⊤ : Submodule R M)))
            (rs.map (Ideal.Quotient.mk (Ideal.span {r})))) :
    IsRegular M (r::rs) :=
  (isRegular_cons_iff' M r rs).mpr ⟨h1, h2⟩

/-- Regular sequences can be inductively characterized by:
* The empty sequence is regular on any nonzero module.
* If `r` is regular on `M` and `rs` is a regular sequence on `M⧸rM` then the
sequence obtained from `rs` by prepending `r` is regular on `M`.

This is the induction principle produced by the inductive definition above.
The motive will usually be valued in `Prop`, but `Sort*` works too. -/
@[eliminator]
def recIterModByRegular
    {motive : (M : Type v) → [AddCommGroup M] → [Module R M] → (rs : List R) →
      IsRegular M rs → Sort*}
    (nil : (M : Type v) → [AddCommGroup M] → [Module R M] → [Nontrivial M] →
      motive M [] (nil R M))
    (cons : {M : Type v} → [AddCommGroup M] → [Module R M] → (r : R) →
      (rs : List R) → (h1 : IsSMulRegular M r) → (h2 : IsRegular (M⧸r • ⊤) rs) →
      (ih : motive (M⧸r • ⊤) rs h2) → motive M (r::rs) (cons h1 h2))
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
      (rs : List R) → IsSMulRegular M r → IsRegular (M⧸r • (⊤ : Submodule R M)) rs →
      motive (M⧸r • (⊤ : Submodule R M)) rs → motive M (r::rs))
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
      (h2 : IsRegular (M⧸r • ⊤)
              (rs.map (Ideal.Quotient.mk (Ideal.span {r})))) →
      (ih : motive (R⧸Ideal.span {r}) (M⧸r • ⊤)
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
      IsRegular (M⧸r • (⊤ : Submodule R M))
        (rs.map (Ideal.Quotient.mk (Ideal.span {r}))) →
      motive (R⧸Ideal.span {r}) (M⧸r • (⊤ : Submodule R M))
        (rs.map (Ideal.Quotient.mk (Ideal.span {r}))) →
      motive R M (r::rs))
    {R} [CommRing R] {M} [AddCommGroup M] [Module R M] {rs} :
    IsRegular M rs → motive R M rs :=
  recIterModByRegularWithRing (motive := (fun R _ M _ _ rs _ => motive R M rs))
    nil cons

end IsRegular

lemma isRegular_iff_isWeaklyRegular_of_subset_jacobson_radical [Nontrivial M]
    [Module.Finite R M] {rs : List R} (h1 : ∀ r ∈ rs, r ∈ Ideal.jacobson ⊥) :
    IsRegular M rs ↔ IsWeaklyRegular M rs :=
  Iff.trans (isRegular_iff M rs) <| and_iff_left fun h2 =>
    have h3 := eq_bot_of_le_smul_of_le_jacobson_bot _ _ Module.Finite.out <|
      le_of_eq <| Eq.trans h2.symm <| sequence_smul_eq_ideal_span_smul _ _
    nontrivial_iff_ne_bot.mp topEquiv.toEquiv.nontrivial (h3 (span_le.mpr h1))

lemma eq_nil_of_isRegular_on_nontrivial_artinian [Nontrivial M]
    [IsArtinian R M] : {rs : List R} → IsRegular M rs → rs = []
  | [], _ => rfl
  | _::_, h =>
    Not.elim (ne_of_lt (lt_of_le_of_lt le_sup_left (h.smul_ne_top.lt_top))) <|
      Eq.trans (map_top _) <| LinearMap.range_eq_top.mpr <|
        IsArtinian.surjective_of_injective_endomorphism _ <|
          And.left <| (IsRegular.isRegular_cons_iff _ _ _).mp h

open LinearMap DistribMulAction in
open scoped TensorProduct in
lemma IsWeaklyRegular.isWeaklyRegular_tensor_with_flat [Module.Flat R M']
    {rs : List R} (h : IsWeaklyRegular M rs) :
    IsWeaklyRegular (M ⊗[R] M') rs := by
  induction h with
  | nil N => exact nil R (N ⊗[R] M')
  | @cons N _ _ r rs' h1 h2 ih =>
    have h3 : r • ⊤ = range (rTensor M' (toLinearMap R N r)) :=
      Eq.trans (Submodule.map_top _) (congrArg _ (rTensor_smul_action N M' r).symm)
    let e : (N ⊗[R] M' ⧸ r • ⊤) ≃ₗ[R] (N ⧸ r • (⊤ : Submodule R N)) ⊗[R] M' :=
      quotEquivOfEq _ _ h3 ≪≫ₗ
        rTensor.equiv M' (exact_map_mkQ_range _) (mkQ_surjective _) ≪≫ₗ
          (quotEquivOfEq _ _ (Submodule.map_top _).symm).rTensor M'
    admit

end

end RingTheory.Sequence
