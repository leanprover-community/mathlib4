import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Regular.SMul
import Mathlib.Algebra.Module.Torsion
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Ideal.Quotient
import Mathlib.LinearAlgebra.Isomorphisms

open scoped Pointwise

section RandomLemmas

def Submodule.quotientSupIdealSmulEquivQuotientQuotientIdealSmul {R M}
    [CommRing R] [AddCommGroup M] [Module R M] (N K : Submodule R M)
    (I : Ideal R) : (M ⧸ (N ⊔ I • K)) ≃ₗ[R] ((M ⧸ N) ⧸ I • K.map N.mkQ) :=
  (quotientQuotientEquivQuotient _ _ le_sup_left).symm ≪≫ₗ quotEquivOfEq _ _ (by
    simp only [map_sup, mkQ_map_self, bot_sup_eq, map_smul'', map_top, range_mkQ])

lemma Submodule.map_mkQ_eq_map_mkQ_iff {R M}
    [CommRing R] [AddCommGroup M] [Module R M] (L N K : Submodule R M) :
    map L.mkQ N = map L.mkQ K ↔ L ⊔ N = L ⊔ K :=
  Iff.trans (comap_injective_of_surjective L.mkQ_surjective).eq_iff.symm <|
    iff_of_eq <| congrArg₂ _ (comap_map_mkQ L N) (comap_map_mkQ L K)

end RandomLemmas

namespace IsSMulRegular

/- A nice property of regularity is that `r` is regular on `M` iff
`t` is regular on `M` with the `ℕ[t]` (or `ℤ[t]`) module structure where
`t • m = r • m`. This should be added at some point. -/

lemma isSMulRegular_iff_ker_smul_eq_bot {R} (M : Type*) [CommRing R]
    [AddCommGroup M] [Module R M] (r : R) :
    IsSMulRegular M r ↔ LinearMap.ker (DistribMulAction.toLinearMap R M r) = ⊥ :=
  Iff.symm <| LinearMap.ker_eq_bot

lemma isSMulRegular_iff_torsionBy_top_eq_bot {R} (M : Type*) [CommRing R]
    [AddCommGroup M] [Module R M] (r : R) :
    IsSMulRegular M r ↔ Submodule.torsionBy R M r = ⊥ :=
  isSMulRegular_iff_ker_smul_eq_bot M r

lemma isSMulRegular_iff_smul_eq_zero_imp_eq_zero {R} (M : Type*) [CommRing R]
    [AddCommGroup M] [Module R M] (r : R) :
    IsSMulRegular M r ↔ (∀ x : M, r • x = 0 → x = 0) :=
  Iff.trans (isSMulRegular_iff_ker_smul_eq_bot M r) <| Submodule.eq_bot_iff _

lemma isSMulRegular_of_smul_eq_zero_imp_eq_zero {R M} [CommRing R]
    [AddCommGroup M] [Module R M] {r : R} (h : ∀ x : M, r • x = 0 → x = 0) :
    IsSMulRegular M r := (isSMulRegular_iff_smul_eq_zero_imp_eq_zero M r).mpr h

protected lemma eq_zero_of_smul_eq_zero {R M} [CommRing R]
    [AddCommGroup M] [Module R M] {r : R} {x : M}
    (h1 : IsSMulRegular M r) (h2 : r • x = 0) : x = 0 :=
  (isSMulRegular_iff_smul_eq_zero_imp_eq_zero M r).mp h1 x h2

lemma _root_.AddEquiv.isSMulRegular_iff {R S M N} [Semiring R] [Semiring S]
    [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module S N]
    (e : M ≃+ N) {r : R} {s : S} (h : ∀ x, e (r • x) = s • e x) :
    IsSMulRegular M r ↔ IsSMulRegular N s :=
  Iff.trans (e.comp_injective _).symm <|
    Iff.trans (iff_of_eq <| congrArg _ <| funext h) <| e.injective_comp _

lemma _root_.LinearEquiv.isSMulRegular_iff' {R S M N} [Semiring R] [Semiring S]
    {σ : R →+* S} {σ' : S →+* R} [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]
    [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module S N]
    (e : M ≃ₛₗ[σ] N) (r : R) : IsSMulRegular M r ↔ IsSMulRegular N (σ r) :=
  e.toAddEquiv.isSMulRegular_iff <| e.map_smul' r

lemma _root_.LinearEquiv.isSMulRegular_iff {R M N} [Semiring R] [AddCommMonoid M]
    [AddCommMonoid N] [Module R M] [Module R N] (e : M ≃ₗ[R] N) (r : R) :
    IsSMulRegular M r ↔ IsSMulRegular N r := e.isSMulRegular_iff' r

lemma isSMulRegular_on_submodule_iff_mem_imp_smul_eq_zero_imp_eq_zero {R M}
    [CommRing R] [AddCommGroup M] [Module R M] (N : Submodule R M) (r : R) :
    IsSMulRegular N r ↔ (∀ x ∈ N, r • x = 0 → x = 0) :=
  Iff.trans (isSMulRegular_iff_smul_eq_zero_imp_eq_zero N r) <|
    Iff.trans Subtype.forall <| by
      simp only [SetLike.mk_smul_mk, AddSubmonoid.mk_eq_zero]

lemma isSMulRegular_on_submodule_iff_disjoint_ker_smul_submodule {R M}
    [CommRing R] [AddCommGroup M] [Module R M] (N : Submodule R M) (r : R) :
    IsSMulRegular N r ↔
      Disjoint (LinearMap.ker (DistribMulAction.toLinearMap R M r)) N :=
  Iff.trans (isSMulRegular_on_submodule_iff_mem_imp_smul_eq_zero_imp_eq_zero N r) <|
    Iff.symm <| Iff.trans disjoint_comm Submodule.disjoint_def

lemma isSMulRegular_of_injective_of_isSMulRegular {R M N} [Semiring R]
    [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
    {f : M →ₗ[R] N} {r : R}
    (h1 : Function.Injective f) (h2 : IsSMulRegular N r) :
    IsSMulRegular M r := fun x y h' =>
  h1 <| h2 <| Eq.trans (f.map_smul r x).symm <|
    Eq.trans (congrArg f h') (f.map_smul r y)

lemma isSMulRegular_on_submodule_of_isSMulRegular {R M} [Semiring R]
    [AddCommMonoid M] [Module R M] (N : Submodule R M) (r : R)
    (h : IsSMulRegular M r) : IsSMulRegular N r :=
  isSMulRegular_of_injective_of_isSMulRegular N.injective_subtype h

lemma isSMulRegular_on_quot_iff_smul_mem_implies_mem {R M} [CommRing R]
    [AddCommGroup M] [Module R M] (N : Submodule R M) (r : R) :
    IsSMulRegular (M⧸N) r ↔ (∀ x : M, r • x ∈ N → x ∈ N) :=
  Iff.trans (isSMulRegular_iff_smul_eq_zero_imp_eq_zero _ r) <|
    Iff.trans N.mkQ_surjective.forall <| by
      simp_rw [← map_smul, N.mkQ_apply, Submodule.Quotient.mk_eq_zero]

lemma isSMulRegular_on_quot_iff_smul_comap_le {R M} [CommRing R]
    [AddCommGroup M] [Module R M] (N : Submodule R M) (r : R) :
    IsSMulRegular (M⧸N) r ↔ N.comap (DistribMulAction.toLinearMap R M r) ≤ N :=
  isSMulRegular_on_quot_iff_smul_mem_implies_mem N r

lemma mem_of_isSMulRegular_on_quot_of_smul_mem {R M} [CommRing R]
    [AddCommGroup M] [Module R M] {N : Submodule R M} {r : R} {x : M}
    (h1 : IsSMulRegular (M⧸N) r) (h2 : r • x ∈ N) : x ∈ N :=
  (isSMulRegular_on_quot_iff_smul_mem_implies_mem N r).mp h1 x h2

/-- Given a left exact sequence `0 → L → M → N`,
if `r` is regular on `L` and `N` it's regular `M` too. -/
lemma isSMulRegular_of_range_eq_ker {R L M N} [CommRing R] [AddCommGroup L]
    [AddCommGroup M] [AddCommGroup N] [Module R L] [Module R M] [Module R N]
    (f : L →ₗ[R] M) (g : M →ₗ[R] N) (hf : Function.Injective f)
    (h : LinearMap.range f = LinearMap.ker g)
    {r : R} (h1 : IsSMulRegular L r) (h2 : IsSMulRegular N r) :
    IsSMulRegular M r := by
  refine isSMulRegular_of_smul_eq_zero_imp_eq_zero ?_
  intro x hx
  obtain ⟨y, ⟨⟩⟩ := (congrArg (x ∈ ·) h).mpr <| h2.eq_zero_of_smul_eq_zero <|
    Eq.trans (g.map_smul r x).symm <| Eq.trans (congrArg _ hx) g.map_zero
  refine Eq.trans (congrArg f (h1.eq_zero_of_smul_eq_zero ?_)) f.map_zero
  exact hf <| Eq.trans (f.map_smul r y) <| Eq.trans hx f.map_zero.symm

lemma isSMulRegular_of_isSMulRegular_on_submodule_on_quotient {R M}
    [CommRing R] [AddCommGroup M] [Module R M] {N : Submodule R M} {r : R}
    (h1 : IsSMulRegular N r) (h2 : IsSMulRegular (M⧸N) r) : IsSMulRegular M r :=
  isSMulRegular_of_range_eq_ker N.subtype N.mkQ N.injective_subtype
    (Eq.trans N.range_subtype N.ker_mkQ.symm) h1 h2

lemma isSMulRegular_iff_isSMulRegular_over_quotient_by_torsion_ideal
    {R M} [CommRing R] [AddCommGroup M] [Module R M] {I : Ideal R}
    (hI : Module.IsTorsionBySet R M I) (r : R) :
      letI := hI.module
      IsSMulRegular M r ↔ IsSMulRegular M (Ideal.Quotient.mk I r) :=
  letI := hI.module
  (AddEquiv.refl M).isSMulRegular_iff fun _ => rfl

lemma isSMulRegular_on_quotient_ideal_smul_iff_isSMulRegular_over_quotient {R}
    (M : Type*) [CommRing R] [AddCommGroup M] [Module R M] (I : Ideal R) (r : R) :
    IsSMulRegular (M⧸I•(⊤ : Submodule R M)) r ↔
      IsSMulRegular (M⧸I•(⊤ : Submodule R M)) (Ideal.Quotient.mk I r) :=
  (AddEquiv.refl _).isSMulRegular_iff fun _ => rfl

end IsSMulRegular

namespace RingTheory.Sequence

open Submodule

section

variable (R : Type*) [CommSemiring R] (M : Type*) [AddCommMonoid M] [Module R M]

-- We need to choose whether we want the defeq `(r::rs) • N = r • N + rs • N` or
-- `[r₁, …, rₙ] • N = r₁ • N + ⋯ + rₙ • N`. For now we pick the first
instance : SMul (List R) (Submodule R M) where
  smul rs N := rs.foldr (fun r N' => r • N ⊔ N') ⊥

variable {M}

@[simp] lemma nil_smul (N : Submodule R M) : ([] : List R) • N = ⊥ := rfl

variable {R}

@[simp] lemma cons_smul (r : R) (rs : List R) (N : Submodule R M) :
    (r::rs) • N = r • N ⊔ rs • N := rfl

@[simp] lemma singleton_smul (r : R) (N : Submodule R M) :
    [r] • N = r • N := Eq.trans (cons_smul r [] N) (add_zero (r • N))

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
    {M'} [AddCommMonoid M'] [Module R M'] (f : M →ₗ[R] M') :
    map f (rs • N) = rs • map f N :=
  by simpa only [sequence_smul_eq_ideal_span_smul] using map_smul'' _ N f

@[simp]
lemma restrictScalars_map_algebraMap_smul_eq_smul_restrictScalars {S}
    [CommSemiring S] [Module S M] [Algebra R S] [IsScalarTower R S M]
    (rs : List R) (N : Submodule S M) :
    (rs.map (algebraMap R S) • N).restrictScalars R = rs • N.restrictScalars R := by
  simp_rw [sequence_smul_eq_ideal_span_smul, List.mem_map,
    Ideal.smul_restrictScalars_eq_restrictScalars_map_smul, Ideal.map_span]
  rfl

end

section

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]

def _root_.Submodule.quotientConsSmulEquivQuotientQuotientTailSmul
    (N : Submodule R M) (r : R) (rs : List R) :
    (M ⧸ (r::rs) • N) ≃ₗ[R] (M ⧸ r • N) ⧸ rs • N.map (r • N).mkQ :=
  quotEquivOfEq _ _ (congrArg (r • N ⊔ ·) <|
      sequence_smul_eq_ideal_span_smul rs N) ≪≫ₗ
    (r • N).quotientSupIdealSmulEquivQuotientQuotientIdealSmul _
      (Ideal.span {r | r ∈ rs }) ≪≫ₗ
        quotEquivOfEq _ _ (sequence_smul_eq_ideal_span_smul rs _).symm

variable (M)

def IsWeaklyRegular (rs : List R) := ∀ i (h : i < rs.length),
  IsSMulRegular (M⧸(rs.take i • (⊤ : Submodule R M))) rs[i]

namespace IsWeaklyRegular

variable {M}

open IsSMulRegular Module in
lemma isWeaklyRegular_iff_isWeaklyRegular_over_quotient_by_torsion_ideal
    {I : Ideal R} (h : IsTorsionBySet R M I) (rs : List R) :
      letI := h.module
      IsWeaklyRegular M rs ↔
        IsWeaklyRegular M (rs.map (Ideal.Quotient.mk I)) := by
  letI := h.module
  simp only [IsWeaklyRegular, List.getElem_eq_get, List.length_map, List.get_map]
  refine forall₂_congr ?_
  intro i h
  refine LinearEquiv.isSMulRegular_iff ?_ _
  refine ?_ ≪≫ₗ Quotient.restrictScalarsEquiv R ((rs.map _).take i • ⊤)
  refine quotEquivOfEq _ _ (Eq.symm ?_)
  rw [← List.map_take]
  exact restrictScalars_map_algebraMap_smul_eq_smul_restrictScalars _ _

variable (M)

open Module in
lemma isWeaklyRegular_on_quotient_ideal_smul_iff_isWeaklyRegular_over_quotient
    (I : Ideal R) (rs : List R) :
    IsWeaklyRegular (M⧸I•(⊤ : Submodule R M)) rs ↔
      IsWeaklyRegular (M⧸I•(⊤ : Submodule R M)) (rs.map (Ideal.Quotient.mk I)) :=
  isWeaklyRegular_iff_isWeaklyRegular_over_quotient_by_torsion_ideal _ rs

lemma isWeaklyRegular_cons_iff (r : R) (rs : List R) :
    IsWeaklyRegular M (r::rs) ↔
      IsSMulRegular M r ∧
        IsWeaklyRegular (M⧸(r • (⊤ : Submodule R M))) rs := by
  refine Iff.trans Nat.and_forall_succ.symm ?_
  simp only [IsWeaklyRegular, Nat.zero_lt_succ, forall_true_left,
    Nat.succ_lt_succ_iff, List.length_cons, Nat.zero_lt_succ]
  refine and_congr ?_ <| forall₂_congr fun i h => ?_ <;>
    apply LinearEquiv.isSMulRegular_iff
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

variable (R)

lemma nil : IsWeaklyRegular M ([] : List R) :=
  fun i h => absurd h (Nat.not_lt_zero i)

variable {R M}

lemma cons {r : R} {rs : List R} (h1 : IsSMulRegular M r)
    (h2 : IsWeaklyRegular (M⧸(r • (⊤ : Submodule R M))) rs) :
    IsWeaklyRegular M (r::rs) :=
  (isWeaklyRegular_cons_iff M r rs).mpr ⟨h1, h2⟩

open Pointwise Module
lemma cons' {r : R} {rs : List R} (h1 : IsSMulRegular M r)
    (h2 : IsWeaklyRegular (M⧸(r • (⊤ : Submodule R M)))
            (rs.map (Ideal.Quotient.mk (Ideal.span {r})))) :
    IsWeaklyRegular M (r::rs) :=
  (isWeaklyRegular_cons_iff' M r rs).mpr ⟨h1, h2⟩

@[eliminator]
def rec.{u} {R} [CommRing R]
    {motive : (M : Type u) → [AddCommGroup M] → [Module R M] → (rs : List R) →
      IsWeaklyRegular M rs → Sort*}
    (nil : (M : Type u) → [AddCommGroup M] → [Module R M] → motive M [] (nil R M))
    (cons : {M : Type u} → [AddCommGroup M] → [Module R M] → (r : R) →
      (rs : List R) → (h1 : IsSMulRegular M r) →
      (h2 : IsWeaklyRegular (M⧸r • ⊤) rs) → (ih : motive (M⧸r • ⊤) rs h2) →
      motive M (r::rs) (cons h1 h2)) :
    {M : Type u} → [AddCommGroup M] → [Module R M] → {rs : List R} →
    (h : IsWeaklyRegular M rs) → motive M rs h
  | M, _, _, [], _ => nil M
  | M, _, _, (r::rs), h =>
    let ⟨h1, h2⟩ := (isWeaklyRegular_cons_iff M r rs).mp h
    cons r rs h1 h2 (rec nil cons h2)

def ndrec.{u} {R} [CommRing R]
    {motive : (M : Type u) → [AddCommGroup M] → [Module R M] → (rs : List R) → Sort*}
    (nil : (M : Type u) → [AddCommGroup M] → [Module R M] → motive M [])
    (cons : {M : Type u} → [AddCommGroup M] → [Module R M] → (r : R) → (rs : List R) →
      IsSMulRegular M r → IsWeaklyRegular (M⧸r • (⊤ : Submodule R M)) rs →
      motive (M⧸r • (⊤ : Submodule R M)) rs → motive M (r::rs))
    {M} [AddCommGroup M] [Module R M] {rs} :
    IsWeaklyRegular M rs → motive M rs :=
  rec (motive := (fun M _ _ rs _ => motive M rs)) nil cons

def recWithRing.{v, u}
    {motive : (R : Type v) → [CommRing R] → (M : Type u) → [AddCommGroup M] →
      [Module R M] → (rs : List R) → IsWeaklyRegular M rs → Sort*}
    (nil : (R : Type v) → [CommRing R] → (M : Type u) → [AddCommGroup M] →
      [Module R M] → motive R M [] (nil R M))
    (cons : {R : Type v} → [CommRing R] → {M : Type u} → [AddCommGroup M] →
      [Module R M] → (r : R) → (rs : List R) → (h1 : IsSMulRegular M r) →
      (h2 : IsWeaklyRegular (M⧸r • ⊤)
              (rs.map (Ideal.Quotient.mk (Ideal.span {r})))) →
      (ih : motive (R⧸Ideal.span {r}) (M⧸r • ⊤)
              (rs.map (Ideal.Quotient.mk (Ideal.span {r}))) h2) →
            motive R M (r::rs) (cons' h1 h2)) :
    {R : Type v} → [CommRing R] → {M : Type u} → [AddCommGroup M] →
    [Module R M] → {rs : List R} → (h : IsWeaklyRegular M rs) → motive R M rs h
  | R, _, M, _, _, [], _ => nil R M
  | R, _, M, _, _, (r::rs), h =>
    let ⟨h1, h2⟩ := (isWeaklyRegular_cons_iff' M r rs).mp h
    cons r rs h1 h2 (recWithRing nil cons h2)
  termination_by _ _ _ _ _ rs => List.length rs

def ndrecWithRing.{v, u}
    {motive : (R : Type v) → [CommRing R] → (M : Type u) →
      [AddCommGroup M] → [Module R M] → (rs : List R) → Sort*}
    (nil : (R : Type v) → [CommRing R] → (M : Type u) →
      [AddCommGroup M] → [Module R M] → motive R M [])
    (cons : {R : Type v} → [CommRing R] → {M : Type u} →
      [AddCommGroup M] → [Module R M] → (r : R) → (rs : List R) →
      IsSMulRegular M r →
      IsWeaklyRegular (M⧸r • (⊤ : Submodule R M))
        (rs.map (Ideal.Quotient.mk (Ideal.span {r}))) →
      motive (R⧸Ideal.span {r}) (M⧸r • (⊤ : Submodule R M))
        (rs.map (Ideal.Quotient.mk (Ideal.span {r}))) →
      motive R M (r::rs))
    {R} [CommRing R] {M} [AddCommGroup M] [Module R M] {rs} :
    IsWeaklyRegular M rs → motive R M rs :=
  recWithRing (motive := (fun R _ M _ _ rs _ => motive R M rs)) nil cons

end IsWeaklyRegular

def IsRegular (rs : List R) :=
  IsWeaklyRegular M rs ∧ rs • ⊤ ≠ (⊤ : Submodule R M)

namespace IsRegular

private lemma cons_smul_eq_top_iff {r : R} {rs} :
    (r::rs) • (⊤ : Submodule R M) = ⊤ ↔
      rs • (⊤ : Submodule R (M⧸r • (⊤ : Submodule R M))) = ⊤ := by
  rw [← range_mkQ, ← Submodule.map_top, ← map_sequence_smul,
    map_mkQ_eq_map_mkQ_iff, sup_top_eq, cons_smul]

lemma isRegular_cons_iff (r : R) (rs : List R) :
    IsRegular M (r::rs) ↔
      IsSMulRegular M r ∧ IsRegular (M⧸(r • (⊤ : Submodule R M))) rs :=
  Iff.trans (and_congr_left' (IsWeaklyRegular.isWeaklyRegular_cons_iff M r rs))
    (Iff.trans (and_congr_right' (cons_smul_eq_top_iff M).not) and_assoc)

open IsWeaklyRegular in
lemma isRegular_cons_iff' (r : R) (rs : List R) :
    IsRegular M (r::rs) ↔
      IsSMulRegular M r ∧ IsRegular (M⧸(r • (⊤ : Submodule R M)))
          (rs.map (Ideal.Quotient.mk (Ideal.span {r}))) := by
  refine Iff.trans (and_congr_left' (isWeaklyRegular_cons_iff' M r rs)) ?_
  refine Iff.trans (and_congr_right' (Iff.not ?_)) and_assoc
  rw [← restrictScalars_inj R (R⧸_), ← Ideal.Quotient.algebraMap_eq,
    restrictScalars_map_algebraMap_smul_eq_smul_restrictScalars]
  exact cons_smul_eq_top_iff M

variable (R)

lemma nil [Nontrivial M] : IsRegular M ([] : List R) :=
  ⟨IsWeaklyRegular.nil R M,
    mt ((quotEquivOfEqBot _ rfl).toEquiv.subsingleton_congr.mp ∘
          subsingleton_quotient_iff_eq_top.mpr) (not_subsingleton M)⟩

variable {R M}

lemma cons {r : R} {rs : List R} (h1 : IsSMulRegular M r)
    (h2 : IsRegular (M⧸(r • (⊤ : Submodule R M))) rs) :
    IsRegular M (r::rs) :=
  (isRegular_cons_iff M r rs).mpr ⟨h1, h2⟩

lemma cons' {r : R} {rs : List R} (h1 : IsSMulRegular M r)
    (h2 : IsRegular (M⧸(r • (⊤ : Submodule R M)))
            (rs.map (Ideal.Quotient.mk (Ideal.span {r})))) :
    IsRegular M (r::rs) :=
  (isRegular_cons_iff' M r rs).mpr ⟨h1, h2⟩

@[eliminator]
def rec.{u} {R} [CommRing R]
    {motive : (M : Type u) → [AddCommGroup M] → [Module R M] → (rs : List R) →
      IsRegular M rs → Sort*}
    (nil : (M : Type u) → [AddCommGroup M] → [Module R M] → [Nontrivial M] →
      motive M [] (nil R M))
    (cons : {M : Type u} → [AddCommGroup M] → [Module R M] → (r : R) →
      (rs : List R) → (h1 : IsSMulRegular M r) → (h2 : IsRegular (M⧸r • ⊤) rs) →
      (ih : motive (M⧸r • ⊤) rs h2) → motive M (r::rs) (cons h1 h2))
    {M} [AddCommGroup M] [Module R M] {rs} (h : IsRegular M rs) : motive M rs h :=
  h.left.rec (motive := fun N _ _ rs' h' => ∀ h'', motive N rs' ⟨h', h''⟩)
    (fun N _ _ h' =>
      haveI := (Submodule.nontrivial_iff R).mp (nontrivial_of_ne _ _ h')
      nil N)
    (fun r rs' h1 h2 h3 h4 =>
      have h5 := (isRegular_cons_iff _ _ _).mp ⟨IsWeaklyRegular.cons h1 h2, h4⟩
      cons r rs' h5.left h5.right <| h3 h5.right.right)
    h.right

def ndrec.{u} {R} [CommRing R]
    {motive : (M : Type u) → [AddCommGroup M] → [Module R M] → (rs : List R) → Sort*}
    (nil : (M : Type u) → [AddCommGroup M] → [Module R M] → [Nontrivial M] → motive M [])
    (cons : {M : Type u} → [AddCommGroup M] → [Module R M] → (r : R) →
      (rs : List R) → IsSMulRegular M r → IsRegular (M⧸r • (⊤ : Submodule R M)) rs →
      motive (M⧸r • (⊤ : Submodule R M)) rs → motive M (r::rs))
    {M} [AddCommGroup M] [Module R M] {rs} : IsRegular M rs → motive M rs :=
  rec (motive := (fun M _ _ rs _ => motive M rs)) nil cons

def recWithRing.{v, u}
    {motive : (R : Type v) → [CommRing R] → (M : Type u) → [AddCommGroup M] →
      [Module R M] → (rs : List R) → IsRegular M rs → Sort*}
    (nil : (R : Type v) → [CommRing R] → (M : Type u) → [AddCommGroup M] →
      [Module R M] → [Nontrivial M] → motive R M [] (nil R M))
    (cons : {R : Type v} → [CommRing R] → {M : Type u} → [AddCommGroup M] →
      [Module R M] → (r : R) → (rs : List R) → (h1 : IsSMulRegular M r) →
      (h2 : IsRegular (M⧸r • ⊤)
              (rs.map (Ideal.Quotient.mk (Ideal.span {r})))) →
      (ih : motive (R⧸Ideal.span {r}) (M⧸r • ⊤)
              (rs.map (Ideal.Quotient.mk (Ideal.span {r}))) h2) →
            motive R M (r::rs) (cons' h1 h2))
    {R} [CommRing R] {M} [AddCommGroup M] [Module R M] {rs}
    (h : IsRegular M rs) : motive R M rs h :=
  h.left.recWithRing (motive := fun R _ N _ _ rs' h' => ∀ h'', motive R N rs' ⟨h', h''⟩)
    (fun R _ N _ _ h' =>
      haveI := (Submodule.nontrivial_iff R).mp (nontrivial_of_ne _ _ h')
      nil R N)
    (fun r rs' h1 h2 h3 h4 =>
      have h5 := (isRegular_cons_iff' _ _ _).mp ⟨IsWeaklyRegular.cons' h1 h2, h4⟩
      cons r rs' h5.left h5.right <| h3 h5.right.right)
    h.right

def ndrecWithRing.{v, u}
    {motive : (R : Type v) → [CommRing R] → (M : Type u) →
      [AddCommGroup M] → [Module R M] → (rs : List R) → Sort*}
    (nil : (R : Type v) → [CommRing R] → (M : Type u) →
      [AddCommGroup M] → [Module R M] → [Nontrivial M] → motive R M [])
    (cons : {R : Type v} → [CommRing R] → {M : Type u} →
      [AddCommGroup M] → [Module R M] → (r : R) → (rs : List R) →
      IsSMulRegular M r →
      IsRegular (M⧸r • (⊤ : Submodule R M))
        (rs.map (Ideal.Quotient.mk (Ideal.span {r}))) →
      motive (R⧸Ideal.span {r}) (M⧸r • (⊤ : Submodule R M))
        (rs.map (Ideal.Quotient.mk (Ideal.span {r}))) →
      motive R M (r::rs))
    {R} [CommRing R] {M} [AddCommGroup M] [Module R M] {rs} :
    IsRegular M rs → motive R M rs :=
  recWithRing (motive := (fun R _ M _ _ rs _ => motive R M rs)) nil cons

end IsRegular

end

end RingTheory.Sequence
