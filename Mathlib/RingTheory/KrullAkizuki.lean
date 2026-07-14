/-
Copyright (c) 2026 Dokying Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dokying Yang
-/
module

public import Mathlib.LinearAlgebra.Quotient.Pi
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.HopkinsLevitzki
public import Mathlib.RingTheory.Ideal.Quotient.Noetherian
public import Mathlib.RingTheory.Length

/-!
# Krull–Akizuki theorem

The **Krull–Akizuki theorem**: if `A` is a one-dimensional Noetherian domain with
fraction field `K`, `L / K` is a finite extension, and `B` is a subring of `L` containing `A`,
then `B` is a Noetherian ring of Krull dimension at most one, and every nonzero ideal of `B` has
finite `A`-length quotient.

## Main results

- `krullAkizuki_isNoetherianRing`: `B` is a Noetherian ring.
- `krullAkizuki_dimensionLEOne`: `B` has Krull dimension at most one.
- `krullAkizuki_quotient_ideal_finiteLength`: every nonzero ideal quotient `B ⧸ J` has finite
  `A`-length.
- `krull_akizuki`: combined statement of all three conclusions.

## References

* Matsumura, *Commutative Ring Theory*, Theorem 11.7
* Stacks Project, Tag 00PG
-/

@[expose] public section

open scoped Pointwise

/-! ### Auxiliary lemmas -/

section Lemmata

variable {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]

/-- For an endomorphism `φ` of a module of finite length, the length of `ker φ` equals the
length of `coker φ`. -/
theorem length_ker_eq_length_coker
    (φ : M →ₗ[R] M) (hlen : Module.length R M < ⊤) :
    Module.length R (LinearMap.ker φ) = Module.length R (M ⧸ LinearMap.range φ) := by
  have h1 : Module.length R M =
      Module.length R (LinearMap.ker φ) + Module.length R (LinearMap.range φ) := by
    convert Module.length_eq_add_of_exact (LinearMap.ker φ).subtype (LinearMap.rangeRestrict φ)
      Subtype.coe_injective
      (fun x => ⟨Classical.choose x.2, Subtype.ext (Classical.choose_spec x.2)⟩)
      (by rw [LinearMap.exact_iff, Submodule.range_subtype, LinearMap.ker_rangeRestrict]) using 1
  have h2 : Module.length R M =
      Module.length R (LinearMap.range φ) + Module.length R (M ⧸ LinearMap.range φ) := by
    convert Module.length_eq_add_of_exact (LinearMap.range φ).subtype
      (Submodule.mkQ (LinearMap.range φ))
      Subtype.coe_injective (Submodule.mkQ_surjective _)
      (by rw [LinearMap.exact_iff, Submodule.range_subtype, Submodule.ker_mkQ]) using 1
  obtain hr | hr := eq_or_ne (Module.length R (LinearMap.range φ)) ⊤
  · exfalso; rw [hr] at h2; simp only [top_add] at h2; exact hlen.ne h2
  · exact WithTop.add_right_cancel hr (h1.symm.trans (h2.trans (add_comm _ _)))

/-- The length of `M ⧸ S` decomposes as the sum of `M ⧸ T` and `T ⧸ S` for `S ≤ T`. -/
lemma length_quotient_chain
    (S T : Submodule R M) (hST : S ≤ T) :
    Module.length R (M ⧸ S) =
      Module.length R (M ⧸ T) + Module.length R (T ⧸ S.comap T.subtype) := by
  have h_iso : (T ⧸ S.comap T.subtype) ≃ₗ[R] T.map S.mkQ :=
    (Submodule.quotEquivOfEq _ _ (by rw [LinearMap.ker_comp, Submodule.ker_mkQ])).symm.trans <|
      (LinearMap.quotKerEquivRange (S.mkQ.comp T.subtype)).trans <|
      LinearEquiv.ofEq _ _ (by rw [LinearMap.range_comp, Submodule.range_subtype])
  rw [Module.length_eq_add_of_exact (T.map S.mkQ).subtype (T.map S.mkQ).mkQ
        (Submodule.subtype_injective _) (Submodule.mkQ_surjective _)
        (LinearMap.exact_subtype_mkQ _),
      (Submodule.quotientQuotientEquivQuotient S T hST).length_eq,
      ← h_iso.length_eq,
      add_comm]

variable (A : Type*) [CommRing A]

/-- If a non-zero element `b ∈ J` is a root of a nonzero polynomial over `A`, then `J` contains a
nonzero element of `A`. -/
lemma ideal_inter_of_aeval_eq_zero
    (B : Type*) [CommRing B] [IsDomain B] [Algebra A B]
    (J : Ideal B) (b : B) (hb : b ≠ 0) (hbJ : b ∈ J)
    (p : Polynomial A) (hp : p ≠ 0) (heval : Polynomial.aeval b p = 0) :
    ∃ a : A, a ≠ 0 ∧ algebraMap A B a ∈ J := by
  obtain ⟨k, q, hq_eq, hq_zero⟩ :
      ∃ k : ℕ, ∃ q : Polynomial A, p = Polynomial.X ^ k * q ∧ q.coeff 0 ≠ 0 := by
    use Polynomial.rootMultiplicity 0 p
    have h1 := Polynomial.pow_rootMultiplicity_dvd p 0
    have h2 := Polynomial.pow_rootMultiplicity_not_dvd hp 0
    rw [Polynomial.C_0, sub_zero] at h1 h2
    obtain ⟨q, hq⟩ := h1
    refine ⟨q, hq, fun h => h2 ?_⟩
    rw [pow_succ]
    have h_dvd : Polynomial.X ^ Polynomial.rootMultiplicity 0 p * Polynomial.X ∣
        Polynomial.X ^ Polynomial.rootMultiplicity 0 p * q :=
      mul_dvd_mul_left _ (Polynomial.X_dvd_iff.mpr h)
    rw [← hq] at h_dvd
    exact h_dvd
  have h_eval_q_add : Polynomial.aeval b q = algebraMap A B (q.coeff 0) +
      b * (∑ i ∈ Finset.range q.natDegree, algebraMap A B (q.coeff (i + 1)) * b^i) := by
    rw [Polynomial.aeval_eq_sum_range]
    simp only [Finset.sum_range_succ', pow_zero, Algebra.smul_def, mul_one, pow_succ']
    have h_sum : (∑ i ∈ Finset.range q.natDegree,
          (algebraMap A B) (q.coeff (i + 1)) * (b * b ^ i)) =
        ∑ i ∈ Finset.range q.natDegree, b * ((algebraMap A B) (q.coeff (i + 1)) * b ^ i) :=
      Finset.sum_congr rfl (fun _ _ => by ring)
    rw [h_sum, ← Finset.mul_sum, add_comm]
  have hq_eval_zero : Polynomial.aeval b q = 0 := by
    have h_aeval : b ^ k * Polynomial.aeval b q = 0 := by
      rw [hq_eq, map_mul, map_pow, Polynomial.aeval_X] at heval
      exact heval
    rcases mul_eq_zero.mp h_aeval with h | h
    · exact absurd (eq_zero_of_pow_eq_zero h) hb
    · exact h
  have h_eval_q : algebraMap A B (q.coeff 0) =
      -b * (∑ i ∈ Finset.range q.natDegree, algebraMap A B (q.coeff (i + 1)) * b^i) := by
    have h_add : algebraMap A B (q.coeff 0) +
        b * (∑ i ∈ Finset.range q.natDegree, algebraMap A B (q.coeff (i + 1)) * b^i) = 0 := by
      rw [← h_eval_q_add, hq_eval_zero]
    calc algebraMap A B (q.coeff 0) =
          - (b * ∑ i ∈ Finset.range q.natDegree, algebraMap A B (q.coeff (i + 1)) * b^i) :=
            eq_neg_of_add_eq_zero_left h_add
         _ = -b * (∑ i ∈ Finset.range q.natDegree, algebraMap A B (q.coeff (i + 1)) * b^i) :=
            by ring
  refine ⟨q.coeff 0, hq_zero, ?_⟩
  rw [h_eval_q]
  apply Ideal.mul_mem_right
  exact neg_mem hbJ

variable
  (A : Type*) [CommRing A]
  (M : Type*) [AddCommGroup M] [Module A M]

/-- If every element of a finitely generated submodule `N` can be scaled into `F` by a
non-zero divisor, then a single non-zero divisor scales all of `N` into `F`. -/
theorem Submodule.exists_smul_mem_of_fg
    {F N : Submodule A M} (hNfg : N.FG)
    (hclear : ∀ x ∈ N, ∃ c ∈ nonZeroDivisors A, c • x ∈ F) :
    ∃ c ∈ nonZeroDivisors A, ∀ x ∈ N, c • x ∈ F := by
  obtain ⟨s, hs⟩ := hNfg
  choose d hd_nz hd_mem using fun x : s => hclear x.1 (hs ▸ Submodule.subset_span x.2)
  refine ⟨∏ x : s, d x, prod_mem fun x _ => hd_nz x, fun x hx => ?_⟩
  have hP : ↑s ⊆ (F.comap (LinearMap.lsmul A M (∏ x : s, d x)) : Set M) := fun y hy => by
    obtain ⟨e, he⟩ := Finset.dvd_prod_of_mem d (Finset.mem_univ ⟨y, hy⟩)
    change (∏ x : s, d x) • y ∈ F
    rw [he, mul_comm, mul_smul]
    exact F.smul_mem e (hd_mem ⟨y, hy⟩)
  exact Submodule.span_le.mpr hP (hs.symm ▸ hx)

private lemma range_smul_mkQ
    (F N : Submodule A M) (a : A) :
    LinearMap.range (a • LinearMap.id : (N ⧸ F.comap N.subtype) →ₗ[A] (N ⧸ F.comap N.subtype)) =
      Submodule.map (Submodule.mkQ (F.comap N.subtype))
        ((a • N ⊔ F).comap N.subtype) := by
  ext x
  simp only [LinearMap.mem_range, LinearMap.smul_apply, LinearMap.id_apply, Submodule.mem_map,
    Submodule.mem_comap, Submodule.mem_sup, Submodule.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨y, rfl⟩
    obtain ⟨y', rfl⟩ := Submodule.Quotient.mk_surjective _ y
    exact ⟨a • y', ⟨a • (y' : M), ⟨y', y'.property, rfl⟩, 0, F.zero_mem, add_zero _⟩, rfl⟩
  · rintro ⟨y, ⟨_, ⟨z, hz, rfl⟩, y₂, hy₂, h_add⟩, rfl⟩
    refine ⟨Submodule.Quotient.mk ⟨z, hz⟩, ?_⟩
    change Submodule.Quotient.mk (a • ⟨z, hz⟩) = Submodule.Quotient.mk y
    rw [Submodule.Quotient.eq, Submodule.mem_comap]
    change a • z - N.subtype y ∈ F
    rw [← h_add, sub_add_eq_sub_sub, sub_self, zero_sub]
    exact F.neg_mem hy₂

/-- The length of `Aʳ ⧸ (a) · Aʳ` equals `r * length(A ⧸ (a))`. -/
theorem length_free_quotient_smul
    (a : A) (r : ℕ) :
    Module.length A ((Fin r → A) ⧸ ((Ideal.span {a}) • (⊤ : Submodule A (Fin r → A))))
      = r * Module.length A (A ⧸ Ideal.span {a}) := by
  have h_iso_fin : ((Fin r → A) ⧸ Ideal.span {a} • (⊤ : Submodule A (Fin r → A))) ≃ₗ[A]
      (Fin r → (A ⧸ Ideal.span {a})) := by
    have h_free : Ideal.span {a} • (⊤ : Submodule A (Fin r → A)) =
        Submodule.pi Set.univ (fun _ => Ideal.span {a}) := by
      rw [Submodule.ideal_span_singleton_smul]
      ext x
      simp only [Submodule.mem_smul_pointwise_iff_exists, Submodule.mem_top, true_and,
        Submodule.mem_pi, Set.mem_univ, forall_true_left]
      refine ⟨fun ⟨y, hy_eq⟩ i => hy_eq ▸ Ideal.mul_mem_right (y i) _
        (Ideal.mem_span_singleton_self a), fun hx => ?_⟩
      choose f hf using fun i => Ideal.mem_span_singleton.mp (hx i)
      exact ⟨f, by ext i; rw [Pi.smul_apply, smul_eq_mul]; exact (hf i).symm⟩
    rw [h_free]
    exact Submodule.quotientPi fun _ => Ideal.span {a}
  rw [LinearEquiv.length_eq h_iso_fin, Module.length_pi,
    ENat.card_eq_coe_fintype_card, Fintype.card_fin]

private lemma length_ker_smul_eq [NoZeroSMulDivisors A M]
    (F N : Submodule A M) (a : A) (ha : a ≠ 0) :
    Module.length A (LinearMap.ker
      (a • LinearMap.id : (N ⧸ F.comap N.subtype) →ₗ[A] (N ⧸ F.comap N.subtype))) =
      Module.length A (((a • N ⊓ F).comap N.subtype) ⧸
        ((a • F).comap N.subtype).comap ((a • N ⊓ F).comap N.subtype).subtype) := by
  let F' := F.comap N.subtype
  let aNF := (a • N ⊓ F).comap N.subtype
  let aF_N := (a • F).comap N.subtype
  let K := Submodule.comap (a • LinearMap.id : ↥N →ₗ[A] ↥N) F'
  have h_cod : ∀ x : ↥K, ((a • LinearMap.id : ↥N →ₗ[A] ↥N).comp K.subtype) x ∈ aNF := by
    intro x
    refine ⟨?_, x.property⟩
    exact ⟨x.val, x.val.property, rfl⟩
  let g := LinearMap.codRestrict aNF ((a • LinearMap.id : ↥N →ₗ[A] ↥N).comp K.subtype) h_cod
  let g_q := (Submodule.mkQ (aF_N.comap aNF.subtype)).comp g
  have hF'_ker : F'.comap K.subtype ≤ LinearMap.ker g_q := by
    intro x hx
    rw [LinearMap.mem_ker]
    change Submodule.Quotient.mk (g x) = 0
    rw [Submodule.Quotient.mk_eq_zero]
    exact ⟨x.val, hx, rfl⟩
  let h := Submodule.liftQ (F'.comap K.subtype) g_q hF'_ker
  have h_bij : Function.Bijective h := by
    constructor
    · rintro ⟨x, hx⟩ ⟨y, hy⟩ hxy
      change (Submodule.Quotient.mk (⟨x, hx⟩ : K) : K ⧸ F'.comap K.subtype) =
        Submodule.Quotient.mk (⟨y, hy⟩ : K)
      rw [Submodule.Quotient.eq]
      change (x.val : M) - (y.val : M) ∈ F
      have h_diff : Submodule.Quotient.mk (g ⟨x, hx⟩) = Submodule.Quotient.mk (g ⟨y, hy⟩) := hxy
      rw [Submodule.Quotient.eq] at h_diff
      change a • (x.val : M) - a • (y.val : M) ∈ a • F at h_diff
      rw [← smul_sub, Submodule.mem_smul_pointwise_iff_exists] at h_diff
      obtain ⟨z, hz, hz_eq⟩ := h_diff
      have h_z : (z : M) = x.val - y.val := by
        refine sub_eq_zero.mp
          ((NoZeroSMulDivisors.eq_zero_or_eq_zero_of_smul_eq_zero ?_).resolve_left ha)
        rw [smul_sub, hz_eq, sub_self]
      rw [← h_z]
      exact hz
    · intro y
      obtain ⟨y_pre, rfl⟩ := Submodule.Quotient.mk_surjective _ y
      have hy_ideal : (y_pre.val : M) ∈ a • N := y_pre.property.1
      rw [Submodule.mem_smul_pointwise_iff_exists] at hy_ideal
      obtain ⟨x, hx, hx_eq⟩ := hy_ideal
      have hxK : a • x ∈ F := hx_eq.symm ▸ y_pre.property.2
      refine ⟨Submodule.Quotient.mk ⟨⟨x, hx⟩, hxK⟩, ?_⟩
      change Submodule.Quotient.mk (g ⟨⟨x, hx⟩, hxK⟩) = Submodule.Quotient.mk y_pre
      rw [Submodule.Quotient.eq]
      have h_g : g ⟨⟨x, hx⟩, hxK⟩ = y_pre := by ext; exact hx_eq
      rw [h_g, sub_self]
      exact Submodule.zero_mem _
  have h_length_K_ker : Module.length A (↥K ⧸ F'.comap K.subtype) =
      Module.length A (LinearMap.ker (a • LinearMap.id : (N ⧸ F') →ₗ[A] (N ⧸ F'))) := by
    let f_ker_pre := (Submodule.mkQ F').comp K.subtype
    have h_ker_cod : ∀ x : K, f_ker_pre x ∈
        LinearMap.ker (a • LinearMap.id : (N ⧸ F') →ₗ[A] (N ⧸ F')) := by
      intro x
      change Submodule.Quotient.mk (a • x.val) = 0
      rw [Submodule.Quotient.mk_eq_zero]
      exact x.property
    let f_ker := LinearMap.codRestrict _ f_ker_pre h_ker_cod
    have h_ker_ker : F'.comap K.subtype ≤ LinearMap.ker f_ker := by
      intro x hx
      rw [LinearMap.mem_ker]
      ext
      change Submodule.Quotient.mk x.val = 0
      rw [Submodule.Quotient.mk_eq_zero]
      exact hx
    let f_ker_lift := Submodule.liftQ _ f_ker h_ker_ker
    refine LinearEquiv.length_eq (LinearEquiv.ofBijective f_ker_lift ⟨?_, ?_⟩)
    · rintro ⟨x, hx⟩ ⟨y, hy⟩ hxy
      have h_eq : F'.mkQ x = F'.mkQ y := by
        have h_ker_eq : f_ker ⟨x, hx⟩ = f_ker ⟨y, hy⟩ := hxy
        change (f_ker ⟨x, hx⟩).val = (f_ker ⟨y, hy⟩).val
        rw [h_ker_eq]
      change (Submodule.Quotient.mk (⟨x, hx⟩ : K) : K ⧸ F'.comap K.subtype) =
        Submodule.Quotient.mk (⟨y, hy⟩ : K)
      simp only [Submodule.mkQ_apply] at h_eq
      rw [Submodule.Quotient.eq] at h_eq ⊢
      exact h_eq
    · rintro ⟨y, hy⟩
      obtain ⟨x, hx_eq⟩ := Submodule.Quotient.mk_surjective _ y
      have hxK : a • x ∈ F' := by
        change a • y = 0 at hy
        rw [← hx_eq] at hy
        change Submodule.Quotient.mk (a • x) = 0 at hy
        rw [Submodule.Quotient.mk_eq_zero] at hy
        exact hy
      refine ⟨Submodule.Quotient.mk ⟨x, hxK⟩, ?_⟩
      ext
      exact hx_eq
  rw [← h_length_K_ker]
  exact (LinearEquiv.ofBijective h h_bij).length_eq

/-- A module of rank `r` over a domain contains a free submodule of rank `r` such that
every element can be scaled into it by a non-zero divisor. -/
theorem exists_free_submodule_of_rank [IsDomain A]
    (r : ℕ) (hrank : Module.rank A M = r) :
    ∃ F : Submodule A M,
      Nonempty (F ≃ₗ[A] (Fin r → A)) ∧
      ∀ x : M, ∃ c ∈ nonZeroDivisors A, c • x ∈ F := by
  obtain ⟨v, hv⟩ : ∃ (v : Fin r → M), LinearIndependent A v :=
    exists_linearIndependent_of_le_rank hrank.symm.le
  use Submodule.span A (Set.range v)
  refine ⟨⟨(Module.Basis.span hv).equivFun⟩, fun x => ?_⟩
  have h_dep : ¬LinearIndependent A (Fin.cons x v) := fun h_ind => by
    have h_rank := h_ind.cardinal_lift_le_rank
    rw [hrank, Cardinal.mk_fin (r + 1)] at h_rank
    simp only [Cardinal.lift_natCast] at h_rank
    exact absurd h_rank (not_le.mpr (Nat.cast_lt.mpr (Nat.lt_succ_self r)))
  obtain ⟨g, hg_sum, i, hgi⟩ := Fintype.not_linearIndependent_iff.mp h_dep
  simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ] at hg_sum
  have hg0 : g 0 ≠ 0 := fun h0 => by
    simp only [h0, zero_smul, zero_add] at hg_sum
    exact hgi (Fin.cases h0
      (Fintype.linearIndependent_iff.mp hv (fun (j : Fin r) => g j.succ) hg_sum) i)
  use g 0, mem_nonZeroDivisors_iff_ne_zero.mpr hg0
  rw [add_eq_zero_iff_eq_neg] at hg_sum
  rw [hg_sum]
  exact Submodule.neg_mem _ (Submodule.sum_mem _
    fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self _)))

variable [IsNoetherianRing A]

lemma build_fg_witness
    (F : Submodule A M) (r : ℕ)
    (hF_iso : Nonempty (F ≃ₗ[A] (Fin r → A)))
    (a : A)
    (p : LTSeries (Submodule A (M ⧸ a • (⊤ : Submodule A M)))) :
    ∃ (N : Submodule A M), F ≤ N ∧ N.FG ∧
      ∃ (q : LTSeries (Submodule A N)), q.length = p.length ∧
        ∀ i, (a • N).comap N.subtype ≤ q i := by
  have hF_fg : F.FG := Module.Finite.iff_fg.mp (Module.Finite.of_injective _ hF_iso.some.injective)
  let e := Submodule.comapMkQRelIso (a • (⊤ : Submodule A M))
  let q : LTSeries (Set.Ici (a • (⊤ : Submodule A M))) := LTSeries.map p ⇑e e.strictMono
  obtain ⟨S, hS_fg, hS⟩ : ∃ S : Submodule A M, S.FG ∧ ∀ i : Fin q.length,
      (q.toFun (Fin.castSucc i)).val ≤ (q.toFun (Fin.succ i)).val ∧
        ∃ y ∈ (q.toFun (Fin.succ i)).val, y ∉ (q.toFun (Fin.castSucc i)).val ∧ y ∈ S := by
    choose y hy using fun i : Fin q.length =>
      SetLike.exists_of_lt (show (q.toFun (Fin.castSucc i)).val <
        (q.toFun (Fin.succ i)).val from q.step i)
    refine ⟨Submodule.span A (Set.range y), Submodule.fg_span (Set.finite_range y), fun i => ?_⟩
    exact ⟨(show (q.toFun (Fin.castSucc i)).val <
        (q.toFun (Fin.succ i)).val from q.step i).le,
      y i, (hy i).1, (hy i).2, Submodule.subset_span (Set.mem_range_self i)⟩
  let FS : Submodule A M := F ⊔ S
  refine ⟨FS, le_sup_left, Submodule.FG.sup hF_fg hS_fg, ?_⟩
  let q' : LTSeries (Submodule A FS) :=
    { length := q.length
      toFun := fun i => Submodule.comap (Submodule.subtype FS) (q.toFun i).val
      step := fun i =>
        have h_lt : Submodule.comap FS.subtype (q.toFun (Fin.castSucc i)).val <
            Submodule.comap FS.subtype (q.toFun (Fin.succ i)).val :=
          SetLike.lt_iff_le_and_exists.mpr (by
            obtain ⟨hle, z, hz1, hz2, hz3⟩ := hS i
            exact ⟨Submodule.comap_mono hle, ⟨z, Submodule.mem_sup_right hz3⟩, hz1, hz2⟩)
        h_lt }
  refine ⟨q', rfl, fun i x hx => ?_⟩
  obtain ⟨y, hy, hy_eq⟩ := (Submodule.mem_smul_pointwise_iff_exists x.val a FS).mp hx
  have hx_top : (x.val : M) ∈ a • (⊤ : Submodule A M) :=
    (Submodule.mem_smul_pointwise_iff_exists x.val a (⊤ : Submodule A M)).mpr
      ⟨y, Set.mem_univ y, hy_eq⟩
  exact (q.toFun i).property hx_top

variable [Ring.DimensionLEOne A]

/-- The quotient of a one-dimensional Noetherian ring by a nonzero principal ideal is
Artinian. -/
theorem quotient_isArtinian_of_nonzero
    (a : A) (ha : a ≠ 0) :
    IsArtinianRing (A ⧸ Ideal.span {a}) := by
  rw [isArtinianRing_iff_krullDimLE_zero, Ring.krullDimLE_zero_iff]
  intro I hI
  have h_max : (Ideal.comap (Ideal.Quotient.mk (Ideal.span {a})) I).IsMaximal :=
    Ideal.IsPrime.isMaximal inferInstance fun h_bot =>
      ha <| Ideal.mem_bot.mp (h_bot ▸ Ideal.mem_comap.mpr
        ((Ideal.Quotient.eq_zero_iff_mem.mpr
          (Ideal.mem_span_singleton_self a)).symm ▸ Submodule.zero_mem I))
  have h_map : Ideal.map (Ideal.Quotient.mk (Ideal.span {a}))
      (Ideal.comap (Ideal.Quotient.mk (Ideal.span {a})) I) = I :=
    Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective I
  rw [← h_map] at hI ⊢
  exact (Ideal.map_eq_top_or_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective h_max).elim
    (fun h_top => absurd h_top hI.ne_top) id

variable [IsDomain A]

/-- If `N` is finitely generated and every element of `N` can be scaled by a non-zero divisor
into `F`, then `N ⧸ F` has finite length. -/
theorem finiteLength_quotient_of_fg
    (F N : Submodule A M)
    (hNfg : N.FG)
    (hclear : ∀ x ∈ N, ∃ c ∈ nonZeroDivisors A, c • x ∈ F) :
    Module.length A (N ⧸ F.comap N.subtype) < ⊤ := by
  obtain ⟨c, hc_nz, hc_clear⟩ := Submodule.exists_smul_mem_of_fg A M hNfg hclear
  have hc_ne : c ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hc_nz
  have hc_ann : ∀ x : N ⧸ F.comap N.subtype, c • x = 0 := by
    intro x; induction x using Quotient.inductionOn with
    | h x =>
      change Submodule.Quotient.mk (c • x) = 0
      rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]
      exact hc_clear (↑x) x.property
  have htorsI : Module.IsTorsionBySet A (N ⧸ F.comap N.subtype) (Ideal.span {c}) := by
    intro x a
    obtain ⟨d, hd⟩ := Ideal.mem_span_singleton.mp a.property
    change (a : A) • x = 0
    rw [hd, mul_comm, mul_smul, hc_ann, smul_zero]
  letI := htorsI.module
  haveI : IsScalarTower A (A ⧸ Ideal.span {c}) (N ⧸ F.comap N.subtype) := htorsI.isScalarTower
  haveI : Module.Finite A N := Module.Finite.iff_fg.mpr hNfg
  haveI : Module.Finite A (N ⧸ F.comap N.subtype) := Module.Finite.quotient _ _
  haveI : Module.Finite (A ⧸ Ideal.span {c}) (N ⧸ F.comap N.subtype) :=
    Module.Finite.of_restrictScalars_finite A _ _
  haveI : IsNoetherian A (N ⧸ F.comap N.subtype) :=
    isNoetherian_of_isNoetherianRing_of_finite A _
  haveI hArt : IsArtinianRing (A ⧸ Ideal.span {c}) := quotient_isArtinian_of_nonzero A c hc_ne
  haveI : IsArtinian A (N ⧸ F.comap N.subtype) :=
    isArtinian_of_surjective_algebraMap (Ideal.Quotient.mk_surjective (I := Ideal.span {c}))
  exact lt_top_iff_ne_top.mpr Module.length_ne_top

variable [NoZeroSMulDivisors A M]

/-- The length of the quotient `N ⧸ aN` equals the length of `F ⧸ aF` when `F ≤ N`
with `N` finitely generated, the element `a` non-zero, and
every element of `N` can be scaled into `F`. -/
theorem length_quotient_smul_eq_free
    (F N : Submodule A M) (a : A) (ha : a ≠ 0)
    (hFN : F ≤ N) (hNfg : N.FG)
    (hclear : ∀ x ∈ N, ∃ c ∈ nonZeroDivisors A, c • x ∈ F) :
    Module.length A (N ⧸ (a • N).comap N.subtype)
      = Module.length A (F ⧸ (a • F).comap F.subtype) := by
  have h_snake : Module.length A (N ⧸ (a • N).comap N.subtype) =
      Module.length A (N ⧸ (a • N ⊔ F).comap N.subtype) +
      Module.length A (F ⧸ (F ⊓ a • N).comap F.subtype) := by
    rw [length_quotient_chain _ _ (Submodule.comap_mono le_sup_left)]
    congr 1
    let aN := a • N
    let T := (aN ⊔ F).comap N.subtype
    let S := aN.comap N.subtype
    let g_pre : F →ₗ[A] T :=
      { toFun := fun x => ⟨⟨x.val, hFN x.property⟩, Submodule.mem_sup_right x.property⟩
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    let g := (Submodule.mkQ (S.comap T.subtype)).comp g_pre
    have h_ker : LinearMap.ker g = (F ⊓ aN).comap F.subtype := by
      ext ⟨x, hx⟩
      simp only [g, g_pre, LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
        Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.mem_inf,
        Submodule.coe_subtype]
      exact ⟨fun h => ⟨hx, h⟩, fun h => h.2⟩
    have h_surj : LinearMap.range g = ⊤ := by
      rw [LinearMap.range_eq_top]
      rintro ⟨⟨x, hxN⟩, hxT⟩
      obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hxT
      refine ⟨⟨z, hz⟩, ?_⟩
      have h_eq : (S.comap T.subtype).mkQ ⟨⟨z, hFN hz⟩, Submodule.mem_sup_right hz⟩ =
          (S.comap T.subtype).mkQ ⟨⟨y + z, hxN⟩, hxT⟩ := by
        rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
        change z - (y + z) ∈ aN
        have h_abel : z - (y + z) = -y := by abel
        rw [h_abel]
        exact Submodule.neg_mem _ hy
      exact h_eq
    exact (LinearEquiv.length_eq (LinearEquiv.ofBijective
      (Submodule.liftQ _ g (le_of_eq h_ker.symm))
      ⟨by rw [← LinearMap.ker_eq_bot, Submodule.ker_liftQ, h_ker, Submodule.mkQ_map_self],
       by rw [← LinearMap.range_eq_top, Submodule.range_liftQ, h_surj]⟩)).symm
  have h_snake_ker : Module.length A (N ⧸ (a • N ⊔ F).comap N.subtype) =
      Module.length A (((a • N ⊓ F).comap N.subtype) ⧸
        ((a • F).comap N.subtype).comap ((a • N ⊓ F).comap N.subtype).subtype) := by
    rw [← LinearEquiv.length_eq
          (Submodule.quotientQuotientEquivQuotient _ _ (Submodule.comap_mono le_sup_right)),
        ← range_smul_mkQ A M F N a,
        ← length_ker_eq_length_coker _ (finiteLength_quotient_of_fg A M F N hNfg hclear),
        length_ker_smul_eq A M F N a ha]
  have h_decomp : Module.length A (F ⧸ (a • F).comap F.subtype) =
      Module.length A (F ⧸ (F ⊓ a • N).comap F.subtype) +
      Module.length A (((F ⊓ a • N).comap F.subtype) ⧸
        ((a • F).comap F.subtype).comap ((F ⊓ a • N).comap F.subtype).subtype) := by
    refine length_quotient_chain _ _ (fun x hx => ?_)
    simp only [Submodule.mem_comap, Submodule.mem_inf] at hx ⊢
    refine ⟨x.property, ?_⟩
    obtain ⟨y, hy, heq⟩ := (Submodule.mem_smul_pointwise_iff_exists _ a F).mp hx
    exact heq ▸ (Submodule.mem_smul_pointwise_iff_exists _ a N).mpr ⟨y, hFN hy, rfl⟩
  have h_match : Module.length A (((a • N ⊓ F).comap N.subtype) ⧸
        ((a • F).comap N.subtype).comap ((a • N ⊓ F).comap N.subtype).subtype) =
      Module.length A (((F ⊓ a • N).comap F.subtype) ⧸
        ((a • F).comap F.subtype).comap ((F ⊓ a • N).comap F.subtype).subtype) := by
    let e : ((a • N ⊓ F).comap N.subtype) ≃ₗ[A] ((F ⊓ a • N).comap F.subtype) :=
      { toFun := fun x => ⟨⟨x.val.val, x.property.2⟩, ⟨x.property.2, x.property.1⟩⟩
        invFun := fun x => ⟨⟨x.val.val, hFN x.property.1⟩, ⟨x.property.2, x.property.1⟩⟩
        left_inv := fun _ => by ext; rfl
        right_inv := fun _ => by ext; rfl
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    refine LinearEquiv.length_eq (Submodule.Quotient.equiv _ _ e ?_)
    ext x
    simp only [Submodule.mem_map, Submodule.mem_comap, Submodule.coe_subtype]
    constructor
    · rintro ⟨y, hy, hy_eq⟩
      change y.val.val ∈ a • F at hy
      have h_eq : y.val.val = x.val.val :=
        congr_arg (fun z : ((F ⊓ a • N).comap F.subtype) => z.val.val) hy_eq
      rw [h_eq] at hy
      exact hy
    · intro hx
      change x.val.val ∈ a • F at hx
      have hy_eq : e (e.symm x) = x := e.apply_symm_apply x
      have h_eq : (e.symm x).val.val = x.val.val :=
        congr_arg (fun z : ((F ⊓ a • N).comap F.subtype) => z.val.val) hy_eq
      refine ⟨e.symm x, ?_, hy_eq⟩
      rw [h_eq]
      exact hx
  rw [h_snake, h_snake_ker, h_decomp, h_match, add_comm]

lemma length_fg_quotient_eq_bound
    (F : Submodule A M) (a : A) (ha : a ≠ 0) (r : ℕ)
    (hF : Nonempty (F ≃ₗ[A] (Fin r → A)))
    (N : Submodule A M) (hFN : F ≤ N) (hNfg : N.FG)
    (hclear : ∀ x ∈ N, ∃ c ∈ nonZeroDivisors A, c • x ∈ F) :
    Module.length A (N ⧸ (a • N).comap N.subtype)
      = r * Module.length A (A ⧸ Ideal.span {a}) := by
  have h_F_eq : Module.length A (F ⧸ (a • F).comap F.subtype) =
      Module.length A ((Fin r → A) ⧸ ((Ideal.span {a}) • (⊤ : Submodule A (Fin r → A)))) := by
    obtain ⟨e⟩ := hF
    have h_iso : Submodule.comap F.subtype (a • F) = Ideal.span {a} • ⊤ := by
      ext ⟨x, hx⟩
      simp only [Submodule.ideal_span_singleton_smul, Submodule.mem_comap,
        Submodule.mem_smul_pointwise_iff_exists, Subtype.ext_iff, Submodule.mem_top, true_and]
      exact ⟨fun ⟨y, hy, eq⟩ => ⟨⟨y, hy⟩, eq⟩, fun ⟨⟨y, hy⟩, eq⟩ => ⟨y, hy, eq⟩⟩
    have h_range : LinearMap.range (e : F →ₗ[A] (Fin r → A)) = ⊤ :=
      LinearMap.range_eq_top.mpr e.surjective
    exact LinearEquiv.length_eq (Submodule.Quotient.equiv _ _ e (by
      change Submodule.map (e : F →ₗ[A] (Fin r → A)) _ = _
      rw [h_iso, Submodule.map_smul'', Submodule.map_top, h_range]))
  rw [length_quotient_smul_eq_free A M F N a ha hFN hNfg hclear,
      h_F_eq,
      length_free_quotient_smul A a r]

/-- The length of `M ⧸ aM` is at most `r * length(A ⧸ (a))` where `r` is the rank
of `M` and `a` is non-zero. -/
theorem length_quotient_smul_le
    (a : A) (ha : a ≠ 0)
    (r : ℕ) (hrank : Module.rank A M = r) :
    Module.length A (M ⧸ a • (⊤ : Submodule A M))
      ≤ r * Module.length A (A ⧸ Ideal.span {a}) := by
  obtain ⟨F, hF_iso, hF_clear⟩ := exists_free_submodule_of_rank A M r hrank
  rw [Module.length_eq_height, Order.height_le_iff]
  intro p hp
  obtain ⟨N, hFN, hNfg, q, hqlen, hqbase⟩ := build_fg_witness A M F r hF_iso a p
  rw [← length_fg_quotient_eq_bound A M F a ha r hF_iso N hFN hNfg (fun x _ => hF_clear x),
    ← hqlen, Module.length]
  let q_Ici : LTSeries (Set.Ici ((a • N).comap N.subtype)) :=
    { length := q.length,
      toFun := fun i => ⟨q i, hqbase i⟩,
      step := fun i => q.step i }
  let e := (Submodule.comapMkQRelIso ((a • N).comap N.subtype)).symm
  exact (WithBot.le_unbot_iff _).mpr (le_iSup_of_le (LTSeries.map q_Ici ⇑e e.strictMono) le_rfl)

end Lemmata

/-! ### Krull–Akizuki -/

section KrullAkizuki

variable
  (A : Type*) [CommRing A] [IsDomain A]
  (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
  (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L]
  (B : Type*) [CommRing B] [IsDomain B]
  [Algebra A B] [Algebra B L] [Algebra A L]
  [IsScalarTower A K L] [IsScalarTower A B L]
  [NoZeroSMulDivisors B L]

open Classical in
/-- The `A`-rank of `B` is at most `[L : K]`. -/
theorem krullAkizuki_B_rank_le :
    Module.rank A B ≤ Module.finrank K L := by
  have h_indep : ∀ (s : Set B), LinearIndependent A (fun x : s => x : s → B) →
      LinearIndependent K (fun x : s => algebraMap B L x : s → L) := by
    intro s hs
    have h_AL_indep : LinearIndependent A (fun x : s => algebraMap B L x) := by
      have h_ker : LinearMap.ker (IsScalarTower.toAlgHom A B L).toLinearMap = ⊥ := by
        apply LinearMap.ker_eq_bot_of_injective
        exact FaithfulSMul.algebraMap_injective B L
      exact hs.map' (IsScalarTower.toAlgHom A B L).toLinearMap h_ker
    rw [linearIndependent_iff'] at h_AL_indep ⊢
    intro t g hg i hi
    obtain ⟨d_sub, hd⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors A) t g
    let a_fun : s → A := fun j => if hj : j ∈ t then (hd j hj).choose else 0
    have ha : ∀ j ∈ t, algebraMap A K (d_sub : A) * g j = algebraMap A K (a_fun j) := by
      intro j hj
      rw [show a_fun j = (hd j hj).choose from dif_pos hj, (hd j hj).choose_spec, Algebra.smul_def]
    have hg_d2 : ∑ i ∈ t, a_fun i • algebraMap B L i = 0 := by
      rw [← smul_zero (algebraMap A K (d_sub : A)), ← hg, Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      simp only [Algebra.smul_def, IsScalarTower.algebraMap_apply A K L, ← ha j hj,
        map_mul, mul_assoc]
    have ha_zero := h_AL_indep t a_fun hg_d2 i hi
    have h_gi : algebraMap A K (d_sub : A) * g i = 0 := by rw [ha i hi, ha_zero, map_zero]
    have hd_nz : algebraMap A K (d_sub : A) ≠ 0 := fun h =>
      mem_nonZeroDivisors_iff_ne_zero.mp d_sub.property <|
        (map_eq_zero_iff (algebraMap A K) (IsFractionRing.injective A K)).mp h
    cases mul_eq_zero.mp h_gi with
    | inl h => exact absurd h hd_nz
    | inr h => exact h
  have h_rank_le : ∀ (s : Set B), LinearIndependent A (fun x : s => x : s → B) →
      Cardinal.mk s ≤ Module.finrank K L := by
    exact fun s a => LinearIndependent.cardinalMk_le_finrank (h_indep s a)
  rw [Module.rank]
  exact ciSup_le' fun s => h_rank_le s.val s.property

include K L

/-- Every nonzero ideal of `B` contains a nonzero element of `A`. -/
theorem krullAkizuki_ideal_inter_nonzero
    (J : Ideal B) (hJ : J ≠ ⊥) :
    ∃ a : A, a ≠ 0 ∧ algebraMap A B a ∈ J := by
  obtain ⟨b, hbJ, hb⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hJ
  have hinj : Function.Injective (algebraMap B L) :=
    FaithfulSMul.algebraMap_injective B L
  haveI : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
  obtain ⟨p, hp, heval_L⟩ :=
    (IsFractionRing.isAlgebraic_iff A K L).mpr (Algebra.IsAlgebraic.isAlgebraic (algebraMap B L b))
  exact ideal_inter_of_aeval_eq_zero A B J b hb hbJ p hp <| hinj <| by
    rw [map_zero, ← Polynomial.aeval_algebraMap_apply L b p, heval_L]

variable [IsNoetherianRing A] [Ring.DimensionLEOne A]

/-- The quotient of `B` by any nonzero ideal has finite `A`-length. -/
theorem krullAkizuki_quotient_ideal_finiteLength
    (J : Ideal B) (hJ : J ≠ ⊥) :
    Module.length A (B ⧸ J) < ⊤ := by
  obtain ⟨a, ha_ne, ha_mem⟩ := krullAkizuki_ideal_inter_nonzero A K L B J hJ
  let I : Ideal B := Ideal.span {algebraMap A B a}
  have hI_le_J : I ≤ J := Ideal.span_le.mpr (Set.singleton_subset_iff.mpr ha_mem)
  let g : (B ⧸ I) →ₗ[A] (B ⧸ J) :=
    (Submodule.mapQ I J LinearMap.id ((Submodule.comap_id J).symm ▸ hI_le_J)).restrictScalars A
  haveI : NoZeroSMulDivisors A B := by
    have h_AB_inj : Function.Injective (algebraMap A B) := by
      have h_AL_inj : Function.Injective (algebraMap A L) := by
        rw [IsScalarTower.algebraMap_eq A K L]
        exact (RingHom.injective (algebraMap K L)).comp (IsFractionRing.injective A K)
      rw [IsScalarTower.algebraMap_eq A B L] at h_AL_inj
      exact Function.Injective.of_comp h_AL_inj
    haveI : Module.IsTorsionFree A B := Module.isTorsionFree_iff_algebraMap_injective.mpr h_AB_inj
    exact ⟨fun {c x} h => smul_eq_zero.mp h⟩
  have hrank := krullAkizuki_B_rank_le A K L B
  have hfin : Module.rank A B < Cardinal.aleph0 := lt_of_le_of_lt hrank Cardinal.natCast_lt_aleph0
  haveI := quotient_isArtinian_of_nonzero A a ha_ne
  haveI : IsArtinian A (A ⧸ Ideal.span {a}) := isArtinian_of_surjective_algebraMap
    (Ideal.Quotient.mk_surjective : Function.Surjective (Ideal.Quotient.mk (Ideal.span {a})))
  have h_idealSmul_eq : a • (⊤ : Submodule A B) = I.restrictScalars A := by
    apply le_antisymm
    · intro x hx
      obtain ⟨y, -, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists x a ⊤).mp hx
      exact Ideal.mem_span_singleton.mpr ⟨y, by rw [Algebra.smul_def]⟩
    · intro x hx
      obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton.mp hx
      rw [← Algebra.smul_def]
      exact Submodule.smul_mem_pointwise_smul b a ⊤ Submodule.mem_top
  have h_idealSmul : Module.length A (B ⧸ a • ⊤) < ⊤ :=
    calc
      Module.length A (B ⧸ a • ⊤)
        ≤ (Module.rank A B).toNat * Module.length A (A ⧸ Ideal.span {a}) :=
          length_quotient_smul_le A B a ha_ne _ (Cardinal.cast_toNat_of_lt_aleph0 hfin).symm
      _ ≤ (Module.finrank K L) * Module.length A (A ⧸ Ideal.span {a}) := by
          gcongr
          exact Cardinal.toNat_natCast (Module.finrank K L) ▸
            Cardinal.toNat_le_toNat hrank Cardinal.natCast_lt_aleph0
      _ < ⊤ := WithTop.mul_lt_top (ENat.coe_lt_top _) Module.length_ne_top.lt_top
  rw [h_idealSmul_eq] at h_idealSmul
  exact lt_of_le_of_lt (Module.length_le_of_surjective g <|
    fun x => (Ideal.Quotient.mk_surjective x).elim fun b hb => ⟨Ideal.Quotient.mk I b, hb⟩)
    h_idealSmul

include A

/-- **Krull–Akizuki theorem** (Noetherian part): `B` is a Noetherian ring. -/
theorem krullAkizuki_isNoetherianRing :
    IsNoetherianRing B := by
  rw [isNoetherianRing_iff_ideal_fg]; intro J
  obtain rfl | hJ := eq_or_ne J ⊥
  · exact Submodule.fg_bot
  obtain ⟨b, hbJ, hb_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hJ
  let I : Ideal B := Ideal.span {b}
  haveI : IsNoetherian B (B ⧸ I) := isNoetherian_of_tower A
    (isFiniteLength_iff_isNoetherian_isArtinian.mp <| Module.length_ne_top_iff.mp <|
      ne_of_lt (krullAkizuki_quotient_ideal_finiteLength A K L B I
        (mt Ideal.span_singleton_eq_bot.mp hb_ne))).1
  exact Submodule.fg_of_fg_map_of_fg_inf_ker I.mkQ (IsNoetherian.noetherian _)
    ⟨{b}, by rw [Finset.coe_singleton, Submodule.ker_mkQ,
      inf_of_le_right (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hbJ))]⟩

/-- **Krull–Akizuki theorem** (dimension part): `B` has Krull dimension at most one. -/
theorem krullAkizuki_dimensionLEOne :
    Ring.DimensionLEOne B :=
  ⟨fun {p} hp_ne hp_prime => by
    letI : IsDomain (B ⧸ p) := Ideal.Quotient.isDomain p
    haveI : IsArtinianRing (B ⧸ p) := isArtinian_of_tower B (isArtinian_of_tower A
      (isFiniteLength_iff_isNoetherian_isArtinian.mp <| Module.length_ne_top_iff.mp <|
        ne_of_lt (krullAkizuki_quotient_ideal_finiteLength A K L B p hp_ne)).2)
    exact Ideal.Quotient.maximal_of_isField p (IsArtinianRing.isField_of_isDomain (B ⧸ p))⟩

/-- **Krull–Akizuki theorem**: `B` is Noetherian, has Krull dimension at most one, and
every nonzero ideal quotient has finite `A`-length. -/
theorem krull_akizuki :
    IsNoetherianRing B ∧
    Ring.DimensionLEOne B ∧
    ∀ J : Ideal B, J ≠ ⊥ → Module.length A (B ⧸ J) < ⊤ :=
  ⟨krullAkizuki_isNoetherianRing A K L B, krullAkizuki_dimensionLEOne A K L B,
    krullAkizuki_quotient_ideal_finiteLength A K L B⟩

end KrullAkizuki
