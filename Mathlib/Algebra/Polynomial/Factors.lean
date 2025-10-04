/-
Copyright (c) 2025 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas
-/
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.Lifts
import Mathlib.Data.List.Prime
import Mathlib.RingTheory.Polynomial.Tower

/-!
# Split polynomials

A polynomial `f : R[X]` factors if it is a product of polynomials of degree ≤ 1.

## Main definitions

* `Polynomial.Factors f`: A predicate on a polynomial `f` saying that `f` is a product of
  of polynoimals of degree ≤ 1.

-/

variable {R : Type*}

namespace Polynomial

section Semiring

variable [Semiring R]

def Factors (f : R[X]) : Prop := f ∈ Submonoid.closure ({C a | a : R} ∪ {X + C a | a : R})

theorem factors_C (a : R) : Factors (C a) :=
  Submonoid.mem_closure_of_mem (Set.mem_union_left _ ⟨a, rfl⟩)

theorem factors_zero : Factors (0 : R[X]) := by
  simpa using factors_C (0 : R)

theorem factors_one : Factors (1 : R[X]) := by
  simpa using factors_C (1 : R)

theorem factors_X_add_C (a : R) : Factors (X + C a) :=
  Submonoid.mem_closure_of_mem (Set.mem_union_right _ ⟨a, rfl⟩)

theorem factors_X : Factors (X : R[X]) := by
  simpa using factors_X_add_C (0 : R)

theorem Factors.mul {f g : R[X]} (hf : Factors f) (hg : Factors g) :
    Factors (f * g) :=
  mul_mem hf hg

theorem Factors.list_prod {l : List R[X]} (h : ∀ f ∈ l, Factors f) : Factors l.prod := by
  induction l with
  | nil => exact factors_one
  | cons f l ih =>
    exact (h f List.mem_cons_self).mul (ih (h · ∘ List.mem_cons_of_mem f))

theorem Factors.pow {f : R[X]} (hf : Factors f) (n : ℕ) : Factors (f ^ n) := by
  rw [← List.prod_replicate]
  exact Factors.list_prod (by simp [hf])

theorem factors_X_pow (n : ℕ) : Factors (X ^ n : R[X]) :=
  factors_X.pow n

theorem Factors.map {f : R[X]} (hf : Factors f) {S : Type*} [Semiring S] (i : R →+* S) :
    Factors (map i f) := by
  have h := Submonoid.mem_map_of_mem (mapRingHom i) hf
  rw [MonoidHom.map_mclosure, Set.image_union] at h
  refine Submonoid.closure_mono (Set.union_subset_union ?_ ?_) h <;>
    rintro - ⟨-, ⟨a, rfl⟩, rfl⟩ <;> exact ⟨i a, by simp⟩

theorem factors_of_isUnit [NoZeroDivisors R] {f : R[X]} (hf : IsUnit f) : Factors f :=
  (isUnit_iff.mp hf).choose_spec.2 ▸ factors_C _

end Semiring

section CommSemiring

variable [CommSemiring R]

theorem Factors.multiset_prod {m : Multiset R[X]} (hm : ∀ f ∈ m, Factors f) : Factors m.prod := by
  rw [← Multiset.prod_toList]
  exact Factors.list_prod (by simpa)

theorem Factors.prod {ι : Type*} {f : ι → R[X]} {s : Finset ι}
    (h : ∀ i ∈ s, Factors (f i)) : Factors (∏ i ∈ s, f i) := by
  rw [Finset.prod_eq_multiset_prod]
  exact Factors.multiset_prod (by simpa)

theorem factors_iff_exists_multiset_add {f : R[X]} :
    Factors f ↔ ∃ s : Multiset R, f = C f.leadingCoeff * (s.map (X + C ·)).prod := by
  refine ⟨fun hf ↦ ?_, ?_⟩
  · rw [Factors, Submonoid.closure_union, Submonoid.mem_sup] at hf
    obtain ⟨f, hf, g, hg, rfl⟩ := hf
    obtain ⟨mf, hmf, rfl⟩ := Submonoid.exists_multiset_of_mem_closure hf
    obtain ⟨mg, hmg, rfl⟩ := Submonoid.exists_multiset_of_mem_closure hg
    clear hf hg
    choose! i hi using hmf
    choose! j hj using hmg
    have hmf : mf = (mf.map i).map C := by simp [Multiset.map_congr rfl hi]
    have hmg : mg = (mg.map j).map (X + C ·) := by simp [Multiset.map_congr rfl hj]
    use mg.map j
    rw [← hmg, leadingCoeff_mul_monic]
    · have key := MonoidHom.map_multiset_prod C.toMonoidHom (mf.map i)
      rw [RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe] at key
      rw [hmf, ← key, leadingCoeff_C]
    · rw [hmg]
      apply monic_multiset_prod_of_monic
      simp [monic_X_add_C]
  · rintro ⟨s, hs⟩
    exact hs ▸ (factors_C _).mul (Factors.multiset_prod (by simp [factors_X_add_C]))

end CommSemiring

section Ring

variable [Ring R]

theorem factors_X_sub_C (a : R) : Factors (X - C a) := by
  simpa using factors_X_add_C (-a)

end Ring

section CommRing

variable [CommRing R]

theorem factors_iff_exists_multiset {f : R[X]} :
    Factors f ↔ ∃ s : Multiset R, f = C f.leadingCoeff * (s.map (X - C ·)).prod := by
  refine factors_iff_exists_multiset_add.trans ⟨?_, ?_⟩ <;>
    rintro ⟨s, hs⟩ <;> exact ⟨s.map (- ·), by simpa⟩

end CommRing

section Field

variable [Field R]

theorem factors_of_natDegree_le_one {f : R[X]} (hf : natDegree f ≤ 1) : Factors f := by
  obtain ⟨a, b, rfl⟩ := exists_eq_X_add_C_of_natDegree_le_one hf
  by_cases ha : a = 0
  · simp [ha, factors_C]
  · rw [← mul_div_cancel₀ b ha, C_mul, ← mul_add]
    exact (factors_C a).mul (factors_X_add_C (b / a))

theorem factors_of_natDegree_eq_one {f : R[X]} (hf : natDegree f = 1) : Factors f :=
  factors_of_natDegree_le_one hf.le

theorem factors_of_degree_le_one {f : R[X]} (hf : degree f ≤ 1) : Factors f :=
  factors_of_natDegree_le_one (natDegree_le_of_degree_le hf)

theorem factors_of_degree_eq_one {f : R[X]} (hf : degree f = 1) : Factors f :=
  factors_of_degree_le_one hf.le

end Field

end Polynomial

-- TODO: Characterization in terms of irreducible factors
-- `splits_of_splits_mul`
-- `splits_of_splits_of_dvd`
-- `splits_mul_iff`
-- `splits_prod_iff`

noncomputable section

open Polynomial

universe u v w

variable {R : Type*} {F : Type u} {K : Type v} {L : Type w}

namespace Polynomial

section Splits

section CommRing

variable [CommRing K] [Field L] [Field F]
variable (i : K →+* L)

/-- A polynomial `Splits` iff it is zero or all of its irreducible factors have `degree` 1. -/
def Splits (f : K[X]) : Prop :=
  f.map i = 0 ∨ ∀ {g : L[X]}, Irreducible g → g ∣ f.map i → degree g = 1

theorem splits_of_splits_mul' {f g : K[X]} (hfg : (f * g).map i ≠ 0) (h : Splits i (f * g)) :
    Splits i f ∧ Splits i g :=
  ⟨Or.inr @fun g hgi hg =>
      Or.resolve_left h hfg hgi (by rw [Polynomial.map_mul]; exact hg.trans (dvd_mul_right _ _)),
    Or.inr @fun g hgi hg =>
      Or.resolve_left h hfg hgi (by rw [Polynomial.map_mul]; exact hg.trans (dvd_mul_left _ _))⟩

variable {i}

/--
This is a weaker variant of `Splits.comp_of_map_degree_le_one`,
but its conditions are easier to check.
-/
theorem Splits.comp_of_degree_le_one {f : K[X]} {p : K[X]} (hd : p.degree ≤ 1)
    (h : f.Splits i) : (f.comp p).Splits i :=
  Splits.comp_of_map_degree_le_one (degree_map_le.trans hd) h

theorem Splits.comp_X_sub_C (a : K) {f : K[X]}
    (h : f.Splits i) : (f.comp (X - C a)).Splits i :=
  Splits.comp_of_degree_le_one (degree_X_sub_C_le _) h

theorem Splits.comp_X_add_C (a : K) {f : K[X]}
    (h : f.Splits i) : (f.comp (X + C a)).Splits i :=
  Splits.comp_of_degree_le_one (by simpa using degree_X_sub_C_le (-a)) h

theorem Splits.comp_neg_X {f : K[X]} (h : f.Splits i) : (f.comp (-X)).Splits i :=
  Splits.comp_of_degree_le_one (by simpa using degree_X_sub_C_le (0 : K)) h

variable (i)

theorem exists_root_of_splits' {f : K[X]} (hs : Splits i f) (hf0 : degree (f.map i) ≠ 0) :
    ∃ x, eval₂ i x f = 0 :=
  letI := Classical.decEq L
  if hf0' : f.map i = 0 then by simp [eval₂_eq_eval_map, hf0']
  else
    let ⟨g, hg⟩ :=
      WfDvdMonoid.exists_irreducible_factor
        (show ¬IsUnit (f.map i) from mt isUnit_iff_degree_eq_zero.1 hf0) hf0'
    let ⟨x, hx⟩ := exists_root_of_degree_eq_one (hs.resolve_left hf0' hg.1 hg.2)
    let ⟨i, hi⟩ := hg.2
    ⟨x, by rw [← eval_map, hi, eval_mul, show _ = _ from hx, zero_mul]⟩

theorem roots_ne_zero_of_splits' {f : K[X]} (hs : Splits i f) (hf0 : natDegree (f.map i) ≠ 0) :
    (f.map i).roots ≠ 0 :=
  let ⟨x, hx⟩ := exists_root_of_splits' i hs fun h => hf0 <| natDegree_eq_of_degree_eq_some h
  fun h => by
  rw [← eval_map] at hx
  have : f.map i ≠ 0 := by intro; simp_all
  cases h.subst ((mem_roots this).2 hx)

/-- Pick a root of a polynomial that splits. See `rootOfSplits` for polynomials over a field
which has simpler assumptions. -/
def rootOfSplits' {f : K[X]} (hf : f.Splits i) (hfd : (f.map i).degree ≠ 0) : L :=
  Classical.choose <| exists_root_of_splits' i hf hfd

theorem map_rootOfSplits' {f : K[X]} (hf : f.Splits i) (hfd) :
    f.eval₂ i (rootOfSplits' i hf hfd) = 0 :=
  Classical.choose_spec <| exists_root_of_splits' i hf hfd

theorem natDegree_eq_card_roots' {p : K[X]} {i : K →+* L} (hsplit : Splits i p) :
    (p.map i).natDegree = Multiset.card (p.map i).roots := by
  by_cases hp : p.map i = 0
  · rw [hp, natDegree_zero, roots_zero, Multiset.card_zero]
  obtain ⟨q, he, hd, hr⟩ := exists_prod_multiset_X_sub_C_mul (p.map i)
  rw [← splits_id_iff_splits, ← he] at hsplit
  rw [← he] at hp
  have hq : q ≠ 0 := fun h => hp (by rw [h, mul_zero])
  rw [← hd, add_eq_left]
  by_contra h
  have h' : (map (RingHom.id L) q).natDegree ≠ 0 := by simp [h]
  have := roots_ne_zero_of_splits' (RingHom.id L) (splits_of_splits_mul' _ ?_ hsplit).2 h'
  · rw [map_id] at this
    exact this hr
  · rw [map_id]
    exact mul_ne_zero (monic_multisetProd_X_sub_C _).ne_zero hq

theorem degree_eq_card_roots' {p : K[X]} {i : K →+* L} (p_ne_zero : p.map i ≠ 0)
    (hsplit : Splits i p) : (p.map i).degree = Multiset.card (p.map i).roots := by
  simp [degree_eq_natDegree p_ne_zero, natDegree_eq_card_roots' hsplit]

end CommRing

theorem aeval_root_of_mapAlg_eq_multiset_prod_X_sub_C [CommSemiring R] [CommRing L] [Algebra R L]
    (s : Multiset L) {x : L} (hx : x ∈ s) {p : R[X]}
    (hp : mapAlg R L p = (Multiset.map (fun a : L ↦ X - C a) s).prod) : aeval x p = 0 := by
  rw [← aeval_map_algebraMap L, ← mapAlg_eq_map, hp, map_multiset_prod, Multiset.prod_eq_zero]
  rw [Multiset.map_map, Multiset.mem_map]
  exact ⟨x, hx, by simp⟩

variable [CommRing R] [Field K] [Field L] [Field F]
variable (i : K →+* L)

/-- This lemma is for polynomials over a field. -/
theorem splits_iff (f : K[X]) :
    Splits i f ↔ f = 0 ∨ ∀ {g : L[X]}, Irreducible g → g ∣ f.map i → degree g = 1 := by
  rw [Splits, Polynomial.map_eq_zero]

/-- This lemma is for polynomials over a field. -/
theorem Splits.def {i : K →+* L} {f : K[X]} (h : Splits i f) :
    f = 0 ∨ ∀ {g : L[X]}, Irreducible g → g ∣ f.map i → degree g = 1 :=
  (splits_iff i f).mp h

theorem splits_of_splits_mul {f g : K[X]} (hfg : f * g ≠ 0) (h : Splits i (f * g)) :
    Splits i f ∧ Splits i g :=
  splits_of_splits_mul' i (map_ne_zero hfg) h

theorem splits_of_splits_of_dvd {f g : K[X]} (hf0 : f ≠ 0) (hf : Splits i f) (hgf : g ∣ f) :
    Splits i g := by
  obtain ⟨f, rfl⟩ := hgf
  exact (splits_of_splits_mul i hf0 hf).1

theorem splits_of_splits_gcd_left [DecidableEq K] {f g : K[X]} (hf0 : f ≠ 0) (hf : Splits i f) :
    Splits i (EuclideanDomain.gcd f g) :=
  Polynomial.splits_of_splits_of_dvd i hf0 hf (EuclideanDomain.gcd_dvd_left f g)

theorem splits_of_splits_gcd_right [DecidableEq K] {f g : K[X]} (hg0 : g ≠ 0) (hg : Splits i g) :
    Splits i (EuclideanDomain.gcd f g) :=
  Polynomial.splits_of_splits_of_dvd i hg0 hg (EuclideanDomain.gcd_dvd_right f g)

theorem splits_mul_iff {f g : K[X]} (hf : f ≠ 0) (hg : g ≠ 0) :
    (f * g).Splits i ↔ f.Splits i ∧ g.Splits i :=
  ⟨splits_of_splits_mul i (mul_ne_zero hf hg), fun ⟨hfs, hgs⟩ => splits_mul i hfs hgs⟩

theorem splits_prod_iff {ι : Type u} {s : ι → K[X]} {t : Finset ι} :
    (∀ j ∈ t, s j ≠ 0) → ((∏ x ∈ t, s x).Splits i ↔ ∀ j ∈ t, (s j).Splits i) := by
  classical
  refine
    Finset.induction_on t (fun _ =>
        ⟨fun _ _ h => by simp only [Finset.notMem_empty] at h, fun _ => splits_one i⟩)
      fun a t hat ih ht => ?_
  rw [Finset.forall_mem_insert] at ht ⊢
  rw [Finset.prod_insert hat, splits_mul_iff i ht.1 (Finset.prod_ne_zero_iff.2 ht.2), ih ht.2]

theorem degree_eq_one_of_irreducible_of_splits {p : K[X]} (hp : Irreducible p)
    (hp_splits : Splits (RingHom.id K) p) : p.degree = 1 := by
  rcases hp_splits with ⟨⟩ | hp_splits
  · exfalso
    simp_all
  · apply hp_splits hp
    simp

theorem exists_root_of_splits {f : K[X]} (hs : Splits i f) (hf0 : degree f ≠ 0) :
    ∃ x, eval₂ i x f = 0 :=
  exists_root_of_splits' i hs ((f.degree_map i).symm ▸ hf0)

theorem roots_ne_zero_of_splits {f : K[X]} (hs : Splits i f) (hf0 : natDegree f ≠ 0) :
    (f.map i).roots ≠ 0 :=
  roots_ne_zero_of_splits' i hs (ne_of_eq_of_ne (natDegree_map i) hf0)

/-- Pick a root of a polynomial that splits. This version is for polynomials over a field and has
simpler assumptions. -/
def rootOfSplits {f : K[X]} (hf : f.Splits i) (hfd : f.degree ≠ 0) : L :=
  rootOfSplits' i hf ((f.degree_map i).symm ▸ hfd)

/-- `rootOfSplits'` is definitionally equal to `rootOfSplits`. -/
theorem rootOfSplits'_eq_rootOfSplits {f : K[X]} (hf : f.Splits i) (hfd) :
    rootOfSplits' i hf hfd = rootOfSplits i hf (f.degree_map i ▸ hfd) :=
  rfl

theorem map_rootOfSplits {f : K[X]} (hf : f.Splits i) (hfd) :
    f.eval₂ i (rootOfSplits i hf hfd) = 0 :=
  map_rootOfSplits' i hf (ne_of_eq_of_ne (degree_map f i) hfd)

theorem natDegree_eq_card_roots {p : K[X]} {i : K →+* L} (hsplit : Splits i p) :
    p.natDegree = Multiset.card (p.map i).roots :=
  (natDegree_map i).symm.trans <| natDegree_eq_card_roots' hsplit

theorem degree_eq_card_roots {p : K[X]} {i : K →+* L} (p_ne_zero : p ≠ 0) (hsplit : Splits i p) :
    p.degree = Multiset.card (p.map i).roots := by
  rw [degree_eq_natDegree p_ne_zero, natDegree_eq_card_roots hsplit]

theorem roots_map {f : K[X]} (hf : f.Splits <| RingHom.id K) : (f.map i).roots = f.roots.map i :=
  (roots_map_of_injective_of_card_eq_natDegree i.injective <| by
      convert (natDegree_eq_card_roots hf).symm
      rw [map_id]).symm

theorem Splits.mem_subfield_of_isRoot (F : Subfield K) {f : F[X]} (hnz : f ≠ 0)
    (hf : Splits (RingHom.id F) f) {x : K} (hx : (f.map F.subtype).IsRoot x) :
    x ∈ F := by
  obtain ⟨x, _, rfl⟩ := Multiset.mem_map.mp
    (roots_map F.subtype hf ▸ mem_roots'.mpr ⟨Polynomial.map_ne_zero hnz, hx⟩)
  exact x.2

theorem image_rootSet [Algebra R K] [Algebra R L] {p : R[X]} (h : p.Splits (algebraMap R K))
    (f : K →ₐ[R] L) : f '' p.rootSet K = p.rootSet L := by
  classical
    rw [rootSet, ← Finset.coe_image, ← Multiset.toFinset_map, ← f.coe_toRingHom,
      ← roots_map _ ((splits_id_iff_splits (algebraMap R K)).mpr h), map_map, f.comp_algebraMap,
      ← rootSet]

theorem adjoin_rootSet_eq_range [Algebra R K] [Algebra R L] {p : R[X]}
    (h : p.Splits (algebraMap R K)) (f : K →ₐ[R] L) :
    Algebra.adjoin R (p.rootSet L) = f.range ↔ Algebra.adjoin R (p.rootSet K) = ⊤ := by
  rw [← image_rootSet h f, Algebra.adjoin_image, ← Algebra.map_top]
  exact (Subalgebra.map_injective f.toRingHom.injective).eq_iff

theorem eq_prod_roots_of_splits {p : K[X]} {i : K →+* L} (hsplit : Splits i p) :
    p.map i = C (i p.leadingCoeff) * ((p.map i).roots.map fun a => X - C a).prod := by
  rw [← leadingCoeff_map]; symm
  apply C_leadingCoeff_mul_prod_multiset_X_sub_C
  rw [natDegree_map]; exact (natDegree_eq_card_roots hsplit).symm

theorem eq_prod_roots_of_splits_id {p : K[X]} (hsplit : Splits (RingHom.id K) p) :
    p = C p.leadingCoeff * (p.roots.map fun a => X - C a).prod := by
  simpa using eq_prod_roots_of_splits hsplit

theorem Splits.dvd_of_roots_le_roots {p q : K[X]} (hp : p.Splits (RingHom.id _)) (hp0 : p ≠ 0)
    (hq : p.roots ≤ q.roots) : p ∣ q := by
  rw [eq_prod_roots_of_splits_id hp, C_mul_dvd (leadingCoeff_ne_zero.2 hp0)]
  exact dvd_trans
    (Multiset.prod_dvd_prod_of_le (Multiset.map_le_map hq))
    (prod_multiset_X_sub_C_dvd _)

theorem Splits.dvd_iff_roots_le_roots {p q : K[X]}
    (hp : p.Splits (RingHom.id _)) (hp0 : p ≠ 0) (hq0 : q ≠ 0) :
    p ∣ q ↔ p.roots ≤ q.roots :=
  ⟨Polynomial.roots.le_of_dvd hq0, hp.dvd_of_roots_le_roots hp0⟩

theorem aeval_eq_prod_aroots_sub_of_splits [Algebra K L] {p : K[X]}
    (hsplit : Splits (algebraMap K L) p) (v : L) :
    aeval v p = algebraMap K L p.leadingCoeff * ((p.aroots L).map fun a ↦ v - a).prod := by
  rw [← eval_map_algebraMap, eq_prod_roots_of_splits hsplit]
  simp [eval_multiset_prod]

theorem eval_eq_prod_roots_sub_of_splits_id {p : K[X]}
    (hsplit : Splits (RingHom.id K) p) (v : K) :
    eval v p = p.leadingCoeff * (p.roots.map fun a ↦ v - a).prod := by
  convert aeval_eq_prod_aroots_sub_of_splits hsplit v
  rw [Algebra.algebraMap_self, map_id]

theorem eq_prod_roots_of_monic_of_splits_id {p : K[X]} (m : Monic p)
    (hsplit : Splits (RingHom.id K) p) : p = (p.roots.map fun a => X - C a).prod := by
  convert eq_prod_roots_of_splits_id hsplit
  simp [m]

theorem aeval_eq_prod_aroots_sub_of_monic_of_splits [Algebra K L] {p : K[X]} (m : Monic p)
    (hsplit : Splits (algebraMap K L) p) (v : L) :
    aeval v p = ((p.aroots L).map fun a ↦ v - a).prod := by
  simp [aeval_eq_prod_aroots_sub_of_splits hsplit, m]

theorem eval_eq_prod_roots_sub_of_monic_of_splits_id {p : K[X]} (m : Monic p)
    (hsplit : Splits (RingHom.id K) p) (v : K) :
    eval v p = (p.roots.map fun a ↦ v - a).prod := by
  simp [eval_eq_prod_roots_sub_of_splits_id hsplit, m]

theorem eq_X_sub_C_of_splits_of_single_root {x : K} {h : K[X]} (h_splits : Splits i h)
    (h_roots : (h.map i).roots = {i x}) : h = C h.leadingCoeff * (X - C x) := by
  apply Polynomial.map_injective _ i.injective
  rw [eq_prod_roots_of_splits h_splits, h_roots]
  simp

variable (R) in
theorem mem_lift_of_splits_of_roots_mem_range [Algebra R K] {f : K[X]}
    (hs : f.Splits (RingHom.id K)) (hm : f.Monic) (hr : ∀ a ∈ f.roots, a ∈ (algebraMap R K).range) :
    f ∈ Polynomial.lifts (algebraMap R K) := by
  rw [eq_prod_roots_of_monic_of_splits_id hm hs, lifts_iff_liftsRing]
  refine Subring.multiset_prod_mem _ _ fun P hP => ?_
  obtain ⟨b, hb, rfl⟩ := Multiset.mem_map.1 hP
  exact Subring.sub_mem _ (X_mem_lifts _) (C'_mem_lifts (hr _ hb))

/--
A polynomial of degree `2` with a root splits.
-/
theorem splits_of_natDegree_eq_two {f : Polynomial K} {x : L} (h₁ : f.natDegree = 2)
    (h₂ : eval₂ i x f = 0) : Splits i f := by
  have hf₀ : f ≠ 0 := ne_zero_of_natDegree_gt (h₁ ▸ zero_lt_two)
  have h : (map i f /ₘ (X - C x)).natDegree = 1 := by
    rw [natDegree_divByMonic _ (monic_X_sub_C x), natDegree_map, h₁, natDegree_X_sub_C]
  replace h₂ := (mem_roots'.mp <| (mem_roots_map_of_injective i.injective hf₀).mpr h₂).2
  rw [← splits_id_iff_splits, ← mul_divByMonic_eq_iff_isRoot.mpr h₂]
  exact (splits_mul_iff _ (X_sub_C_ne_zero x) (by simp [ne_zero_of_natDegree_gt, h])).mpr
    ⟨splits_X_sub_C  _, splits_of_natDegree_le_one (RingHom.id L) (by rw [h])⟩

theorem splits_of_degree_eq_two {f : Polynomial K} {x : L} (h₁ : f.degree = 2)
    (h₂ : eval₂ i x f = 0) : Splits i f :=
  splits_of_natDegree_eq_two i (natDegree_eq_of_degree_eq_some h₁) h₂

theorem splits_of_comp (j : L →+* F) {f : K[X]} (h : Splits (j.comp i) f)
    (roots_mem_range : ∀ a ∈ (f.map (j.comp i)).roots, a ∈ j.range) : Splits i f := by
  choose lift lift_eq using roots_mem_range
  rw [splits_iff_exists_multiset]
  refine ⟨(f.map (j.comp i)).roots.pmap lift fun _ ↦ id, map_injective _ j.injective ?_⟩
  conv_lhs => rw [Polynomial.map_map, eq_prod_roots_of_splits h]
  simp_rw [Polynomial.map_mul, Polynomial.map_multiset_prod, Multiset.map_pmap, Polynomial.map_sub,
    map_C, map_X, lift_eq, Multiset.pmap_eq_map]
  rfl

theorem splits_id_of_splits {f : K[X]} (h : Splits i f)
    (roots_mem_range : ∀ a ∈ (f.map i).roots, a ∈ i.range) : Splits (RingHom.id K) f :=
  splits_of_comp (RingHom.id K) i h roots_mem_range

theorem splits_comp_of_splits (i : R →+* K) (j : K →+* L) {f : R[X]} (h : Splits i f) :
    Splits (j.comp i) f :=
  (splits_map_iff i j).mp (splits_of_splits_id _ <| (splits_map_iff i <| .id K).mpr h)

variable [Algebra R K] [Algebra R L]

theorem splits_of_algHom {f : R[X]} (h : Splits (algebraMap R K) f) (e : K →ₐ[R] L) :
    Splits (algebraMap R L) f := by
  rw [← e.comp_algebraMap_of_tower R]; exact splits_comp_of_splits _ _ h

variable (L) in
theorem splits_of_isScalarTower {f : R[X]} [Algebra K L] [IsScalarTower R K L]
    (h : Splits (algebraMap R K) f) : Splits (algebraMap R L) f :=
  splits_of_algHom h (IsScalarTower.toAlgHom R K L)

/-- A polynomial splits if and only if it has as many roots as its degree. -/
theorem splits_iff_card_roots {p : K[X]} :
    Splits (RingHom.id K) p ↔ Multiset.card p.roots = p.natDegree := by
  constructor
  · intro H
    rw [natDegree_eq_card_roots H, map_id]
  · intro hroots
    rw [splits_iff_exists_multiset (RingHom.id K)]
    use p.roots
    simp only [RingHom.id_apply, map_id]
    exact (C_leadingCoeff_mul_prod_multiset_X_sub_C hroots).symm

theorem eval₂_derivative_of_splits [DecidableEq L] {P : K[X]} {f : K →+* L} (hP : P.Splits f)
    (x : L) :
    eval₂ f x P.derivative = f (P.leadingCoeff) *
      ((P.map f).roots.map fun a ↦ (((P.map f).roots.erase a).map (x - ·)).prod).sum := by
  conv_lhs => rw [← eval_map, ← derivative_map, eq_prod_roots_of_splits hP]
  classical
  simp [derivative_prod, eval_multisetSum, eval_multiset_prod]

theorem aeval_derivative_of_splits [Algebra K L] [DecidableEq L] {P : K[X]}
    (hP : P.Splits (algebraMap K L)) (r : L) :
    aeval r P.derivative = algebraMap K L P.leadingCoeff *
      ((P.aroots L).map fun a ↦ (((P.aroots L).erase a).map (r - ·)).prod).sum :=
  eval₂_derivative_of_splits hP r

theorem eval_derivative_of_splits [DecidableEq K] {P : K[X]} (hP : P.Splits (.id K)) (r : K) :
    eval r P.derivative = P.leadingCoeff *
      (P.roots.map fun a ↦ ((P.roots.erase a).map (r - ·)).prod).sum := by
  simpa using eval₂_derivative_of_splits hP r

/-- Let `P` be a monic polynomial over `K` that splits over `L`. Let `r : L` be a root of `P`.
Then $P'(r) = \prod_{a}(r-a)$, where the product in the RHS is taken over all roots of `P` in `L`,
with the multiplicity of `r` reduced by one. -/
theorem aeval_root_derivative_of_splits [Algebra K L] [DecidableEq L] {P : K[X]} (hmo : P.Monic)
    (hP : P.Splits (algebraMap K L)) {r : L} (hr : r ∈ P.aroots L) :
    aeval r (Polynomial.derivative P) = (((P.aroots L).erase r).map fun a => r - a).prod := by
  replace hmo := hmo.map (algebraMap K L)
  replace hP := (splits_id_iff_splits (algebraMap K L)).2 hP
  rw [aeval_def, ← eval_map, ← derivative_map]
  nth_rw 1 [eq_prod_roots_of_monic_of_splits_id hmo hP]
  rw [eval_multiset_prod_X_sub_C_derivative hr]

theorem eval_derivative_eq_eval_mul_sum_of_splits {p : K[X]} {x : K}
    (h : p.Splits (.id K)) (hx : p.eval x ≠ 0) :
    p.derivative.eval x = p.eval x * (p.roots.map fun z ↦ 1 / (x - z)).sum := by
  classical
  suffices p.roots.map (fun z ↦ p.leadingCoeff * ((p.roots.erase z).map (fun w ↦ x - w) ).prod) =
      p.roots.map fun i ↦ p.leadingCoeff * ((x - i)⁻¹ * (p.roots.map (fun z ↦ x - z)).prod) by
    nth_rw 2 [p.eq_prod_roots_of_splits_id h]
    simp [eval_derivative_of_splits h, ← Multiset.sum_map_mul_left, this, eval_multiset_prod,
      mul_comm, mul_left_comm]
  refine Multiset.map_congr rfl fun z hz ↦ ?_
  rw [← Multiset.prod_map_erase hz, inv_mul_cancel_left₀]
  aesop (add simp sub_eq_zero)

theorem eval_derivative_div_eval_of_ne_zero_of_splits {p : K[X]} {x : K}
    (h : p.Splits (.id K)) (hx : p.eval x ≠ 0) :
    p.derivative.eval x / p.eval x = (p.roots.map fun z ↦ 1 / (x - z)).sum := by
  rw [eval_derivative_eq_eval_mul_sum_of_splits h hx]
  exact mul_div_cancel_left₀ _ hx

/-- If `P` is a monic polynomial that splits, then `coeff P 0` equals the product of the roots. -/
theorem prod_roots_eq_coeff_zero_of_monic_of_splits {P : K[X]} (hmo : P.Monic)
    (hP : P.Splits (RingHom.id K)) : coeff P 0 = (-1) ^ P.natDegree * P.roots.prod := by
  nth_rw 1 [eq_prod_roots_of_monic_of_splits_id hmo hP]
  rw [coeff_zero_eq_eval_zero, eval_multiset_prod, Multiset.map_map]
  simp_rw [Function.comp_apply, eval_sub, eval_X, zero_sub, eval_C]
  simp only [splits_iff_card_roots.1 hP, Multiset.prod_map_neg]

/-- If `P` is a monic polynomial that splits, then `P.nextCoeff` equals the sum of the roots. -/
theorem sum_roots_eq_nextCoeff_of_monic_of_split {P : K[X]} (hmo : P.Monic)
    (hP : P.Splits (RingHom.id K)) : P.nextCoeff = -P.roots.sum := by
  nth_rw 1 [eq_prod_roots_of_monic_of_splits_id hmo hP]
  rw [Monic.nextCoeff_multiset_prod _ _ fun a ha => _]
  · simp_rw [nextCoeff_X_sub_C, Multiset.sum_map_neg']
  · simp only [monic_X_sub_C, implies_true]

end Splits

end Polynomial
