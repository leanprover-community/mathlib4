/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
module

public import Mathlib.Algebra.Polynomial.Factors
public import Mathlib.Algebra.Polynomial.Lifts
public import Mathlib.RingTheory.Polynomial.Tower

/-!
# Split polynomials

A polynomial `f : K[X]` splits over a field extension `L` of `K` if it is zero or all of its
irreducible factors over `L` have degree `1`.

## Main definitions

* `Polynomial.Splits i f`: A predicate on a homomorphism `i : K →+* L` from a commutative ring to a
  field and a polynomial `f` saying that `f.map i` factors in `L`.

-/

@[expose] public section

noncomputable section

open Polynomial

universe u v w

variable {R : Type*} {F : Type u} {K : Type v} {L : Type w}

namespace Polynomial

section Splits

section CommRing

variable [CommRing K] [Field L] [Field F]
variable (i : K →+* L)

@[deprecated (since := "2025-11-24")]
alias splits_zero := Splits.zero

@[deprecated "Use `Splits.C` instead." (since := "2025-11-24")]
theorem splits_of_map_eq_C {f : K[X]} {a : L} (h : f.map i = C a) : Splits (f.map i) :=
  h ▸ Splits.C a

@[deprecated (since := "2025-11-24")]
alias splits_C := Splits.C

@[deprecated (since := "2025-11-24")]
alias splits_of_map_degree_eq_one := Splits.of_degree_eq_one

@[deprecated (since := "2025-11-24")]
alias splits_of_degree_le_one := Splits.of_degree_le_one

@[deprecated (since := "2025-11-24")]
alias splits_of_degree_eq_one := Splits.of_degree_eq_one

@[deprecated (since := "2025-11-24")]
alias splits_of_natDegree_le_one := Splits.of_natDegree_le_one

@[deprecated (since := "2025-11-24")]
alias splits_of_natDegree_eq_one := Splits.of_natDegree_eq_one

@[deprecated (since := "2025-11-25")]
alias splits_mul := Splits.mul

@[deprecated (since := "2025-11-25")]
alias splits_of_splits_mul' := splits_mul_iff

@[deprecated "Use `Polynomial.map_map` instead." (since := "2025-11-24")]
theorem splits_map_iff {L : Type*} [CommRing L] (i : K →+* L) (j : L →+* F) {f : K[X]} :
    Splits ((f.map i).map j) ↔ Splits (f.map (j.comp i)) := by
  rw [Polynomial.map_map]

@[deprecated (since := "2025-11-24")]
alias splits_one := Splits.one

@[deprecated (since := "2025-11-24")]
alias splits_X_sub_C := Splits.X_sub_C

@[deprecated (since := "2025-11-24")]
alias splits_X := Splits.X

@[deprecated (since := "2025-11-24")]
alias splits_prod := Splits.prod

@[deprecated (since := "2025-11-24")]
alias splits_pow := Splits.pow

@[deprecated (since := "2025-11-24")]
alias splits_X_pow := Splits.X_pow

@[deprecated "Use `Polynomial.map_id` instead." (since := "2025-11-24")]
theorem splits_id_iff_splits {f : K[X]} :
    ((f.map i).map (RingHom.id L)).Splits ↔ (f.map i).Splits := by
  rw [map_id]

variable {i}

@[deprecated (since := "2025-11-25")]
alias Splits.comp_of_map_degree_le_one := Splits.comp_of_degree_le_one

variable (i)

@[deprecated (since := "2025-12-01")]
alias exists_root_of_splits' := Splits.exists_eval_eq_zero

@[deprecated (since := "2025-12-01")]
alias roots_ne_zero_of_splits' := Splits.roots_ne_zero

@[deprecated (since := "2025-12-01")]
alias rootOfSplits' := rootOfSplits

@[deprecated (since := "2025-12-01")]
alias map_rootOfSplits' := eval_rootOfSplits

@[deprecated (since := "2025-12-01")]
alias natDegree_eq_card_roots' := Splits.natDegree_eq_card_roots

@[deprecated (since := "2025-12-01")]
alias degree_eq_card_roots' := Splits.degree_eq_card_roots

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
@[deprecated (since := "2025-11-30")]
alias splits_iff := splits_iff_splits

/-- This lemma is for polynomials over a field. -/
@[deprecated (since := "2025-11-30")]
alias Splits.def := splits_iff_splits

@[deprecated (since := "2025-11-25")]
alias splits_of_splits_mul := splits_mul_iff

@[deprecated (since := "2025-11-25")]
alias splits_of_splits_of_dvd := Splits.splits_of_dvd

@[deprecated "Use `Splits.splits_of_dvd` directly." (since := "2025-11-30")]
theorem splits_of_splits_gcd_left [DecidableEq K] {f g : K[X]} (hf0 : f ≠ 0)
    (hf : Splits f) : Splits (EuclideanDomain.gcd f g) :=
  Splits.splits_of_dvd hf hf0 <| EuclideanDomain.gcd_dvd_left f g

@[deprecated "Use `Splits.splits_of_dvd` directly." (since := "2025-11-30")]
theorem splits_of_splits_gcd_right [DecidableEq K] {f g : K[X]} (hg0 : g ≠ 0)
    (hg : Splits g) : Splits (EuclideanDomain.gcd f g) :=
  Splits.splits_of_dvd hg hg0 <| EuclideanDomain.gcd_dvd_right f g

@[deprecated (since := "2025-11-30")]
alias degree_eq_one_of_irreducible_of_splits := Splits.degree_eq_one_of_irreducible

@[deprecated (since := "2025-12-01")]
alias exists_root_of_splits := Splits.exists_eval_eq_zero

@[deprecated (since := "2025-12-01")]
alias roots_ne_zero_of_splits := Splits.roots_ne_zero

@[deprecated (since := "2025-12-01")]
alias map_rootOfSplits := eval_rootOfSplits

/-- `rootOfSplits'` is definitionally equal to `rootOfSplits`. -/
@[deprecated "`rootOfSplits'` is now deprecated." (since := "2025-12-01")]
theorem rootOfSplits'_eq_rootOfSplits {f : K[X]} (hf : (f.map i).Splits) (hfd) :
    rootOfSplits hf hfd = rootOfSplits hf (f.degree_map i ▸ hfd) :=
  rfl

@[deprecated (since := "2025-11-30")]
alias natDegree_eq_card_roots := Splits.natDegree_eq_card_roots

@[deprecated (since := "2025-11-30")]
alias degree_eq_card_roots := Splits.degree_eq_card_roots

theorem roots_map {f : K[X]} (hf : f.Splits) : (f.map i).roots = f.roots.map i :=
  (roots_map_of_injective_of_card_eq_natDegree i.injective hf.natDegree_eq_card_roots.symm).symm

theorem Splits.mem_subfield_of_isRoot (F : Subfield K) {f : F[X]} (hnz : f ≠ 0)
    (hf : Splits f) {x : K} (hx : (f.map F.subtype).IsRoot x) :
    x ∈ F := by
  obtain ⟨x, _, rfl⟩ := Multiset.mem_map.mp
    (roots_map F.subtype hf ▸ mem_roots'.mpr ⟨Polynomial.map_ne_zero hnz, hx⟩)
  exact x.2

theorem image_rootSet [Algebra R K] [Algebra R L] {p : R[X]} (h : (p.map (algebraMap R K)).Splits)
    (f : K →ₐ[R] L) : f '' p.rootSet K = p.rootSet L := by
  classical
    rw [rootSet, ← Finset.coe_image, ← Multiset.toFinset_map, ← f.coe_toRingHom,
      ← roots_map _ h, map_map, f.comp_algebraMap,
      ← rootSet]

theorem adjoin_rootSet_eq_range [Algebra R K] [Algebra R L] {p : R[X]}
    (h : (p.map (algebraMap R K)).Splits) (f : K →ₐ[R] L) :
    Algebra.adjoin R (p.rootSet L) = f.range ↔ Algebra.adjoin R (p.rootSet K) = ⊤ := by
  rw [← image_rootSet h f, Algebra.adjoin_image, ← Algebra.map_top]
  exact (Subalgebra.map_injective f.toRingHom.injective).eq_iff

@[deprecated (since := "2025-11-25")]
alias eq_prod_roots_of_splits := Splits.eq_prod_roots

@[deprecated (since := "2025-11-25")]
alias eq_prod_roots_of_splits_id := Splits.eq_prod_roots

theorem Splits.dvd_of_roots_le_roots {p q : K[X]} (hp : p.Splits) (hp0 : p ≠ 0)
    (hq : p.roots ≤ q.roots) : p ∣ q := by
  rw [Splits.eq_prod_roots hp, C_mul_dvd (leadingCoeff_ne_zero.2 hp0)]
  exact dvd_trans
    (Multiset.prod_dvd_prod_of_le (Multiset.map_le_map hq))
    (prod_multiset_X_sub_C_dvd _)

theorem Splits.dvd_iff_roots_le_roots {p q : K[X]}
    (hp : p.Splits) (hp0 : p ≠ 0) (hq0 : q ≠ 0) :
    p ∣ q ↔ p.roots ≤ q.roots :=
  ⟨Polynomial.roots.le_of_dvd hq0, hp.dvd_of_roots_le_roots hp0⟩

theorem aeval_eq_prod_aroots_sub_of_splits [Algebra K L] {p : K[X]}
    (hsplit : Splits (p.map (algebraMap K L))) (v : L) :
    aeval v p = algebraMap K L p.leadingCoeff * ((p.aroots L).map fun a ↦ v - a).prod := by
  rw [← eval_map_algebraMap, Splits.eq_prod_roots hsplit]
  simp [eval_multiset_prod]

theorem eval_eq_prod_roots_sub_of_splits_id {p : K[X]}
    (hsplit : Splits p) (v : K) :
    eval v p = p.leadingCoeff * (p.roots.map fun a ↦ v - a).prod := by
  convert aeval_eq_prod_aroots_sub_of_splits (hsplit.map <| .id K) v
  rw [Algebra.algebraMap_self, map_id]

theorem eq_prod_roots_of_monic_of_splits_id {p : K[X]} (m : Monic p)
    (hsplit : Splits p) : p = (p.roots.map fun a => X - C a).prod := by
  convert Splits.eq_prod_roots hsplit
  simp [m]

theorem aeval_eq_prod_aroots_sub_of_monic_of_splits [Algebra K L] {p : K[X]} (m : Monic p)
    (hsplit : Splits (p.map (algebraMap K L))) (v : L) :
    aeval v p = ((p.aroots L).map fun a ↦ v - a).prod := by
  simp [aeval_eq_prod_aroots_sub_of_splits hsplit, m]

theorem eval_eq_prod_roots_sub_of_monic_of_splits_id {p : K[X]} (m : Monic p)
    (hsplit : Splits p) (v : K) :
    eval v p = (p.roots.map fun a ↦ v - a).prod := by
  simp [eval_eq_prod_roots_sub_of_splits_id hsplit, m]

theorem eq_X_sub_C_of_splits_of_single_root {x : K} {h : K[X]} (h_splits : Splits (h.map i))
    (h_roots : (h.map i).roots = {i x}) : h = C h.leadingCoeff * (X - C x) := by
  apply Polynomial.map_injective _ i.injective
  rw [Splits.eq_prod_roots h_splits, h_roots]
  simp

variable (R) in
theorem mem_lift_of_splits_of_roots_mem_range [Algebra R K] {f : K[X]}
    (hs : f.Splits) (hm : f.Monic)
    (hr : ∀ a ∈ f.roots, a ∈ (algebraMap R K).range) : f ∈ Polynomial.lifts (algebraMap R K) := by
  rw [eq_prod_roots_of_monic_of_splits_id hm hs, lifts_iff_liftsRing]
  refine Subring.multiset_prod_mem _ _ fun P hP => ?_
  obtain ⟨b, hb, rfl⟩ := Multiset.mem_map.1 hP
  exact Subring.sub_mem _ (X_mem_lifts _) (C'_mem_lifts (hr _ hb))

/--
A polynomial of degree `2` with a root splits.
-/
theorem splits_of_natDegree_eq_two {f : Polynomial K} {x : L} (h₁ : f.natDegree = 2)
    (h₂ : eval₂ i x f = 0) : Splits (f.map i) := by
  have hf₀ : f ≠ 0 := ne_zero_of_natDegree_gt (h₁ ▸ zero_lt_two)
  have h : (map i f /ₘ (X - C x)).natDegree = 1 := by
    rw [natDegree_divByMonic _ (monic_X_sub_C x), natDegree_map, h₁, natDegree_X_sub_C]
  replace h₂ := (mem_roots'.mp <| (mem_roots_map_of_injective i.injective hf₀).mpr h₂).2
  rw [← mul_divByMonic_eq_iff_isRoot.mpr h₂]
  exact (splits_mul_iff (X_sub_C_ne_zero x) (by simp [ne_zero_of_natDegree_gt, h])).mpr
    ⟨Splits.X_sub_C  _, Splits.of_natDegree_le_one (by rw [h])⟩

theorem splits_of_degree_eq_two {f : Polynomial K} {x : L} (h₁ : f.degree = 2)
    (h₂ : eval₂ i x f = 0) : Splits (f.map i) :=
  splits_of_natDegree_eq_two i (natDegree_eq_of_degree_eq_some h₁) h₂

section UFD

attribute [local instance] PrincipalIdealRing.to_uniqueFactorizationMonoid

local infixl:50 " ~ᵤ " => Associated

open UniqueFactorizationMonoid Associates

theorem splits_of_exists_multiset {f : K[X]} {s : Multiset L}
    (hs : f.map i = C (i f.leadingCoeff) * (s.map fun a : L => X - C a).prod) : Splits (f.map i) :=
  splits_iff_exists_multiset.mpr ⟨s, leadingCoeff_map i ▸ hs⟩

@[deprecated (since := "2025-11-30")]
alias splits_of_splits_id := Splits.map

end UFD

theorem splits_of_comp (j : L →+* F) {f : K[X]} (h : Splits (f.map (j.comp i)))
    (roots_mem_range : ∀ a ∈ (f.map (j.comp i)).roots, a ∈ j.range) : Splits (f.map i) := by
  choose lift lift_eq using roots_mem_range
  rw [splits_iff_exists_multiset]
  refine ⟨(f.map (j.comp i)).roots.pmap lift fun _ ↦ id, map_injective _ j.injective ?_⟩
  conv_lhs => rw [Polynomial.map_map, Splits.eq_prod_roots h]
  simp_rw [Polynomial.map_mul, Polynomial.map_multiset_prod, Multiset.map_pmap, Polynomial.map_sub,
    map_C, map_X, lift_eq, Multiset.pmap_eq_map]
  simp

theorem splits_id_of_splits {f : K[X]} (h : Splits (f.map i))
    (roots_mem_range : ∀ a ∈ (f.map i).roots, a ∈ i.range) : Splits (f.map (RingHom.id K)) :=
  splits_of_comp (RingHom.id K) i h roots_mem_range

theorem splits_comp_of_splits (i : R →+* K) (j : K →+* L) {f : R[X]} (h : Splits (f.map i)) :
    Splits (f.map (j.comp i)) :=
  f.map_map i j ▸ h.map j

variable [Algebra R K] [Algebra R L]

theorem splits_of_algHom {f : R[X]} (h : Splits (f.map (algebraMap R K))) (e : K →ₐ[R] L) :
    Splits (f.map (algebraMap R L)) := by
  rw [← e.comp_algebraMap_of_tower R]; exact splits_comp_of_splits _ _ h

variable (L) in
theorem splits_of_isScalarTower {f : R[X]} [Algebra K L] [IsScalarTower R K L]
    (h : Splits (f.map (algebraMap R K))) : Splits (f.map (algebraMap R L)) :=
  splits_of_algHom h (IsScalarTower.toAlgHom R K L)

theorem eval₂_derivative_of_splits [DecidableEq L] {P : K[X]} {f : K →+* L} (hP : (P.map f).Splits)
    (x : L) :
    eval₂ f x P.derivative = f (P.leadingCoeff) *
      ((P.map f).roots.map fun a ↦ (((P.map f).roots.erase a).map (x - ·)).prod).sum := by
  conv_lhs => rw [← eval_map, ← derivative_map, Splits.eq_prod_roots hP]
  classical
  simp [derivative_prod, eval_multisetSum, eval_multiset_prod]

theorem aeval_derivative_of_splits [Algebra K L] [DecidableEq L] {P : K[X]}
    (hP : (P.map (algebraMap K L)).Splits) (r : L) :
    aeval r P.derivative = algebraMap K L P.leadingCoeff *
      ((P.aroots L).map fun a ↦ (((P.aroots L).erase a).map (r - ·)).prod).sum :=
  eval₂_derivative_of_splits hP r

theorem eval_derivative_of_splits [DecidableEq K] {P : K[X]} (hP : P.Splits) (r : K) :
    eval r P.derivative = P.leadingCoeff *
      (P.roots.map fun a ↦ ((P.roots.erase a).map (r - ·)).prod).sum := by
  simpa using eval₂_derivative_of_splits (hP.map <| .id K) r

/-- Let `P` be a monic polynomial over `K` that splits over `L`. Let `r : L` be a root of `P`.
Then $P'(r) = \prod_{a}(r-a)$, where the product in the RHS is taken over all roots of `P` in `L`,
with the multiplicity of `r` reduced by one. -/
theorem aeval_root_derivative_of_splits [Algebra K L] [DecidableEq L] {P : K[X]} (hmo : P.Monic)
    (hP : (P.map (algebraMap K L)).Splits) {r : L} (hr : r ∈ P.aroots L) :
    aeval r (Polynomial.derivative P) = (((P.aroots L).erase r).map fun a => r - a).prod := by
  replace hmo := hmo.map (algebraMap K L)
  rw [aeval_def, ← eval_map, ← derivative_map]
  nth_rw 1 [eq_prod_roots_of_monic_of_splits_id hmo hP]
  rw [eval_multiset_prod_X_sub_C_derivative hr]

theorem eval_derivative_eq_eval_mul_sum_of_splits {p : K[X]} {x : K}
    (h : p.Splits) (hx : p.eval x ≠ 0) :
    p.derivative.eval x = p.eval x * (p.roots.map fun z ↦ 1 / (x - z)).sum := by
  classical
  suffices p.roots.map (fun z ↦ p.leadingCoeff * ((p.roots.erase z).map (fun w ↦ x - w) ).prod) =
      p.roots.map fun i ↦ p.leadingCoeff * ((x - i)⁻¹ * (p.roots.map (fun z ↦ x - z)).prod) by
    nth_rw 2 [Splits.eq_prod_roots h]
    simp [eval_derivative_of_splits h, ← Multiset.sum_map_mul_left, this, eval_multiset_prod,
      mul_comm, mul_left_comm]
  refine Multiset.map_congr rfl fun z hz ↦ ?_
  rw [← Multiset.prod_map_erase hz, inv_mul_cancel_left₀]
  aesop (add simp sub_eq_zero)

theorem eval_derivative_div_eval_of_ne_zero_of_splits {p : K[X]} {x : K}
    (h : p.Splits) (hx : p.eval x ≠ 0) :
    p.derivative.eval x / p.eval x = (p.roots.map fun z ↦ 1 / (x - z)).sum := by
  rw [eval_derivative_eq_eval_mul_sum_of_splits h hx]
  exact mul_div_cancel_left₀ _ hx

theorem coeff_zero_eq_leadingCoeff_mul_prod_roots_of_splits {P : K[X]}
    (hP : P.Splits) :
    P.coeff 0 = (-1) ^ P.natDegree * P.leadingCoeff * P.roots.prod := by
  nth_rw 1 [hP.eq_prod_roots]
  simp only [coeff_zero_eq_eval_zero, eval_mul, eval_C, eval_multiset_prod, Function.comp_apply,
    Multiset.map_map, eval_sub, eval_X, zero_sub, Multiset.prod_map_neg]
  grind [splits_iff_card_roots]

/-- If `P` is a monic polynomial that splits, then `coeff P 0` equals the product of the roots. -/
theorem coeff_zero_eq_prod_roots_of_monic_of_splits {P : K[X]} (hmo : P.Monic)
    (hP : P.Splits) : coeff P 0 = (-1) ^ P.natDegree * P.roots.prod := by
  simp [hmo, coeff_zero_eq_leadingCoeff_mul_prod_roots_of_splits hP]

theorem nextCoeff_eq_neg_sum_roots_mul_leadingCoeff_of_splits {P : K[X]}
    (hP : P.Splits) : P.nextCoeff = -P.leadingCoeff * P.roots.sum := by
  nth_rw 1 [Splits.eq_prod_roots hP]
  simp [Multiset.sum_map_neg', monic_X_sub_C, Monic.nextCoeff_multiset_prod]

/-- If `P` is a monic polynomial that splits, then `P.nextCoeff` equals the negative of the sum
of the roots. -/
theorem nextCoeff_eq_neg_sum_roots_of_monic_of_splits {P : K[X]} (hmo : P.Monic)
    (hP : P.Splits) : P.nextCoeff = -P.roots.sum := by
  simp [hmo, nextCoeff_eq_neg_sum_roots_mul_leadingCoeff_of_splits hP]

@[deprecated (since := "2025-10-08")]
alias prod_roots_eq_coeff_zero_of_monic_of_splits := coeff_zero_eq_prod_roots_of_monic_of_splits

@[deprecated (since := "2025-10-08")]
alias sum_roots_eq_nextCoeff_of_monic_of_split := nextCoeff_eq_neg_sum_roots_of_monic_of_splits

end Splits

end Polynomial
