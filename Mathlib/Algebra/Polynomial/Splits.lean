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

theorem splits_mul {f g : K[X]} (hf : Splits (f.map i)) (hg : Splits (g.map i)) :
    Splits ((f * g).map i) := by
  simp [hf.mul hg]

theorem splits_of_splits_mul' {f g : K[X]} (hfg : (f * g).map i ≠ 0) (h : Splits ((f * g).map i)) :
    Splits (f.map i) ∧ Splits (g.map i) := by
  simp only [Splits, Polynomial.map_mul, mul_ne_zero_iff] at hfg h
  exact (splits_mul_iff hfg.1 hfg.2).mp h

@[deprecated "Use `Polynomial.map_map` instead." (since := "2025-11-24")]
theorem splits_map_iff {L : Type*} [CommRing L] (i : K →+* L) (j : L →+* F) {f : K[X]} :
    Splits ((f.map i).map j) ↔ Splits (f.map (j.comp i)) := by
  rw [Polynomial.map_map]

@[deprecated (since := "2025-11-24")]
alias splits_one := Splits.one

theorem splits_of_isUnit [IsDomain K] {u : K[X]} (hu : IsUnit u) : (u.map i).Splits :=
  (isUnit_iff.mp hu).choose_spec.2 ▸ map_C i ▸ Splits.C _

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

theorem Splits.comp_of_degree_le_one {f : L[X]} {p : L[X]} (hd : p.degree ≤ 1)
    (h : f.Splits) : (f.comp p).Splits := by
  obtain ⟨m, hm⟩ := splits_iff_exists_multiset.mp h
  rw [hm, mul_comp, C_comp, multiset_prod_comp]
  refine (Splits.C _).mul (Splits.multisetProd ?_)
  simp only [Multiset.mem_map]
  rintro - ⟨-, ⟨a, -, rfl⟩, rfl⟩
  apply Splits.of_degree_le_one
  grw [sub_comp, X_comp, C_comp, degree_sub_le, hd, degree_C_le, max_eq_left zero_le_one]

@[deprecated (since := "2025-11-24")]
alias Splits.comp_of_map_degree_le_one := Splits.comp_of_degree_le_one

theorem splits_iff_comp_splits_of_degree_eq_one {f : L[X]} {p : L[X]} (hd : p.degree = 1) :
    f.Splits ↔ (f.comp p).Splits := by
  refine ⟨Splits.comp_of_degree_le_one hd.le, fun h ↦ ?_⟩
  let _ := invertibleOfNonzero (leadingCoeff_ne_zero.mpr
      (ne_zero_of_degree_gt (n := ⊥) (by rw [hd]; decide)))
  have : f = (f.comp p).comp ((C ⅟p.leadingCoeff *
      (X - C (p.coeff 0)))) := by
    rw [comp_assoc]
    nth_rw 1 [eq_X_add_C_of_degree_eq_one hd]
    simp only [invOf_eq_inv, mul_sub, ← C_mul, add_comp, mul_comp, C_comp, X_comp,
      ← mul_assoc]
    simp
  rw [this]
  refine Splits.comp_of_degree_le_one ?_ h
  simp [degree_C (inv_ne_zero (Invertible.ne_zero (a := p.leadingCoeff)))]

theorem Splits.comp_X_sub_C (a : L) {f : L[X]}
    (h : f.Splits) : (f.comp (X - C a)).Splits :=
  Splits.comp_of_degree_le_one (degree_X_sub_C_le _) h

theorem Splits.comp_X_add_C (a : L) {f : L[X]}
    (h : f.Splits) : (f.comp (X + C a)).Splits :=
  Splits.comp_of_degree_le_one (degree_X_add_C a).le h

variable (i)

theorem exists_root_of_splits' {f : K[X]} (hs : Splits (f.map i)) (hf0 : degree (f.map i) ≠ 0) :
    ∃ x, eval₂ i x f = 0 := by
  simpa only [eval_map] using hs.exists_eval_eq_zero hf0

theorem roots_ne_zero_of_splits' {f : K[X]} (hs : Splits (f.map i))
    (hf0 : natDegree (f.map i) ≠ 0) : (f.map i).roots ≠ 0 :=
  hs.roots_ne_zero hf0

/-- Pick a root of a polynomial that splits. See `rootOfSplits` for polynomials over a field
which has simpler assumptions. -/
def rootOfSplits' {f : K[X]} (hf : (f.map i).Splits) (hfd : (f.map i).degree ≠ 0) : L :=
  Classical.choose <| exists_root_of_splits' i hf hfd

theorem map_rootOfSplits' {f : K[X]} (hf : (f.map i).Splits) (hfd) :
    f.eval₂ i (rootOfSplits' i hf hfd) = 0 :=
  Classical.choose_spec <| exists_root_of_splits' i hf hfd

theorem natDegree_eq_card_roots' {p : K[X]} {i : K →+* L} (hsplit : Splits (p.map i)) :
    (p.map i).natDegree = Multiset.card (p.map i).roots :=
  hsplit.natDegree_eq_card_roots

theorem degree_eq_card_roots' {p : K[X]} {i : K →+* L} (p_ne_zero : p.map i ≠ 0)
    (hsplit : Splits (p.map i)) : (p.map i).degree = Multiset.card (p.map i).roots := by
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
    Splits (f.map i) ↔ f = 0 ∨ ∀ {g : L[X]}, Irreducible g → g ∣ f.map i → degree g = 1 := by
  rw [splits_iff_splits, Polynomial.map_eq_zero]

/-- This lemma is for polynomials over a field. -/
theorem Splits.def {i : K →+* L} {f : K[X]} (h : Splits (f.map i)) :
    f = 0 ∨ ∀ {g : L[X]}, Irreducible g → g ∣ f.map i → degree g = 1 :=
  (splits_iff i f).mp h

theorem splits_of_splits_mul {f g : K[X]} (hfg : f * g ≠ 0) (h : Splits ((f * g).map i)) :
    Splits (f.map i) ∧ Splits (g.map i) :=
  splits_of_splits_mul' i (map_ne_zero hfg) h

theorem splits_of_splits_of_dvd {f g : K[X]} (hf0 : f ≠ 0) (hf : Splits (f.map i)) (hgf : g ∣ f) :
    Splits (g.map i) := by
  obtain ⟨f, rfl⟩ := hgf
  exact (splits_of_splits_mul i hf0 hf).1

theorem splits_of_splits_gcd_left [DecidableEq K] {f g : K[X]} (hf0 : f ≠ 0)
    (hf : Splits (f.map i)) : Splits ((EuclideanDomain.gcd f g).map i) :=
  Polynomial.splits_of_splits_of_dvd i hf0 hf (EuclideanDomain.gcd_dvd_left f g)

theorem splits_of_splits_gcd_right [DecidableEq K] {f g : K[X]} (hg0 : g ≠ 0)
    (hg : Splits (g.map i)) : Splits ((EuclideanDomain.gcd f g).map i) :=
  Polynomial.splits_of_splits_of_dvd i hg0 hg (EuclideanDomain.gcd_dvd_right f g)

theorem splits_prod_iff {ι : Type u} {s : ι → K[X]} {t : Finset ι} :
    (∀ j ∈ t, s j ≠ 0) → (((∏ x ∈ t, s x).map i).Splits ↔ ∀ j ∈ t, ((s j).map i).Splits) := by
  classical
  refine
    Finset.induction_on t (fun _ =>
        ⟨fun _ _ h => by simp only [Finset.notMem_empty] at h, by simp⟩)
      fun a t hat ih ht => ?_
  rw [Finset.forall_mem_insert] at ht ⊢
  rw [Finset.prod_insert hat, Polynomial.map_mul, splits_mul_iff (map_ne_zero ht.1)
    (map_ne_zero (Finset.prod_ne_zero_iff.2 ht.2)), ih ht.2]

theorem degree_eq_one_of_irreducible_of_splits {p : K[X]} (hp : Irreducible p)
    (hp_splits : Splits (p.map (RingHom.id K))) : p.degree = 1 := by
  rw [splits_iff_splits] at hp_splits
  rcases hp_splits with ⟨⟩ | hp_splits
  · exfalso
    simp_all
  · apply hp_splits hp
    simp

theorem exists_root_of_splits {f : K[X]} (hs : Splits (f.map i)) (hf0 : degree f ≠ 0) :
    ∃ x, eval₂ i x f = 0 :=
  exists_root_of_splits' i hs ((f.degree_map i).symm ▸ hf0)

theorem roots_ne_zero_of_splits {f : K[X]} (hs : Splits (f.map i)) (hf0 : natDegree f ≠ 0) :
    (f.map i).roots ≠ 0 :=
  roots_ne_zero_of_splits' i hs (ne_of_eq_of_ne (natDegree_map i) hf0)

/-- Pick a root of a polynomial that splits. This version is for polynomials over a field and has
simpler assumptions. -/
def rootOfSplits {f : K[X]} (hf : (f.map i).Splits) (hfd : f.degree ≠ 0) : L :=
  rootOfSplits' i hf ((f.degree_map i).symm ▸ hfd)

/-- `rootOfSplits'` is definitionally equal to `rootOfSplits`. -/
theorem rootOfSplits'_eq_rootOfSplits {f : K[X]} (hf : (f.map i).Splits) (hfd) :
    rootOfSplits' i hf hfd = rootOfSplits i hf (f.degree_map i ▸ hfd) :=
  rfl

theorem map_rootOfSplits {f : K[X]} (hf : (f.map i).Splits) (hfd) :
    f.eval₂ i (rootOfSplits i hf hfd) = 0 :=
  map_rootOfSplits' i hf (ne_of_eq_of_ne (degree_map f i) hfd)

theorem natDegree_eq_card_roots {p : K[X]} {i : K →+* L} (hsplit : Splits (p.map i)) :
    p.natDegree = Multiset.card (p.map i).roots :=
  (natDegree_map i).symm.trans <| natDegree_eq_card_roots' hsplit

theorem degree_eq_card_roots {p : K[X]} {i : K →+* L} (p_ne_zero : p ≠ 0)
    (hsplit : Splits (p.map i)) : p.degree = Multiset.card (p.map i).roots := by
  rw [degree_eq_natDegree p_ne_zero, natDegree_eq_card_roots hsplit]

theorem roots_map {f : K[X]} (hf : f.Splits) : (f.map i).roots = f.roots.map i :=
  (roots_map_of_injective_of_card_eq_natDegree i.injective <| by
      convert (natDegree_eq_card_roots (hf.map <| .id K)).symm
      rw [map_id]).symm

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

theorem eq_prod_roots_of_splits {p : K[X]} {i : K →+* L} (hsplit : Splits (p.map i)) :
    p.map i = C (i p.leadingCoeff) * ((p.map i).roots.map fun a => X - C a).prod := by
  rw [← leadingCoeff_map]; symm
  apply C_leadingCoeff_mul_prod_multiset_X_sub_C
  rw [natDegree_map]; exact (natDegree_eq_card_roots hsplit).symm

theorem eq_prod_roots_of_splits_id {p : K[X]} (hsplit : Splits p) :
    p = C p.leadingCoeff * (p.roots.map fun a => X - C a).prod :=
  hsplit.eq_prod_roots

theorem Splits.dvd_of_roots_le_roots {p q : K[X]} (hp : p.Splits) (hp0 : p ≠ 0)
    (hq : p.roots ≤ q.roots) : p ∣ q := by
  rw [eq_prod_roots_of_splits_id hp, C_mul_dvd (leadingCoeff_ne_zero.2 hp0)]
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
  rw [← eval_map_algebraMap, eq_prod_roots_of_splits hsplit]
  simp [eval_multiset_prod]

theorem eval_eq_prod_roots_sub_of_splits_id {p : K[X]}
    (hsplit : Splits p) (v : K) :
    eval v p = p.leadingCoeff * (p.roots.map fun a ↦ v - a).prod := by
  convert aeval_eq_prod_aroots_sub_of_splits (hsplit.map <| .id K) v
  rw [Algebra.algebraMap_self, map_id]

theorem eq_prod_roots_of_monic_of_splits_id {p : K[X]} (m : Monic p)
    (hsplit : Splits p) : p = (p.roots.map fun a => X - C a).prod := by
  convert eq_prod_roots_of_splits_id hsplit
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
  rw [eq_prod_roots_of_splits h_splits, h_roots]
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

theorem splits_of_splits_id {f : K[X]} (h : Splits (f.map (RingHom.id K))) : Splits (f.map i) := by
  simpa using h.map i

end UFD

theorem splits_of_comp (j : L →+* F) {f : K[X]} (h : Splits (f.map (j.comp i)))
    (roots_mem_range : ∀ a ∈ (f.map (j.comp i)).roots, a ∈ j.range) : Splits (f.map i) := by
  choose lift lift_eq using roots_mem_range
  rw [splits_iff_exists_multiset]
  refine ⟨(f.map (j.comp i)).roots.pmap lift fun _ ↦ id, map_injective _ j.injective ?_⟩
  conv_lhs => rw [Polynomial.map_map, eq_prod_roots_of_splits h]
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

/-- A polynomial splits if and only if it has as many roots as its degree. -/
theorem splits_iff_card_roots {p : K[X]} :
    Splits p ↔ Multiset.card p.roots = p.natDegree := by
  constructor
  · intro H
    rw [H.natDegree_eq_card_roots]
  · intro hroots
    rw [splits_iff_exists_multiset]
    use p.roots
    exact (C_leadingCoeff_mul_prod_multiset_X_sub_C hroots).symm

theorem eval₂_derivative_of_splits [DecidableEq L] {P : K[X]} {f : K →+* L} (hP : (P.map f).Splits)
    (x : L) :
    eval₂ f x P.derivative = f (P.leadingCoeff) *
      ((P.map f).roots.map fun a ↦ (((P.map f).roots.erase a).map (x - ·)).prod).sum := by
  conv_lhs => rw [← eval_map, ← derivative_map, eq_prod_roots_of_splits hP]
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
    nth_rw 2 [p.eq_prod_roots_of_splits_id h]
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
  nth_rw 1 [eq_prod_roots_of_splits_id hP]
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
