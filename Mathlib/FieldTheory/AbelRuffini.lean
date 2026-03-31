/-
Copyright (c) 2020 Thomas Browning and Patrick Lutz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning, Patrick Lutz
-/
module

public import Mathlib.FieldTheory.AlgebraicClosure
public import Mathlib.FieldTheory.PolynomialGaloisGroup
public import Mathlib.GroupTheory.Solvable
public import Mathlib.RingTheory.RootsOfUnity.Basic

/-!
# The Abel-Ruffini Theorem

This file proves one direction of the Abel-Ruffini theorem, namely that if an element is solvable
by radicals, then its minimal polynomial has solvable Galois group.

## Main definitions

* `solvableByRad F E` : the intermediate field of solvable-by-radicals elements

## Main results

* The Abel-Ruffini Theorem `isSolvable_gal_of_irreducible`: An irreducible polynomial with a root
  that is solvable by radicals has a solvable Galois group.
-/

public section

open Polynomial

variable {F E : Type*} [Field F] [Field E] [Algebra F E]

theorem gal_zero_isSolvable : IsSolvable (0 : F[X]).Gal := by infer_instance

theorem gal_one_isSolvable : IsSolvable (1 : F[X]).Gal := by infer_instance

theorem gal_C_isSolvable (x : F) : IsSolvable (C x).Gal := by infer_instance

theorem gal_X_isSolvable : IsSolvable (X : F[X]).Gal := by infer_instance

theorem gal_X_sub_C_isSolvable (x : F) : IsSolvable (X - C x).Gal := by infer_instance

theorem gal_X_pow_isSolvable (n : ℕ) : IsSolvable (X ^ n : F[X]).Gal := by infer_instance

theorem gal_mul_isSolvable {p q : F[X]} (_ : IsSolvable p.Gal) (_ : IsSolvable q.Gal) :
    IsSolvable (p * q).Gal :=
  solvable_of_solvable_injective (Gal.restrictProd_injective p q)

theorem gal_prod_isSolvable {s : Multiset F[X]} (hs : ∀ p ∈ s, IsSolvable (Gal p)) :
    IsSolvable s.prod.Gal := by
  apply Multiset.induction_on' s
  · exact gal_one_isSolvable
  · intro p t hps _ ht
    rw [Multiset.insert_eq_cons, Multiset.prod_cons]
    exact gal_mul_isSolvable (hs p hps) ht

theorem gal_isSolvable_of_splits {p q : F[X]}
    (_ : Fact ((p.map (algebraMap F q.SplittingField)).Splits)) (hq : IsSolvable q.Gal) :
    IsSolvable p.Gal :=
  haveI : IsSolvable (q.SplittingField ≃ₐ[F] q.SplittingField) := hq
  solvable_of_surjective (AlgEquiv.restrictNormalHom_surjective q.SplittingField)

theorem gal_isSolvable_tower (p q : F[X]) (hpq : (p.map (algebraMap F q.SplittingField)).Splits)
    (hp : IsSolvable p.Gal) (hq : IsSolvable (q.map (algebraMap F p.SplittingField)).Gal) :
    IsSolvable q.Gal := by
  let K := p.SplittingField
  let L := q.SplittingField
  haveI : Fact ((p.map (algebraMap F L)).Splits) := ⟨hpq⟩
  let ϕ : Gal(L/K) ≃* (q.map (algebraMap F K)).Gal :=
    (IsSplittingField.algEquiv L (q.map (algebraMap F K))).autCongr
  have ϕ_inj : Function.Injective ϕ.toMonoidHom := ϕ.injective
  haveI : IsSolvable Gal(K/F) := hp
  haveI : IsSolvable Gal(L/K) := solvable_of_solvable_injective ϕ_inj
  exact isSolvable_of_isScalarTower F p.SplittingField q.SplittingField

section GalXPowSubC

set_option backward.isDefEq.respectTransparency false in
theorem gal_X_pow_sub_one_isSolvable (n : ℕ) : IsSolvable (X ^ n - 1 : F[X]).Gal := by
  by_cases hn : n = 0
  · rw [hn, pow_zero, sub_self]
    exact gal_zero_isSolvable
  have hn' : 0 < n := pos_iff_ne_zero.mpr hn
  have hn'' : (X ^ n - 1 : F[X]) ≠ 0 := X_pow_sub_C_ne_zero hn' 1
  apply isSolvable_of_comm
  intro σ τ
  ext a ha
  simp only [mem_rootSet_of_ne hn'', map_sub, aeval_X_pow, aeval_one, sub_eq_zero] at ha
  have key : ∀ σ : (X ^ n - 1 : F[X]).Gal, ∃ m : ℕ, σ a = a ^ m := by
    intro σ
    lift n to ℕ+ using hn'
    exact map_rootsOfUnity_eq_pow_self σ.toAlgHom (rootsOfUnity.mkOfPowEq a ha)
  obtain ⟨c, hc⟩ := key σ
  obtain ⟨d, hd⟩ := key τ
  rw [σ.mul_apply, τ.mul_apply, hc, map_pow, hd, map_pow, hc, ← pow_mul, pow_mul']

set_option backward.isDefEq.respectTransparency false in
theorem gal_X_pow_sub_C_isSolvable_aux (n : ℕ) (a : F)
    (h : ((X ^ n - 1 : F[X]).map (RingHom.id F)).Splits) : IsSolvable (X ^ n - C a).Gal := by
  by_cases ha : a = 0
  · rw [ha, C_0, sub_zero]
    exact gal_X_pow_isSolvable n
  have ha' : algebraMap F (X ^ n - C a).SplittingField a ≠ 0 :=
    mt ((injective_iff_map_eq_zero _).mp (RingHom.injective _) a) ha
  by_cases hn : n = 0
  · rw [hn, pow_zero, ← C_1, ← C_sub]
    exact gal_C_isSolvable (1 - a)
  have hn' : 0 < n := pos_iff_ne_zero.mpr hn
  have hn'' : X ^ n - C a ≠ 0 := X_pow_sub_C_ne_zero hn' a
  have hn''' : (X ^ n - 1 : F[X]) ≠ 0 := X_pow_sub_C_ne_zero hn' 1
  have mem_range : ∀ {c : (X ^ n - C a).SplittingField},
      (c ^ n = 1 → (∃ d, algebraMap F (X ^ n - C a).SplittingField d = c)) := fun {c} hc =>
    RingHom.mem_range.mp (minpoly.mem_range_of_degree_eq_one F c
      (Splits.degree_eq_one_of_irreducible (h.of_dvd (map_ne_zero hn''')
        (minpoly.dvd F c (by rwa [map_id, map_sub, sub_eq_zero, aeval_X_pow, aeval_one])))
          (minpoly.irreducible ((SplittingField.instNormal (X ^ n - C a)).isIntegral c))))
  apply isSolvable_of_comm
  intro σ τ
  ext b hb
  rw [mem_rootSet_of_ne hn'', map_sub, aeval_X_pow, aeval_C, sub_eq_zero] at hb
  have hb' : b ≠ 0 := by
    intro hb'
    rw [hb', zero_pow hn] at hb
    exact ha' hb.symm
  have key : ∀ σ : (X ^ n - C a).Gal, ∃ c, σ b = b * algebraMap F _ c := by
    intro σ
    have key : (σ b / b) ^ n = 1 := by rw [div_pow, ← map_pow, hb, σ.commutes, div_self ha']
    obtain ⟨c, hc⟩ := mem_range key
    use c
    rw [hc, mul_div_cancel₀ (σ b) hb']
  obtain ⟨c, hc⟩ := key σ
  obtain ⟨d, hd⟩ := key τ
  rw [σ.mul_apply, τ.mul_apply, hc, map_mul, τ.commutes, hd, map_mul, σ.commutes, hc,
    mul_assoc, mul_assoc, mul_right_inj' hb', mul_comm]

theorem splits_X_pow_sub_one_of_X_pow_sub_C {F : Type*} [Field F] {E : Type*} [Field E]
    (i : F →+* E) (n : ℕ) {a : F} (ha : a ≠ 0) (h : ((X ^ n - C a).map i).Splits) :
    ((X ^ n - 1 : F[X]).map i).Splits := by
  have ha' : i a ≠ 0 := mt ((injective_iff_map_eq_zero i).mp i.injective a) ha
  by_cases hn : n = 0
  · simp [hn]
  have hn' : 0 < n := pos_iff_ne_zero.mpr hn
  have hn'' : (X ^ n - C a).degree ≠ 0 :=
    ne_of_eq_of_ne (degree_X_pow_sub_C hn' a) (mt WithBot.coe_eq_coe.mp hn)
  obtain ⟨b, hb⟩ := Splits.exists_eval_eq_zero h (by rwa [degree_map])
  rw [eval_map, eval₂_sub, eval₂_X_pow, eval₂_C, sub_eq_zero] at hb
  have hb' : b ≠ 0 := by
    intro hb'
    rw [hb', zero_pow hn] at hb
    exact ha' hb.symm
  let s := ((X ^ n - C a).map i).roots
  have hs : _ = _ * (s.map _).prod := h.eq_prod_roots
  rw [leadingCoeff_map, leadingCoeff_X_pow_sub_C hn', RingHom.map_one, C_1, one_mul] at hs
  have hs' : Multiset.card s = n := by
    rw [← h.natDegree_eq_card_roots, natDegree_map, natDegree_X_pow_sub_C]
  rw [splits_iff_exists_multiset, leadingCoeff_map]
  use (s.map fun c ↦ c / b)
  rw [leadingCoeff_X_pow_sub_one hn', map_one, C_1, one_mul, Multiset.map_map]
  have C_mul_C : C (i a⁻¹) * C (i a) = 1 := by
    rw [← C_mul, ← i.map_mul, inv_mul_cancel₀ ha, i.map_one, C_1]
  have key1 : (X ^ n - 1 : F[X]).map i = C (i a⁻¹) * ((X ^ n - C a).map i).comp (C b * X) := by
    rw [Polynomial.map_sub, Polynomial.map_sub, Polynomial.map_pow, map_X, map_C,
      Polynomial.map_one, sub_comp, pow_comp, X_comp, C_comp, mul_pow, ← C_pow, hb, mul_sub, ←
      mul_assoc, C_mul_C, one_mul]
  have key2 : ((fun q : E[X] => q.comp (C b * X)) ∘ fun c : E => X - C c) = fun c : E =>
      C b * (X - C (c / b)) := by
    ext1 c
    dsimp only [Function.comp_apply]
    rw [sub_comp, X_comp, C_comp, mul_sub, ← C_mul, mul_div_cancel₀ c hb']
  rw [key1, hs, multiset_prod_comp, Multiset.map_map, key2, Multiset.prod_map_mul,
    Function.const_def (α := E) (y := C b), Multiset.map_const, Multiset.prod_replicate,
    hs', ← C_pow, hb, ← mul_assoc, C_mul_C, one_mul]
  rfl

theorem gal_X_pow_sub_C_isSolvable (n : ℕ) (x : F) : IsSolvable (X ^ n - C x).Gal := by
  by_cases hx : x = 0
  · rw [hx, C_0, sub_zero]
    exact gal_X_pow_isSolvable n
  apply gal_isSolvable_tower (X ^ n - 1) (X ^ n - C x)
  · exact splits_X_pow_sub_one_of_X_pow_sub_C _ n hx (SplittingField.splits _)
  · exact gal_X_pow_sub_one_isSolvable n
  · rw [Polynomial.map_sub, Polynomial.map_pow, map_X, map_C]
    apply gal_X_pow_sub_C_isSolvable_aux
    rw [map_id]
    have key := SplittingField.splits (X ^ n - 1 : F[X])
    rwa [Polynomial.map_sub, Polynomial.map_pow, map_X,
      Polynomial.map_one] at key

end GalXPowSubC

variable (F E) in
/-- The intermediate field of elements solvable by radicals, defined as the smallest subfield which
is closed under `n`-th roots. -/
def solvableByRad : IntermediateField F E :=
  sInf {s | ∀ x, ∀ n ≠ 0, x ^ n ∈ s → x ∈ s}

variable (F) in
/-- Inductive definition of solvable by radicals -/
@[deprecated solvableByRad (since := "2026-02-28")]
inductive IsSolvableByRad : E → Prop
  | base (α : F) : IsSolvableByRad (algebraMap F E α)
  | add (α β : E) : IsSolvableByRad α → IsSolvableByRad β → IsSolvableByRad (α + β)
  | neg (α : E) : IsSolvableByRad α → IsSolvableByRad (-α)
  | mul (α β : E) : IsSolvableByRad α → IsSolvableByRad β → IsSolvableByRad (α * β)
  | inv (α : E) : IsSolvableByRad α → IsSolvableByRad α⁻¹
  | rad (α : E) (n : ℕ) (hn : n ≠ 0) : IsSolvableByRad (α ^ n) → IsSolvableByRad α

theorem solvableByRad_le {s : IntermediateField F E} (H : ∀ x, ∀ n ≠ 0, x ^ n ∈ s → x ∈ s) :
    solvableByRad F E ≤ s :=
  sInf_le H

theorem solvableByRad.rad_mem {x : E} {n : ℕ} (hn : n ≠ 0) (hx : x ^ n ∈ solvableByRad F E) :
    x ∈ solvableByRad F E := by
  grind [solvableByRad]

variable (F E) in
theorem solvableByRad_le_algClosure : solvableByRad F E ≤ algebraicClosure F E := by
  refine solvableByRad_le fun x n hn hx ↦ ?_
  rw [mem_algebraicClosure_iff] at hx ⊢
  obtain ⟨p, h1, h2⟩ := hx
  refine ⟨p.comp (X ^ n), ⟨fun h ↦ h1 (leadingCoeff_eq_zero.mp ?_), ?_⟩⟩
  · rwa [← leadingCoeff_eq_zero, leadingCoeff_comp, leadingCoeff_X_pow, one_pow, mul_one] at h
    rwa [natDegree_X_pow]
  · simpa [aeval_comp]

theorem isAlgebraic_solvableByRad : (solvableByRad F E).IsAlgebraic :=
  fun _ hx ↦ mem_algebraicClosure_iff.1 (solvableByRad_le_algClosure _ _ hx)

theorem isIntegral_of_mem_solvableByRad {x : E} (hx : x ∈ solvableByRad F E) : IsIntegral F x :=
  (isAlgebraic_solvableByRad _ hx).isIntegral

@[deprecated (since := "2026-02-28")]
alias solvableByRad.isIntegral := isIntegral_of_mem_solvableByRad

/-- An induction principle for `solvableByRad`. -/
@[elab_as_elim]
protected theorem solvableByRad.induction (motive : ∀ x, x ∈ solvableByRad F E → Prop)
    (mem : ∀ x, motive (algebraMap F E x) (algebraMap_mem _ _))
    (add : ∀ x y (hx : x ∈ solvableByRad F E) (hy : y ∈ solvableByRad F E),
      motive x hx → motive y hy → motive (x + y) (add_mem hx hy))
    (mul : ∀ x y (hx : x ∈ solvableByRad F E) (hy : y ∈ solvableByRad F E),
      motive x hx → motive y hy → motive (x * y) (mul_mem hx hy))
    (rad : ∀ n x (hn : n ≠ 0) (hx : x ^ n ∈ solvableByRad F E),
      motive (x ^ n) hx → motive x (rad_mem hn hx))
    {x : E} (hx : x ∈ solvableByRad F E) : motive x hx := by
  let s : Subalgebra F E :=
  { carrier := {x | ∃ hx : x ∈ solvableByRad F E, motive x hx}
    algebraMap_mem' a := ⟨algebraMap_mem _ a, mem a⟩
    add_mem' := fun ⟨ha, ha'⟩ ⟨hb, hb'⟩ ↦ ⟨add_mem ha hb, add _ _ ha hb ha' hb'⟩
    mul_mem' := fun ⟨ha, ha'⟩ ⟨hb, hb'⟩ ↦ ⟨mul_mem ha hb, mul _ _ ha hb ha' hb'⟩ }
  let t : IntermediateField F E := Subalgebra.IsAlgebraic.toIntermediateField (S := s) <| by
    rintro x ⟨hx, hx'⟩
    apply isAlgebraic_solvableByRad
    exact hx
  have ht (x n) (hn : n ≠ 0) : x ^ n ∈ t → x ∈ t := by
    rintro ⟨hx, hx'⟩
    exact ⟨rad_mem hn hx, rad _ _ hn hx hx'⟩
  obtain ⟨_, h⟩ := solvableByRad_le (s := t) ht hx
  exact h

private theorem induction_rad {x : E} (hx : x ∈ solvableByRad F E) {n : ℕ} (hn : n ≠ 0)
    (hα : IsSolvable (minpoly F (x ^ n)).Gal) : IsSolvable (minpoly F x).Gal := by
  let p := minpoly F (x ^ n)
  have hp : p.comp (X ^ n) ≠ 0 := by
    intro h
    rcases comp_eq_zero_iff.mp h with h' | h'
    · exact minpoly.ne_zero (isIntegral_of_mem_solvableByRad (pow_mem hx n)) h'
    · exact hn (by rw [← @natDegree_C F, ← h'.2, natDegree_X_pow])
  apply gal_isSolvable_of_splits
  · exact ⟨(SplittingField.splits (p.comp (X ^ n))).of_dvd (map_ne_zero hp)
      ((map_dvd_map' _).mpr (minpoly.dvd F x (by rw [aeval_comp, aeval_X_pow, minpoly.aeval])))⟩
  · refine gal_isSolvable_tower p (p.comp (X ^ n)) ?_ hα ?_
    · exact Gal.splits_in_splittingField_of_comp _ _ (by rwa [natDegree_X_pow])
    · obtain ⟨s, hs⟩ := splits_iff_exists_multiset.1 (SplittingField.splits p)
      rw [map_comp, Polynomial.map_pow, map_X, hs, mul_comp, C_comp]
      apply gal_mul_isSolvable (gal_C_isSolvable _)
      rw [multiset_prod_comp]
      apply gal_prod_isSolvable
      intro q hq
      rw [Multiset.mem_map] at hq
      obtain ⟨q, hq, rfl⟩ := hq
      rw [Multiset.mem_map] at hq
      obtain ⟨q, _, rfl⟩ := hq
      rw [sub_comp, X_comp, C_comp]
      exact gal_X_pow_sub_C_isSolvable n q

open IntermediateField

private theorem induction_step {x y z : E}
    (hx : x ∈ solvableByRad F E) (hy : y ∈ solvableByRad F E) (hz : z ∈ solvableByRad F E)
    (hx' : IsSolvable (minpoly F x).Gal) (hy' : IsSolvable (minpoly F y).Gal) (hz' : z ∈ F⟮x, y⟯) :
    IsSolvable (minpoly F z).Gal := by
  let p := minpoly F x
  let q := minpoly F y
  have hpq := SplittingField.splits (p * q)
  rw [Polynomial.map_mul,
    splits_mul_iff (map_ne_zero (minpoly.ne_zero (isIntegral_of_mem_solvableByRad hx)))
      (map_ne_zero (minpoly.ne_zero (isIntegral_of_mem_solvableByRad hy)))] at hpq
  have f : ↥F⟮x, y⟯ →ₐ[F] (p * q).SplittingField :=
    Classical.choice <| nonempty_algHom_adjoin_of_splits <| by
      rintro a (rfl | rfl)
      · exact ⟨isIntegral_of_mem_solvableByRad hx, hpq.1⟩
      · exact ⟨isIntegral_of_mem_solvableByRad hy, hpq.2⟩
  have key : minpoly F z = minpoly F (f ⟨z, hz'⟩) := by
    refine minpoly.eq_of_irreducible_of_monic
      (minpoly.irreducible (isIntegral_of_mem_solvableByRad hz)) ?_
      (minpoly.monic (isIntegral_of_mem_solvableByRad hz))
    rw [aeval_algHom_apply, map_eq_zero]
    apply (algebraMap (↥F⟮x, y⟯) E).injective
    simp [← aeval_algebraMap_apply]
  rw [key]
  refine gal_isSolvable_of_splits ⟨Normal.splits ?_ (f ⟨z, hz'⟩)⟩ (gal_mul_isSolvable hx' hy')
  infer_instance

theorem isSolvable_gal_minpoly {x : E} (hx : x ∈ solvableByRad F E) :
    IsSolvable (minpoly F x).Gal := by
  induction hx using solvableByRad.induction with
  | mem y => rw [minpoly.eq_X_sub_C E]; infer_instance
  | add y z hy hz hy' hz' =>
    apply induction_step hy hz (add_mem hy hz) hy' hz' (add_mem ..) <;> apply subset_adjoin <;> simp
  | mul y z hy hz hy' hz' =>
    apply induction_step hy hz (mul_mem hy hz) hy' hz' (mul_mem ..) <;> apply subset_adjoin <;> simp
  | rad n y hn hy hy' => exact induction_rad (solvableByRad.rad_mem hn hy) hn hy'

@[deprecated (since := "2026-02-28")]
alias solvableByRad.isSolvable := isSolvable_gal_minpoly

/-- **Abel-Ruffini Theorem** (one direction): An irreducible polynomial with a `solvableByRad` root
has a solvable Galois group. -/
theorem isSolvable_gal_of_irreducible {x : E} (hx : x ∈ solvableByRad F E) {q : F[X]}
    (q_irred : Irreducible q) (q_aeval : aeval x q = 0) : IsSolvable q.Gal := by
  have : IsSolvable (q * C q.leadingCoeff⁻¹).Gal := by
    rw [minpoly.eq_of_irreducible q_irred q_aeval]
    exact isSolvable_gal_minpoly hx
  refine solvable_of_surjective (Gal.restrictDvd_surjective ⟨C q.leadingCoeff⁻¹, rfl⟩ ?_)
  aesop

@[deprecated (since := "2026-02-28")]
alias solvableByRad.isSolvable' := isSolvable_gal_of_irreducible
