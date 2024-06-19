/-
Copyright (c) 2020 Thomas Browning and Patrick Lutz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning, Patrick Lutz
-/
import Mathlib.GroupTheory.Solvable
import Mathlib.FieldTheory.PolynomialGaloisGroup
import Mathlib.RingTheory.RootsOfUnity.Basic

#align_import field_theory.abel_ruffini from "leanprover-community/mathlib"@"e3f4be1fcb5376c4948d7f095bec45350bfb9d1a"

/-!
# The Abel-Ruffini Theorem

This file proves one direction of the Abel-Ruffini theorem, namely that if an element is solvable
by radicals, then its minimal polynomial has solvable Galois group.

## Main definitions

* `solvableByRad F E` : the intermediate field of solvable-by-radicals elements

## Main results

* the Abel-Ruffini Theorem `solvableByRad.isSolvable'` : An irreducible polynomial with a root
that is solvable by radicals has a solvable Galois group.
-/


noncomputable section

open scoped Classical Polynomial IntermediateField

open Polynomial IntermediateField

section AbelRuffini

variable {F : Type*} [Field F] {E : Type*} [Field E] [Algebra F E]

theorem gal_zero_isSolvable : IsSolvable (0 : F[X]).Gal := by infer_instance
#align gal_zero_is_solvable gal_zero_isSolvable

theorem gal_one_isSolvable : IsSolvable (1 : F[X]).Gal := by infer_instance
#align gal_one_is_solvable gal_one_isSolvable

theorem gal_C_isSolvable (x : F) : IsSolvable (C x).Gal := by infer_instance
set_option linter.uppercaseLean3 false in
#align gal_C_is_solvable gal_C_isSolvable

theorem gal_X_isSolvable : IsSolvable (X : F[X]).Gal := by infer_instance
set_option linter.uppercaseLean3 false in
#align gal_X_is_solvable gal_X_isSolvable

theorem gal_X_sub_C_isSolvable (x : F) : IsSolvable (X - C x).Gal := by infer_instance
set_option linter.uppercaseLean3 false in
#align gal_X_sub_C_is_solvable gal_X_sub_C_isSolvable

theorem gal_X_pow_isSolvable (n : ℕ) : IsSolvable (X ^ n : F[X]).Gal := by infer_instance
set_option linter.uppercaseLean3 false in
#align gal_X_pow_is_solvable gal_X_pow_isSolvable

theorem gal_mul_isSolvable {p q : F[X]} (_ : IsSolvable p.Gal) (_ : IsSolvable q.Gal) :
    IsSolvable (p * q).Gal :=
  solvable_of_solvable_injective (Gal.restrictProd_injective p q)
#align gal_mul_is_solvable gal_mul_isSolvable

theorem gal_prod_isSolvable {s : Multiset F[X]} (hs : ∀ p ∈ s, IsSolvable (Gal p)) :
    IsSolvable s.prod.Gal := by
  apply Multiset.induction_on' s
  · exact gal_one_isSolvable
  · intro p t hps _ ht
    rw [Multiset.insert_eq_cons, Multiset.prod_cons]
    exact gal_mul_isSolvable (hs p hps) ht
#align gal_prod_is_solvable gal_prod_isSolvable

theorem gal_isSolvable_of_splits {p q : F[X]}
    (_ : Fact (p.Splits (algebraMap F q.SplittingField))) (hq : IsSolvable q.Gal) :
    IsSolvable p.Gal :=
  haveI : IsSolvable (q.SplittingField ≃ₐ[F] q.SplittingField) := hq
  solvable_of_surjective (AlgEquiv.restrictNormalHom_surjective q.SplittingField)
#align gal_is_solvable_of_splits gal_isSolvable_of_splits

theorem gal_isSolvable_tower (p q : F[X]) (hpq : p.Splits (algebraMap F q.SplittingField))
    (hp : IsSolvable p.Gal) (hq : IsSolvable (q.map (algebraMap F p.SplittingField)).Gal) :
    IsSolvable q.Gal := by
  let K := p.SplittingField
  let L := q.SplittingField
  haveI : Fact (p.Splits (algebraMap F L)) := ⟨hpq⟩
  let ϕ : (L ≃ₐ[K] L) ≃* (q.map (algebraMap F K)).Gal :=
    (IsSplittingField.algEquiv L (q.map (algebraMap F K))).autCongr
  have ϕ_inj : Function.Injective ϕ.toMonoidHom := ϕ.injective
  haveI : IsSolvable (K ≃ₐ[F] K) := hp
  haveI : IsSolvable (L ≃ₐ[K] L) := solvable_of_solvable_injective ϕ_inj
  exact isSolvable_of_isScalarTower F p.SplittingField q.SplittingField
#align gal_is_solvable_tower gal_isSolvable_tower

section GalXPowSubC

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
  rw [σ.mul_apply, τ.mul_apply, hc, τ.map_pow, hd, σ.map_pow, hc, ← pow_mul, pow_mul']
set_option linter.uppercaseLean3 false in
#align gal_X_pow_sub_one_is_solvable gal_X_pow_sub_one_isSolvable

theorem gal_X_pow_sub_C_isSolvable_aux (n : ℕ) (a : F)
    (h : (X ^ n - 1 : F[X]).Splits (RingHom.id F)) : IsSolvable (X ^ n - C a).Gal := by
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
    RingHom.mem_range.mp (minpoly.mem_range_of_degree_eq_one F c (h.def.resolve_left hn'''
      (minpoly.irreducible ((SplittingField.instNormal (X ^ n - C a)).isIntegral c))
      (minpoly.dvd F c (by rwa [map_id, AlgHom.map_sub, sub_eq_zero, aeval_X_pow, aeval_one]))))
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
    have key : (σ b / b) ^ n = 1 := by rw [div_pow, ← σ.map_pow, hb, σ.commutes, div_self ha']
    obtain ⟨c, hc⟩ := mem_range key
    use c
    rw [hc, mul_div_cancel₀ (σ b) hb']
  obtain ⟨c, hc⟩ := key σ
  obtain ⟨d, hd⟩ := key τ
  rw [σ.mul_apply, τ.mul_apply, hc, τ.map_mul, τ.commutes, hd, σ.map_mul, σ.commutes, hc,
    mul_assoc, mul_assoc, mul_right_inj' hb', mul_comm]
set_option linter.uppercaseLean3 false in
#align gal_X_pow_sub_C_is_solvable_aux gal_X_pow_sub_C_isSolvable_aux

theorem splits_X_pow_sub_one_of_X_pow_sub_C {F : Type*} [Field F] {E : Type*} [Field E]
    (i : F →+* E) (n : ℕ) {a : F} (ha : a ≠ 0) (h : (X ^ n - C a).Splits i) :
    (X ^ n - 1 : F[X]).Splits i := by
  have ha' : i a ≠ 0 := mt ((injective_iff_map_eq_zero i).mp i.injective a) ha
  by_cases hn : n = 0
  · rw [hn, pow_zero, sub_self]
    exact splits_zero i
  have hn' : 0 < n := pos_iff_ne_zero.mpr hn
  have hn'' : (X ^ n - C a).degree ≠ 0 :=
    ne_of_eq_of_ne (degree_X_pow_sub_C hn' a) (mt WithBot.coe_eq_coe.mp hn)
  obtain ⟨b, hb⟩ := exists_root_of_splits i h hn''
  rw [eval₂_sub, eval₂_X_pow, eval₂_C, sub_eq_zero] at hb
  have hb' : b ≠ 0 := by
    intro hb'
    rw [hb', zero_pow hn] at hb
    exact ha' hb.symm
  let s := ((X ^ n - C a).map i).roots
  have hs : _ = _ * (s.map _).prod := eq_prod_roots_of_splits h
  rw [leadingCoeff_X_pow_sub_C hn', RingHom.map_one, C_1, one_mul] at hs
  have hs' : Multiset.card s = n := (natDegree_eq_card_roots h).symm.trans natDegree_X_pow_sub_C
  apply @splits_of_exists_multiset F E _ _ i (X ^ n - 1) (s.map fun c : E => c / b)
  rw [leadingCoeff_X_pow_sub_one hn', RingHom.map_one, C_1, one_mul, Multiset.map_map]
  have C_mul_C : C (i a⁻¹) * C (i a) = 1 := by
    rw [← C_mul, ← i.map_mul, inv_mul_cancel ha, i.map_one, C_1]
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
    -- Porting note: needed for `Multiset.map_const` to work
    show (fun (_ : E) => C b) = Function.const E (C b) by rfl,
    Multiset.map_const, Multiset.prod_replicate, hs', ← C_pow, hb, ← mul_assoc, C_mul_C, one_mul]
  rfl
set_option linter.uppercaseLean3 false in
#align splits_X_pow_sub_one_of_X_pow_sub_C splits_X_pow_sub_one_of_X_pow_sub_C

theorem gal_X_pow_sub_C_isSolvable (n : ℕ) (x : F) : IsSolvable (X ^ n - C x).Gal := by
  by_cases hx : x = 0
  · rw [hx, C_0, sub_zero]
    exact gal_X_pow_isSolvable n
  apply gal_isSolvable_tower (X ^ n - 1) (X ^ n - C x)
  · exact splits_X_pow_sub_one_of_X_pow_sub_C _ n hx (SplittingField.splits _)
  · exact gal_X_pow_sub_one_isSolvable n
  · rw [Polynomial.map_sub, Polynomial.map_pow, map_X, map_C]
    apply gal_X_pow_sub_C_isSolvable_aux
    have key := SplittingField.splits (X ^ n - 1 : F[X])
    rwa [← splits_id_iff_splits, Polynomial.map_sub, Polynomial.map_pow, map_X,
      Polynomial.map_one] at key
set_option linter.uppercaseLean3 false in
#align gal_X_pow_sub_C_is_solvable gal_X_pow_sub_C_isSolvable

end GalXPowSubC

variable (F)

/-- Inductive definition of solvable by radicals -/
inductive IsSolvableByRad : E → Prop
  | base (α : F) : IsSolvableByRad (algebraMap F E α)
  | add (α β : E) : IsSolvableByRad α → IsSolvableByRad β → IsSolvableByRad (α + β)
  | neg (α : E) : IsSolvableByRad α → IsSolvableByRad (-α)
  | mul (α β : E) : IsSolvableByRad α → IsSolvableByRad β → IsSolvableByRad (α * β)
  | inv (α : E) : IsSolvableByRad α → IsSolvableByRad α⁻¹
  | rad (α : E) (n : ℕ) (hn : n ≠ 0) : IsSolvableByRad (α ^ n) → IsSolvableByRad α
#align is_solvable_by_rad IsSolvableByRad

variable (E)

/-- The intermediate field of solvable-by-radicals elements -/
def solvableByRad : IntermediateField F E where
  carrier := IsSolvableByRad F
  zero_mem' := by
    change IsSolvableByRad F 0
    convert IsSolvableByRad.base (E := E) (0 : F); rw [RingHom.map_zero]
  add_mem' := by apply IsSolvableByRad.add
  one_mem' := by
    change IsSolvableByRad F 1
    convert IsSolvableByRad.base (E := E) (1 : F); rw [RingHom.map_one]
  mul_mem' := by apply IsSolvableByRad.mul
  inv_mem' := IsSolvableByRad.inv
  algebraMap_mem' := IsSolvableByRad.base
#align solvable_by_rad solvableByRad

namespace solvableByRad

variable {F} {E} {α : E}

theorem induction (P : solvableByRad F E → Prop)
    (base : ∀ α : F, P (algebraMap F (solvableByRad F E) α))
    (add : ∀ α β : solvableByRad F E, P α → P β → P (α + β))
    (neg : ∀ α : solvableByRad F E, P α → P (-α))
    (mul : ∀ α β : solvableByRad F E, P α → P β → P (α * β))
    (inv : ∀ α : solvableByRad F E, P α → P α⁻¹)
    (rad : ∀ α : solvableByRad F E, ∀ n : ℕ, n ≠ 0 → P (α ^ n) → P α) (α : solvableByRad F E) :
    P α := by
  revert α
  suffices ∀ α : E, IsSolvableByRad F α → ∃ β : solvableByRad F E, ↑β = α ∧ P β by
    intro α
    obtain ⟨α₀, hα₀, Pα⟩ := this α (Subtype.mem α)
    convert Pα
    exact Subtype.ext hα₀.symm
  apply IsSolvableByRad.rec
  · exact fun α => ⟨algebraMap F (solvableByRad F E) α, rfl, base α⟩
  · intro α β _ _ Pα Pβ
    obtain ⟨⟨α₀, hα₀, Pα⟩, β₀, hβ₀, Pβ⟩ := Pα, Pβ
    exact ⟨α₀ + β₀, by rw [← hα₀, ← hβ₀]; rfl, add α₀ β₀ Pα Pβ⟩
  · intro α _ Pα
    obtain ⟨α₀, hα₀, Pα⟩ := Pα
    exact ⟨-α₀, by rw [← hα₀]; rfl, neg α₀ Pα⟩
  · intro α β _ _ Pα Pβ
    obtain ⟨⟨α₀, hα₀, Pα⟩, β₀, hβ₀, Pβ⟩ := Pα, Pβ
    exact ⟨α₀ * β₀, by rw [← hα₀, ← hβ₀]; rfl, mul α₀ β₀ Pα Pβ⟩
  · intro α _ Pα
    obtain ⟨α₀, hα₀, Pα⟩ := Pα
    exact ⟨α₀⁻¹, by rw [← hα₀]; rfl, inv α₀ Pα⟩
  · intro α n hn hα Pα
    obtain ⟨α₀, hα₀, Pα⟩ := Pα
    refine ⟨⟨α, IsSolvableByRad.rad α n hn hα⟩, rfl, rad _ n hn ?_⟩
    convert Pα
    exact Subtype.ext (Eq.trans ((solvableByRad F E).coe_pow _ n) hα₀.symm)
#align solvable_by_rad.induction solvableByRad.induction

theorem isIntegral (α : solvableByRad F E) : IsIntegral F α := by
  revert α
  apply solvableByRad.induction
  · exact fun _ => isIntegral_algebraMap
  · exact fun _ _ => IsIntegral.add
  · exact fun _ => IsIntegral.neg
  · exact fun _ _ => IsIntegral.mul
  · intro α hα
    exact Subalgebra.inv_mem_of_algebraic (integralClosure F (solvableByRad F E))
      (show IsAlgebraic F ↑(⟨α, hα⟩ : integralClosure F (solvableByRad F E)) from hα.isAlgebraic)
  · intro α n hn hα
    obtain ⟨p, h1, h2⟩ := hα.isAlgebraic
    refine IsAlgebraic.isIntegral ⟨p.comp (X ^ n),
      ⟨fun h => h1 (leadingCoeff_eq_zero.mp ?_), by rw [aeval_comp, aeval_X_pow, h2]⟩⟩
    rwa [← leadingCoeff_eq_zero, leadingCoeff_comp, leadingCoeff_X_pow, one_pow, mul_one] at h
    rwa [natDegree_X_pow]
#align solvable_by_rad.is_integral solvableByRad.isIntegral

/-- The statement to be proved inductively -/
def P (α : solvableByRad F E) : Prop :=
  IsSolvable (minpoly F α).Gal
set_option linter.uppercaseLean3 false in
#align solvable_by_rad.P solvableByRad.P

/-- An auxiliary induction lemma, which is generalized by `solvableByRad.isSolvable`. -/
theorem induction3 {α : solvableByRad F E} {n : ℕ} (hn : n ≠ 0) (hα : P (α ^ n)) : P α := by
  let p := minpoly F (α ^ n)
  have hp : p.comp (X ^ n) ≠ 0 := by
    intro h
    cases' comp_eq_zero_iff.mp h with h' h'
    · exact minpoly.ne_zero (isIntegral (α ^ n)) h'
    · exact hn (by rw [← @natDegree_C F, ← h'.2, natDegree_X_pow])
  apply gal_isSolvable_of_splits
  · exact ⟨splits_of_splits_of_dvd _ hp (SplittingField.splits (p.comp (X ^ n)))
      (minpoly.dvd F α (by rw [aeval_comp, aeval_X_pow, minpoly.aeval]))⟩
  · refine gal_isSolvable_tower p (p.comp (X ^ n)) ?_ hα ?_
    · exact Gal.splits_in_splittingField_of_comp _ _ (by rwa [natDegree_X_pow])
    · obtain ⟨s, hs⟩ := (splits_iff_exists_multiset _).1 (SplittingField.splits p)
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
#align solvable_by_rad.induction3 solvableByRad.induction3

/-- An auxiliary induction lemma, which is generalized by `solvableByRad.isSolvable`. -/
theorem induction2 {α β γ : solvableByRad F E} (hγ : γ ∈ F⟮α, β⟯) (hα : P α) (hβ : P β) : P γ := by
  let p := minpoly F α
  let q := minpoly F β
  have hpq := Polynomial.splits_of_splits_mul _
    (mul_ne_zero (minpoly.ne_zero (isIntegral α)) (minpoly.ne_zero (isIntegral β)))
    (SplittingField.splits (p * q))
  let f : ↥F⟮α, β⟯ →ₐ[F] (p * q).SplittingField :=
    Classical.choice <| nonempty_algHom_adjoin_of_splits <| by
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      cases hx with rw [hx]
      | inl hx => exact ⟨isIntegral α, hpq.1⟩
      | inr hx => exact ⟨isIntegral β, hpq.2⟩
  have key : minpoly F γ = minpoly F (f ⟨γ, hγ⟩) := by
    refine minpoly.eq_of_irreducible_of_monic
      (minpoly.irreducible (isIntegral γ)) ?_ (minpoly.monic (isIntegral γ))
    suffices aeval (⟨γ, hγ⟩ : F⟮α, β⟯) (minpoly F γ) = 0 by
      rw [aeval_algHom_apply, this, AlgHom.map_zero]
    apply (algebraMap (↥F⟮α, β⟯) (solvableByRad F E)).injective
    simp only [map_zero, _root_.map_eq_zero]
    -- Porting note: end of the proof was `exact minpoly.aeval F γ`.
    apply Subtype.val_injective
    -- This used to be `simp`, but we need `erw` and `simp` after leanprover/lean4#2644
    erw [Polynomial.aeval_subalgebra_coe (minpoly F γ)]
    simp
  rw [P, key]
  refine gal_isSolvable_of_splits ⟨Normal.splits ?_ (f ⟨γ, hγ⟩)⟩ (gal_mul_isSolvable hα hβ)
  apply SplittingField.instNormal
#align solvable_by_rad.induction2 solvableByRad.induction2

/-- An auxiliary induction lemma, which is generalized by `solvableByRad.isSolvable`. -/
theorem induction1 {α β : solvableByRad F E} (hβ : β ∈ F⟮α⟯) (hα : P α) : P β :=
  induction2 (adjoin.mono F _ _ (ge_of_eq (Set.pair_eq_singleton α)) hβ) hα hα
#align solvable_by_rad.induction1 solvableByRad.induction1

theorem isSolvable (α : solvableByRad F E) : IsSolvable (minpoly F α).Gal := by
  revert α
  apply solvableByRad.induction
  · exact fun α => by rw [minpoly.eq_X_sub_C (solvableByRad F E)]; exact gal_X_sub_C_isSolvable α
  · exact fun α β => induction2 (add_mem (subset_adjoin F _ (Set.mem_insert α _))
      (subset_adjoin F _ (Set.mem_insert_of_mem α (Set.mem_singleton β))))
  · exact fun α => induction1 (neg_mem (mem_adjoin_simple_self F α))
  · exact fun α β => induction2 (mul_mem (subset_adjoin F _ (Set.mem_insert α _))
      (subset_adjoin F _ (Set.mem_insert_of_mem α (Set.mem_singleton β))))
  · exact fun α => induction1 (inv_mem (mem_adjoin_simple_self F α))
  · exact fun α n => induction3
#align solvable_by_rad.is_solvable solvableByRad.isSolvable

/-- **Abel-Ruffini Theorem** (one direction): An irreducible polynomial with an
`IsSolvableByRad` root has solvable Galois group -/
theorem isSolvable' {α : E} {q : F[X]} (q_irred : Irreducible q) (q_aeval : aeval α q = 0)
    (hα : IsSolvableByRad F α) : IsSolvable q.Gal := by
  have : _root_.IsSolvable (q * C q.leadingCoeff⁻¹).Gal := by
    rw [minpoly.eq_of_irreducible q_irred q_aeval, ←
      show minpoly F (⟨α, hα⟩ : solvableByRad F E) = minpoly F α from
        (minpoly.algebraMap_eq (RingHom.injective _) _).symm]
    exact isSolvable ⟨α, hα⟩
  refine solvable_of_surjective (Gal.restrictDvd_surjective ⟨C q.leadingCoeff⁻¹, rfl⟩ ?_)
  rw [mul_ne_zero_iff, Ne, Ne, C_eq_zero, inv_eq_zero]
  exact ⟨q_irred.ne_zero, leadingCoeff_ne_zero.mpr q_irred.ne_zero⟩
#align solvable_by_rad.is_solvable' solvableByRad.isSolvable'

end solvableByRad

end AbelRuffini
