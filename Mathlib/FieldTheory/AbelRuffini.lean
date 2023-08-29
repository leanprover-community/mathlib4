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

local macro_rules | `($x ^ $y) => `(HPow.hPow $x $y) -- Porting note: See issue lean4#2220

open scoped Classical Polynomial

open Polynomial IntermediateField

section AbelRuffini

variable {F : Type*} [Field F] {E : Type*} [Field E] [Algebra F E]

theorem gal_zero_isSolvable : IsSolvable (0 : F[X]).Gal := by infer_instance
                                                              -- 🎉 no goals
#align gal_zero_is_solvable gal_zero_isSolvable

theorem gal_one_isSolvable : IsSolvable (1 : F[X]).Gal := by infer_instance
                                                             -- 🎉 no goals
#align gal_one_is_solvable gal_one_isSolvable

theorem gal_C_isSolvable (x : F) : IsSolvable (C x).Gal := by infer_instance
                                                              -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align gal_C_is_solvable gal_C_isSolvable

theorem gal_X_isSolvable : IsSolvable (X : F[X]).Gal := by infer_instance
                                                           -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align gal_X_is_solvable gal_X_isSolvable

theorem gal_X_sub_C_isSolvable (x : F) : IsSolvable (X - C x).Gal := by infer_instance
                                                                        -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align gal_X_sub_C_is_solvable gal_X_sub_C_isSolvable

theorem gal_X_pow_isSolvable (n : ℕ) : IsSolvable (X ^ n : F[X]).Gal := by infer_instance
                                                                           -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align gal_X_pow_is_solvable gal_X_pow_isSolvable

theorem gal_mul_isSolvable {p q : F[X]} (_ : IsSolvable p.Gal) (_ : IsSolvable q.Gal) :
    IsSolvable (p * q).Gal :=
  solvable_of_solvable_injective (Gal.restrictProd_injective p q)
#align gal_mul_is_solvable gal_mul_isSolvable

theorem gal_prod_isSolvable {s : Multiset F[X]} (hs : ∀ p ∈ s, IsSolvable (Gal p)) :
    IsSolvable s.prod.Gal := by
  apply Multiset.induction_on' s
  -- ⊢ IsSolvable (Gal (Multiset.prod 0))
  · exact gal_one_isSolvable
    -- 🎉 no goals
  · intro p t hps _ ht
    -- ⊢ IsSolvable (Gal (Multiset.prod (insert p t)))
    rw [Multiset.insert_eq_cons, Multiset.prod_cons]
    -- ⊢ IsSolvable (Gal (p * Multiset.prod t))
    exact gal_mul_isSolvable (hs p hps) ht
    -- 🎉 no goals
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
  -- ⊢ IsSolvable (Gal q)
  let L := q.SplittingField
  -- ⊢ IsSolvable (Gal q)
  haveI : Fact (p.Splits (algebraMap F L)) := ⟨hpq⟩
  -- ⊢ IsSolvable (Gal q)
  let ϕ : (L ≃ₐ[K] L) ≃* (q.map (algebraMap F K)).Gal :=
    (IsSplittingField.algEquiv L (q.map (algebraMap F K))).autCongr
  have ϕ_inj : Function.Injective ϕ.toMonoidHom := ϕ.injective
  -- ⊢ IsSolvable (Gal q)
  haveI : IsSolvable (K ≃ₐ[F] K) := hp
  -- ⊢ IsSolvable (Gal q)
  haveI : IsSolvable (L ≃ₐ[K] L) := solvable_of_solvable_injective ϕ_inj
  -- ⊢ IsSolvable (Gal q)
  exact isSolvable_of_isScalarTower F p.SplittingField q.SplittingField
  -- 🎉 no goals
#align gal_is_solvable_tower gal_isSolvable_tower

section GalXPowSubC

theorem gal_X_pow_sub_one_isSolvable (n : ℕ) : IsSolvable (X ^ n - 1 : F[X]).Gal := by
  by_cases hn : n = 0
  -- ⊢ IsSolvable (Gal (X ^ n - 1))
  · rw [hn, pow_zero, sub_self]
    -- ⊢ IsSolvable (Gal 0)
    exact gal_zero_isSolvable
    -- 🎉 no goals
  have hn' : 0 < n := pos_iff_ne_zero.mpr hn
  -- ⊢ IsSolvable (Gal (X ^ n - 1))
  have hn'' : (X ^ n - 1 : F[X]) ≠ 0 := X_pow_sub_C_ne_zero hn' 1
  -- ⊢ IsSolvable (Gal (X ^ n - 1))
  apply isSolvable_of_comm
  -- ⊢ ∀ (a b : Gal (X ^ n - 1)), a * b = b * a
  intro σ τ
  -- ⊢ σ * τ = τ * σ
  ext a ha
  -- ⊢ ↑(σ * τ) a = ↑(τ * σ) a
  simp only [mem_rootSet_of_ne hn'', map_sub, aeval_X_pow, aeval_one, sub_eq_zero] at ha
  -- ⊢ ↑(σ * τ) a = ↑(τ * σ) a
  have key : ∀ σ : (X ^ n - 1 : F[X]).Gal, ∃ m : ℕ, σ a = a ^ m := by
    intro σ
    lift n to ℕ+ using hn'
    exact map_rootsOfUnity_eq_pow_self σ.toAlgHom (rootsOfUnity.mkOfPowEq a ha)
  obtain ⟨c, hc⟩ := key σ
  -- ⊢ ↑(σ * τ) a = ↑(τ * σ) a
  obtain ⟨d, hd⟩ := key τ
  -- ⊢ ↑(σ * τ) a = ↑(τ * σ) a
  rw [σ.mul_apply, τ.mul_apply, hc, τ.map_pow, hd, σ.map_pow, hc, ← pow_mul, pow_mul']
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align gal_X_pow_sub_one_is_solvable gal_X_pow_sub_one_isSolvable

set_option maxHeartbeats 300000 in
theorem gal_X_pow_sub_C_isSolvable_aux (n : ℕ) (a : F)
    (h : (X ^ n - 1 : F[X]).Splits (RingHom.id F)) : IsSolvable (X ^ n - C a).Gal := by
  by_cases ha : a = 0
  -- ⊢ IsSolvable (Gal (X ^ n - ↑C a))
  · rw [ha, C_0, sub_zero]
    -- ⊢ IsSolvable (Gal (X ^ n))
    exact gal_X_pow_isSolvable n
    -- 🎉 no goals
  have ha' : algebraMap F (X ^ n - C a).SplittingField a ≠ 0 :=
    mt ((injective_iff_map_eq_zero _).mp (RingHom.injective _) a) ha
  by_cases hn : n = 0
  -- ⊢ IsSolvable (Gal (X ^ n - ↑C a))
  · rw [hn, pow_zero, ← C_1, ← C_sub]
    -- ⊢ IsSolvable (Gal (↑C (1 - a)))
    exact gal_C_isSolvable (1 - a)
    -- 🎉 no goals
  have hn' : 0 < n := pos_iff_ne_zero.mpr hn
  -- ⊢ IsSolvable (Gal (X ^ n - ↑C a))
  have hn'' : X ^ n - C a ≠ 0 := X_pow_sub_C_ne_zero hn' a
  -- ⊢ IsSolvable (Gal (X ^ n - ↑C a))
  have hn''' : (X ^ n - 1 : F[X]) ≠ 0 := X_pow_sub_C_ne_zero hn' 1
  -- ⊢ IsSolvable (Gal (X ^ n - ↑C a))
  have mem_range : ∀ {c : (X ^ n - C a).SplittingField},
      (c ^ n = 1 → (∃ d, algebraMap F (X ^ n - C a).SplittingField d = c)) := fun {c} hc =>
    RingHom.mem_range.mp (minpoly.mem_range_of_degree_eq_one F c (h.def.resolve_left hn'''
      (minpoly.irreducible ((SplittingField.instNormal (X ^ n - C a)).isIntegral c))
      (minpoly.dvd F c (by rwa [map_id, AlgHom.map_sub, sub_eq_zero, aeval_X_pow, aeval_one]))))
  apply isSolvable_of_comm
  -- ⊢ ∀ (a_1 b : Gal (X ^ n - ↑C a)), a_1 * b = b * a_1
  intro σ τ
  -- ⊢ σ * τ = τ * σ
  ext b hb
  -- ⊢ ↑(σ * τ) b = ↑(τ * σ) b
  rw [mem_rootSet_of_ne hn'', map_sub, aeval_X_pow, aeval_C, sub_eq_zero] at hb
  -- ⊢ ↑(σ * τ) b = ↑(τ * σ) b
  have hb' : b ≠ 0 := by
    intro hb'
    rw [hb', zero_pow hn'] at hb
    exact ha' hb.symm
  have key : ∀ σ : (X ^ n - C a).Gal, ∃ c, σ b = b * algebraMap F _ c := by
    intro σ
    have key : (σ b / b) ^ n = 1 := by rw [div_pow, ← σ.map_pow, hb, σ.commutes, div_self ha']
    obtain ⟨c, hc⟩ := mem_range key
    use c
    rw [hc, mul_div_cancel' (σ b) hb']
  obtain ⟨c, hc⟩ := key σ
  -- ⊢ ↑(σ * τ) b = ↑(τ * σ) b
  obtain ⟨d, hd⟩ := key τ
  -- ⊢ ↑(σ * τ) b = ↑(τ * σ) b
  rw [σ.mul_apply, τ.mul_apply, hc, τ.map_mul, τ.commutes, hd, σ.map_mul, σ.commutes, hc,
    mul_assoc, mul_assoc, mul_right_inj' hb', mul_comm]
set_option linter.uppercaseLean3 false in
#align gal_X_pow_sub_C_is_solvable_aux gal_X_pow_sub_C_isSolvable_aux

set_option maxHeartbeats 300000 in
theorem splits_X_pow_sub_one_of_X_pow_sub_C {F : Type*} [Field F] {E : Type*} [Field E]
    (i : F →+* E) (n : ℕ) {a : F} (ha : a ≠ 0) (h : (X ^ n - C a).Splits i) :
    (X ^ n - 1 : F[X]).Splits i := by
  have ha' : i a ≠ 0 := mt ((injective_iff_map_eq_zero i).mp i.injective a) ha
  -- ⊢ Splits i (X ^ n - 1)
  by_cases hn : n = 0
  -- ⊢ Splits i (X ^ n - 1)
  · rw [hn, pow_zero, sub_self]
    -- ⊢ Splits i 0
    exact splits_zero i
    -- 🎉 no goals
  have hn' : 0 < n := pos_iff_ne_zero.mpr hn
  -- ⊢ Splits i (X ^ n - 1)
  have hn'' : (X ^ n - C a).degree ≠ 0 :=
    ne_of_eq_of_ne (degree_X_pow_sub_C hn' a) (mt WithBot.coe_eq_coe.mp hn)
  obtain ⟨b, hb⟩ := exists_root_of_splits i h hn''
  -- ⊢ Splits i (X ^ n - 1)
  rw [eval₂_sub, eval₂_X_pow, eval₂_C, sub_eq_zero] at hb
  -- ⊢ Splits i (X ^ n - 1)
  have hb' : b ≠ 0 := by
    intro hb'
    rw [hb', zero_pow hn'] at hb
    exact ha' hb.symm
  let s := ((X ^ n - C a).map i).roots
  -- ⊢ Splits i (X ^ n - 1)
  have hs : _ = _ * (s.map _).prod := eq_prod_roots_of_splits h
  -- ⊢ Splits i (X ^ n - 1)
  rw [leadingCoeff_X_pow_sub_C hn', RingHom.map_one, C_1, one_mul] at hs
  -- ⊢ Splits i (X ^ n - 1)
  have hs' : Multiset.card s = n := (natDegree_eq_card_roots h).symm.trans natDegree_X_pow_sub_C
  -- ⊢ Splits i (X ^ n - 1)
  apply @splits_of_exists_multiset F E _ _ i (X ^ n - 1) (s.map fun c : E => c / b)
  -- ⊢ Polynomial.map i (X ^ n - 1) = ↑C (↑i (leadingCoeff (X ^ n - 1))) * Multiset …
  rw [leadingCoeff_X_pow_sub_one hn', RingHom.map_one, C_1, one_mul, Multiset.map_map]
  -- ⊢ Polynomial.map i (X ^ n - 1) = Multiset.prod (Multiset.map ((fun a => X - ↑C …
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
    rw [sub_comp, X_comp, C_comp, mul_sub, ← C_mul, mul_div_cancel' c hb']
  rw [key1, hs, multiset_prod_comp, Multiset.map_map, key2, Multiset.prod_map_mul,
    -- Porting note: needed for `Multiset.map_const` to work
    show (fun (_ : E) => C b) = Function.const E (C b) by rfl,
    Multiset.map_const, Multiset.prod_replicate, hs', ← C_pow, hb, ← mul_assoc, C_mul_C, one_mul]
  rfl
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align splits_X_pow_sub_one_of_X_pow_sub_C splits_X_pow_sub_one_of_X_pow_sub_C

theorem gal_X_pow_sub_C_isSolvable (n : ℕ) (x : F) : IsSolvable (X ^ n - C x).Gal := by
  by_cases hx : x = 0
  -- ⊢ IsSolvable (Gal (X ^ n - ↑C x))
  · rw [hx, C_0, sub_zero]
    -- ⊢ IsSolvable (Gal (X ^ n))
    exact gal_X_pow_isSolvable n
    -- 🎉 no goals
  apply gal_isSolvable_tower (X ^ n - 1) (X ^ n - C x)
  · exact splits_X_pow_sub_one_of_X_pow_sub_C _ n hx (SplittingField.splits _)
    -- 🎉 no goals
  · exact gal_X_pow_sub_one_isSolvable n
    -- 🎉 no goals
  · rw [Polynomial.map_sub, Polynomial.map_pow, map_X, map_C]
    -- ⊢ IsSolvable (Gal (X ^ n - ↑C (↑(algebraMap F (SplittingField (X ^ n - 1))) x)))
    apply gal_X_pow_sub_C_isSolvable_aux
    -- ⊢ Splits (RingHom.id (SplittingField (X ^ n - 1))) (X ^ n - 1)
    have key := SplittingField.splits (X ^ n - 1 : F[X])
    -- ⊢ Splits (RingHom.id (SplittingField (X ^ n - 1))) (X ^ n - 1)
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
    -- ⊢ IsSolvableByRad F 0
    convert IsSolvableByRad.base (E := E) (0 : F); rw [RingHom.map_zero]
                 -- 🎉 no goals
    -- ⊢ 0 = ↑(algebraMap F E) 0
    -- ⊢ IsSolvableByRad F 1
                                                   -- 🎉 no goals
                 -- 🎉 no goals
    -- ⊢ 1 = ↑(algebraMap F E) 1
                                                   -- 🎉 no goals
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
  -- ⊢ ∀ (α : { x // x ∈ solvableByRad F E }), P α
  suffices ∀ α : E, IsSolvableByRad F α → ∃ β : solvableByRad F E, ↑β = α ∧ P β by
    intro α
    obtain ⟨α₀, hα₀, Pα⟩ := this α (Subtype.mem α)
    convert Pα
    exact Subtype.ext hα₀.symm
  apply IsSolvableByRad.rec
  · exact fun α => ⟨algebraMap F (solvableByRad F E) α, rfl, base α⟩
    -- 🎉 no goals
  · intro α β _ _ Pα Pβ
    -- ⊢ ∃ β_1, ↑β_1 = α + β ∧ P β_1
    obtain ⟨⟨α₀, hα₀, Pα⟩, β₀, hβ₀, Pβ⟩ := Pα, Pβ
    -- ⊢ ∃ β_1, ↑β_1 = α + β ∧ P β_1
    exact ⟨α₀ + β₀, by rw [← hα₀, ← hβ₀]; rfl, add α₀ β₀ Pα Pβ⟩
    -- 🎉 no goals
  · intro α _ Pα
    -- ⊢ ∃ β, ↑β = -α ∧ P β
    obtain ⟨α₀, hα₀, Pα⟩ := Pα
    -- ⊢ ∃ β, ↑β = -α ∧ P β
    exact ⟨-α₀, by rw [← hα₀]; rfl, neg α₀ Pα⟩
    -- 🎉 no goals
  · intro α β _ _ Pα Pβ
    -- ⊢ ∃ β_1, ↑β_1 = α * β ∧ P β_1
    obtain ⟨⟨α₀, hα₀, Pα⟩, β₀, hβ₀, Pβ⟩ := Pα, Pβ
    -- ⊢ ∃ β_1, ↑β_1 = α * β ∧ P β_1
    exact ⟨α₀ * β₀, by rw [← hα₀, ← hβ₀]; rfl, mul α₀ β₀ Pα Pβ⟩
    -- 🎉 no goals
  · intro α _ Pα
    -- ⊢ ∃ β, ↑β = α⁻¹ ∧ P β
    obtain ⟨α₀, hα₀, Pα⟩ := Pα
    -- ⊢ ∃ β, ↑β = α⁻¹ ∧ P β
    exact ⟨α₀⁻¹, by rw [← hα₀]; rfl, inv α₀ Pα⟩
    -- 🎉 no goals
  · intro α n hn hα Pα
    -- ⊢ ∃ β, ↑β = α ∧ P β
    obtain ⟨α₀, hα₀, Pα⟩ := Pα
    -- ⊢ ∃ β, ↑β = α ∧ P β
    refine' ⟨⟨α, IsSolvableByRad.rad α n hn hα⟩, rfl, rad _ n hn _⟩
    -- ⊢ P ({ val := α, property := (_ : IsSolvableByRad F α) } ^ n)
    convert Pα
    -- ⊢ { val := α, property := (_ : IsSolvableByRad F α) } ^ n = α₀
    exact Subtype.ext (Eq.trans ((solvableByRad F E).coe_pow _ n) hα₀.symm)
    -- 🎉 no goals
#align solvable_by_rad.induction solvableByRad.induction

theorem isIntegral (α : solvableByRad F E) : IsIntegral F α := by
  revert α
  -- ⊢ ∀ (α : { x // x ∈ solvableByRad F E }), IsIntegral F α
  apply solvableByRad.induction
  · exact fun _ => isIntegral_algebraMap
    -- 🎉 no goals
  · exact fun _ _ => isIntegral_add
    -- 🎉 no goals
  · exact fun _ => isIntegral_neg
    -- 🎉 no goals
  · exact fun _ _ => isIntegral_mul
    -- 🎉 no goals
  · intro α hα
    -- ⊢ IsIntegral F α⁻¹
    exact Subalgebra.inv_mem_of_algebraic (integralClosure F (solvableByRad F E))
      (show IsAlgebraic F ↑(⟨α, hα⟩ : integralClosure F (solvableByRad F E)) from
        isAlgebraic_iff_isIntegral.mpr hα)
  · intro α n hn hα
    -- ⊢ IsIntegral F α
    obtain ⟨p, h1, h2⟩ := isAlgebraic_iff_isIntegral.mpr hα
    -- ⊢ IsIntegral F α
    refine' isAlgebraic_iff_isIntegral.mp ⟨p.comp (X ^ n),
      ⟨fun h => h1 (leadingCoeff_eq_zero.mp _), by rw [aeval_comp, aeval_X_pow, h2]⟩⟩
    rwa [← leadingCoeff_eq_zero, leadingCoeff_comp, leadingCoeff_X_pow, one_pow, mul_one] at h
    -- ⊢ natDegree (X ^ n) ≠ 0
    rwa [natDegree_X_pow]
    -- 🎉 no goals
#align solvable_by_rad.is_integral solvableByRad.isIntegral

/-- The statement to be proved inductively -/
def P (α : solvableByRad F E) : Prop :=
  IsSolvable (minpoly F α).Gal
set_option linter.uppercaseLean3 false in
#align solvable_by_rad.P solvableByRad.P

set_option maxHeartbeats 500000 in
/-- An auxiliary induction lemma, which is generalized by `solvableByRad.isSolvable`. -/
theorem induction3 {α : solvableByRad F E} {n : ℕ} (hn : n ≠ 0) (hα : P (α ^ n)) : P α := by
  let p := minpoly F (α ^ n)
  -- ⊢ P α
  have hp : p.comp (X ^ n) ≠ 0 := by
    intro h
    cases' comp_eq_zero_iff.mp h with h' h'
    · exact minpoly.ne_zero (isIntegral (α ^ n)) h'
    · exact hn (by rw [← @natDegree_C F, ← h'.2, natDegree_X_pow])
  apply gal_isSolvable_of_splits
  · exact ⟨splits_of_splits_of_dvd _ hp (SplittingField.splits (p.comp (X ^ n)))
      (minpoly.dvd F α (by rw [aeval_comp, aeval_X_pow, minpoly.aeval]))⟩
  · refine' gal_isSolvable_tower p (p.comp (X ^ n)) _ hα _
    -- ⊢ Splits (algebraMap F (SplittingField (comp p (X ^ n)))) p
    · exact Gal.splits_in_splittingField_of_comp _ _ (by rwa [natDegree_X_pow])
      -- 🎉 no goals
    · obtain ⟨s, hs⟩ := (splits_iff_exists_multiset _).1 (SplittingField.splits p)
      -- ⊢ IsSolvable (Gal (Polynomial.map (algebraMap F (SplittingField p)) (comp p (X …
      rw [map_comp, Polynomial.map_pow, map_X, hs, mul_comp, C_comp]
      -- ⊢ IsSolvable (Gal (↑C (↑(algebraMap F (SplittingField p)) (leadingCoeff p)) *  …
      apply gal_mul_isSolvable (gal_C_isSolvable _)
      -- ⊢ IsSolvable (Gal (comp (Multiset.prod (Multiset.map (fun a => X - ↑C a) s)) ( …
      rw [multiset_prod_comp]
      -- ⊢ IsSolvable (Gal (Multiset.prod (Multiset.map (fun p_1 => comp p_1 (X ^ n)) ( …
      apply gal_prod_isSolvable
      -- ⊢ ∀ (p_1 : (SplittingField p)[X]), p_1 ∈ Multiset.map (fun p_2 => comp p_2 (X  …
      intro q hq
      -- ⊢ IsSolvable (Gal q)
      rw [Multiset.mem_map] at hq
      -- ⊢ IsSolvable (Gal q)
      obtain ⟨q, hq, rfl⟩ := hq
      -- ⊢ IsSolvable (Gal (comp q (X ^ n)))
      rw [Multiset.mem_map] at hq
      -- ⊢ IsSolvable (Gal (comp q (X ^ n)))
      obtain ⟨q, _, rfl⟩ := hq
      -- ⊢ IsSolvable (Gal (comp (X - ↑C q) (X ^ n)))
      rw [sub_comp, X_comp, C_comp]
      -- ⊢ IsSolvable (Gal (X ^ n - ↑C q))
      exact gal_X_pow_sub_C_isSolvable n q
      -- 🎉 no goals
#align solvable_by_rad.induction3 solvableByRad.induction3

/-- An auxiliary induction lemma, which is generalized by `solvableByRad.isSolvable`. -/
theorem induction2 {α β γ : solvableByRad F E} (hγ : γ ∈ F⟮α, β⟯) (hα : P α) (hβ : P β) : P γ := by
  let p := minpoly F α
  -- ⊢ P γ
  let q := minpoly F β
  -- ⊢ P γ
  have hpq := Polynomial.splits_of_splits_mul _
    (mul_ne_zero (minpoly.ne_zero (isIntegral α)) (minpoly.ne_zero (isIntegral β)))
    (SplittingField.splits (p * q))
  let f : ↥F⟮α, β⟯ →ₐ[F] (p * q).SplittingField := Classical.choice <| algHom_mk_adjoin_splits (by
    intro x hx
    cases' hx with hx hx
    rw [hx]
    exact ⟨isIntegral α, hpq.1⟩
    cases hx
    exact ⟨isIntegral β, hpq.2⟩)
  have key : minpoly F γ = minpoly F (f ⟨γ, hγ⟩) := by
    refine' minpoly.eq_of_irreducible_of_monic
      (minpoly.irreducible (isIntegral γ)) _ (minpoly.monic (isIntegral γ))
    suffices aeval (⟨γ, hγ⟩ : F⟮α, β⟯) (minpoly F γ) = 0 by
      rw [aeval_algHom_apply, this, AlgHom.map_zero]
    -- Porting note: this instance is needed for the following `apply`
    haveI := @IntermediateField.toAlgebra F (solvableByRad F E) _ _ _ F⟮α, β⟯
      (solvableByRad F E) _ (Algebra.id (solvableByRad F E))
    apply (algebraMap (↥F⟮α, β⟯) (solvableByRad F E)).injective
    simp only [map_zero, _root_.map_eq_zero]
    -- Porting note: end of the proof was `exact minpoly.aeval F γ`.
    apply Subtype.val_injective
    simp [Polynomial.aeval_subalgebra_coe (minpoly F γ)]
  rw [P, key]
  -- ⊢ IsSolvable (Gal (minpoly F (↑f { val := γ, property := hγ })))
  refine' gal_isSolvable_of_splits ⟨Normal.splits _ (f ⟨γ, hγ⟩)⟩ (gal_mul_isSolvable hα hβ)
  -- ⊢ Normal F ((fun x => SplittingField (p * q)) { val := γ, property := hγ })
  apply SplittingField.instNormal
  -- 🎉 no goals
#align solvable_by_rad.induction2 solvableByRad.induction2

/-- An auxiliary induction lemma, which is generalized by `solvableByRad.isSolvable`. -/
theorem induction1 {α β : solvableByRad F E} (hβ : β ∈ F⟮α⟯) (hα : P α) : P β :=
  induction2 (adjoin.mono F _ _ (ge_of_eq (Set.pair_eq_singleton α)) hβ) hα hα
#align solvable_by_rad.induction1 solvableByRad.induction1

theorem isSolvable (α : solvableByRad F E) : IsSolvable (minpoly F α).Gal := by
  revert α
  -- ⊢ ∀ (α : { x // x ∈ solvableByRad F E }), IsSolvable (Gal (minpoly F α))
  apply solvableByRad.induction
  · exact fun α => by rw [minpoly.eq_X_sub_C (solvableByRad F E)]; exact gal_X_sub_C_isSolvable α
    -- 🎉 no goals
  · exact fun α β => induction2 (add_mem (subset_adjoin F _ (Set.mem_insert α _))
      (subset_adjoin F _ (Set.mem_insert_of_mem α (Set.mem_singleton β))))
  · exact fun α => induction1 (neg_mem (mem_adjoin_simple_self F α))
    -- 🎉 no goals
  · exact fun α β => induction2 (mul_mem (subset_adjoin F _ (Set.mem_insert α _))
      (subset_adjoin F _ (Set.mem_insert_of_mem α (Set.mem_singleton β))))
  · exact fun α => induction1 (inv_mem (mem_adjoin_simple_self F α))
    -- 🎉 no goals
  · exact fun α n => induction3
    -- 🎉 no goals
#align solvable_by_rad.is_solvable solvableByRad.isSolvable

/-- **Abel-Ruffini Theorem** (one direction): An irreducible polynomial with an
`IsSolvableByRad` root has solvable Galois group -/
theorem isSolvable' {α : E} {q : F[X]} (q_irred : Irreducible q) (q_aeval : aeval α q = 0)
    (hα : IsSolvableByRad F α) : IsSolvable q.Gal := by
  have : _root_.IsSolvable (q * C q.leadingCoeff⁻¹).Gal := by
    rw [minpoly.eq_of_irreducible q_irred q_aeval, ←
      show minpoly F (⟨α, hα⟩ : solvableByRad F E) = minpoly F α from
        minpoly.eq_of_algebraMap_eq (RingHom.injective _) (isIntegral ⟨α, hα⟩) rfl]
    exact isSolvable ⟨α, hα⟩
  refine' solvable_of_surjective (Gal.restrictDvd_surjective ⟨C q.leadingCoeff⁻¹, rfl⟩ _)
  -- ⊢ q * ↑C (leadingCoeff q)⁻¹ ≠ 0
  rw [mul_ne_zero_iff, Ne, Ne, C_eq_zero, inv_eq_zero]
  -- ⊢ ¬q = 0 ∧ ¬leadingCoeff q = 0
  exact ⟨q_irred.ne_zero, leadingCoeff_ne_zero.mpr q_irred.ne_zero⟩
  -- 🎉 no goals
#align solvable_by_rad.is_solvable' solvableByRad.isSolvable'

end solvableByRad

end AbelRuffini
