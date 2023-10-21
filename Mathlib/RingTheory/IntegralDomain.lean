/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Chris Hughes
-/
import Mathlib.Data.Polynomial.RingDivision
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Algebra.GeomSum

#align_import ring_theory.integral_domain from "leanprover-community/mathlib"@"6e70e0d419bf686784937d64ed4bfde866ff229e"

/-!
# Integral domains

Assorted theorems about integral domains.

## Main theorems

* `isCyclic_of_subgroup_isDomain`: A finite subgroup of the units of an integral domain is cyclic.
* `Fintype.fieldOfDomain`: A finite integral domain is a field.

## TODO

Prove Wedderburn's little theorem, which shows that all finite division rings are actually fields.

## Tags

integral domain, finite integral domain, finite field
-/

section

open Finset Polynomial Function BigOperators Nat

section CancelMonoidWithZero

-- There doesn't seem to be a better home for these right now
variable {M : Type*} [CancelMonoidWithZero M] [Finite M]

theorem mul_right_bijective_of_finite₀ {a : M} (ha : a ≠ 0) : Bijective fun b => a * b :=
  Finite.injective_iff_bijective.1 <| mul_right_injective₀ ha
#align mul_right_bijective_of_finite₀ mul_right_bijective_of_finite₀

theorem mul_left_bijective_of_finite₀ {a : M} (ha : a ≠ 0) : Bijective fun b => b * a :=
  Finite.injective_iff_bijective.1 <| mul_left_injective₀ ha
#align mul_left_bijective_of_finite₀ mul_left_bijective_of_finite₀

/-- Every finite nontrivial cancel_monoid_with_zero is a group_with_zero. -/
def Fintype.groupWithZeroOfCancel (M : Type*) [CancelMonoidWithZero M] [DecidableEq M] [Fintype M]
    [Nontrivial M] : GroupWithZero M :=
  { ‹Nontrivial M›,
    ‹CancelMonoidWithZero M› with
    inv := fun a => if h : a = 0 then 0 else Fintype.bijInv (mul_right_bijective_of_finite₀ h) 1
    mul_inv_cancel := fun a ha => by
      simp only [Inv.inv, dif_neg ha]
      exact Fintype.rightInverse_bijInv _ _
    inv_zero := by simp [Inv.inv, dif_pos rfl] }
#align fintype.group_with_zero_of_cancel Fintype.groupWithZeroOfCancel

theorem exists_eq_pow_of_mul_eq_pow_of_coprime {R : Type*} [CommSemiring R] [IsDomain R]
    [GCDMonoid R] [Unique Rˣ] {a b c : R} {n : ℕ} (cp : IsCoprime a b) (h : a * b = c ^ n) :
    ∃ d : R, a = d ^ n := by
  refine' exists_eq_pow_of_mul_eq_pow (isUnit_of_dvd_one _) h
  obtain ⟨x, y, hxy⟩ := cp
  rw [← hxy]
  exact  -- porting note: added `GCDMonoid.` twice
    dvd_add (dvd_mul_of_dvd_right (GCDMonoid.gcd_dvd_left _ _) _)
      (dvd_mul_of_dvd_right (GCDMonoid.gcd_dvd_right _ _) _)
#align exists_eq_pow_of_mul_eq_pow_of_coprime exists_eq_pow_of_mul_eq_pow_of_coprime

nonrec
theorem Finset.exists_eq_pow_of_mul_eq_pow_of_coprime {ι R : Type*} [CommSemiring R] [IsDomain R]
    [GCDMonoid R] [Unique Rˣ] {n : ℕ} {c : R} {s : Finset ι} {f : ι → R}
    (h : ∀ (i) (_ : i ∈ s) (j) (_ : j ∈ s), i ≠ j → IsCoprime (f i) (f j))
    (hprod : ∏ i in s, f i = c ^ n) : ∀ i ∈ s, ∃ d : R, f i = d ^ n := by
  classical
    intro i hi
    rw [← insert_erase hi, prod_insert (not_mem_erase i s)] at hprod
    refine'
      exists_eq_pow_of_mul_eq_pow_of_coprime
        (IsCoprime.prod_right fun j hj => h i hi j (erase_subset i s hj) fun hij => _) hprod
    rw [hij] at hj
    exact (s.not_mem_erase _) hj
#align finset.exists_eq_pow_of_mul_eq_pow_of_coprime Finset.exists_eq_pow_of_mul_eq_pow_of_coprime

end CancelMonoidWithZero

variable {R : Type*} {G : Type*}

section Ring

variable [Ring R] [IsDomain R] [Fintype R]

/-- Every finite domain is a division ring.

TODO: Prove Wedderburn's little theorem,
which shows a finite domain is in fact commutative, hence a field. -/
def Fintype.divisionRingOfIsDomain (R : Type*) [Ring R] [IsDomain R] [DecidableEq R] [Fintype R] :
    DivisionRing R :=
  { show GroupWithZero R from Fintype.groupWithZeroOfCancel R, ‹Ring R› with }
#align fintype.division_ring_of_is_domain Fintype.divisionRingOfIsDomain

/-- Every finite commutative domain is a field.

TODO: Prove Wedderburn's little theorem, which shows a finite domain is automatically commutative,
dropping one assumption from this theorem. -/
def Fintype.fieldOfDomain (R) [CommRing R] [IsDomain R] [DecidableEq R] [Fintype R] : Field R :=
  { Fintype.groupWithZeroOfCancel R, ‹CommRing R› with }
#align fintype.field_of_domain Fintype.fieldOfDomain

theorem Finite.isField_of_domain (R) [CommRing R] [IsDomain R] [Finite R] : IsField R := by
  cases nonempty_fintype R
  exact @Field.toIsField R (@Fintype.fieldOfDomain R _ _ (Classical.decEq R) _)
#align finite.is_field_of_domain Finite.isField_of_domain

end Ring

variable [CommRing R] [IsDomain R] [Group G]

-- porting note: Finset doesn't seem to have `{g ∈ univ | g^n = g₀}` notation anymore,
-- so we have to use `Finset.filter` instead
theorem card_nthRoots_subgroup_units [Fintype G] [DecidableEq G] (f : G →* R) (hf : Injective f)
    {n : ℕ} (hn : 0 < n) (g₀ : G) :
    Finset.card (Finset.univ.filter (fun g ↦ g^n = g₀)) ≤ Multiset.card (nthRoots n (f g₀)) := by
  haveI : DecidableEq R := Classical.decEq _
  refine' le_trans _ (nthRoots n (f g₀)).toFinset_card_le
  apply card_le_card_of_inj_on f
  · intro g hg
    rw [mem_filter] at hg
    rw [Multiset.mem_toFinset, mem_nthRoots hn, ← f.map_pow, hg.2]
  · intros
    apply hf
    assumption
#align card_nth_roots_subgroup_units card_nthRoots_subgroup_units

/-- A finite subgroup of the unit group of an integral domain is cyclic. -/
theorem isCyclic_of_subgroup_isDomain [Finite G] (f : G →* R) (hf : Injective f) : IsCyclic G := by
  classical
    cases nonempty_fintype G
    apply isCyclic_of_card_pow_eq_one_le
    intro n hn
    exact le_trans (card_nthRoots_subgroup_units f hf hn 1) (card_nthRoots n (f 1))
#align is_cyclic_of_subgroup_is_domain isCyclic_of_subgroup_isDomain

/-- The unit group of a finite integral domain is cyclic.

To support `ℤˣ` and other infinite monoids with finite groups of units, this requires only
`Finite Rˣ` rather than deducing it from `Finite R`. -/
instance [Finite Rˣ] : IsCyclic Rˣ :=
  isCyclic_of_subgroup_isDomain (Units.coeHom R) <| Units.ext

section

variable (S : Subgroup Rˣ) [Finite S]

/-- A finite subgroup of the units of an integral domain is cyclic. -/
instance subgroup_units_cyclic : IsCyclic S := by
  -- porting note: the original proof used a `coe`, but I was not able to get it to work.
  apply isCyclic_of_subgroup_isDomain (R := R) (G := S) _ _
  · exact MonoidHom.mk (OneHom.mk (fun s => ↑s.val) rfl) (by simp)
  · exact Units.ext.comp Subtype.val_injective
#align subgroup_units_cyclic subgroup_units_cyclic

end

section EuclideanDivision

namespace Polynomial

open Polynomial

variable (K : Type) [Field K] [Algebra R[X] K] [IsFractionRing R[X] K]

theorem div_eq_quo_add_rem_div (f : R[X]) {g : R[X]} (hg : g.Monic) :
    ∃ q r : R[X], r.degree < g.degree ∧
      (algebraMap R[X] K f) / (algebraMap R[X] K g) =
        algebraMap R[X] K q + (algebraMap R[X] K r) / (algebraMap R[X] K g) := by
  refine' ⟨f /ₘ g, f %ₘ g, _, _⟩
  · exact degree_modByMonic_lt _ hg
  · have hg' : algebraMap R[X] K g ≠ 0 :=
      -- porting note: the proof was `by exact_mod_cast Monic.ne_zero hg`
      (map_ne_zero_iff _ (IsFractionRing.injective R[X] K)).mpr (Monic.ne_zero hg)
    field_simp [hg']
    -- porting note: `norm_cast` was here, but does nothing.
    rw [add_comm, mul_comm, ← map_mul, ← map_add, modByMonic_add_div f hg]

#align polynomial.div_eq_quo_add_rem_div Polynomial.div_eq_quo_add_rem_div

end Polynomial

end EuclideanDivision

variable [Fintype G]

theorem card_fiber_eq_of_mem_range {H : Type*} [Group H] [DecidableEq H] (f : G →* H) {x y : H}
    (hx : x ∈ Set.range f) (hy : y ∈ Set.range f) :
    -- porting note: the `filter` had an index `ₓ` that I removed.
    (univ.filter fun g => f g = x).card = (univ.filter fun g => f g = y).card := by
  rcases hx with ⟨x, rfl⟩
  rcases hy with ⟨y, rfl⟩
  refine' card_congr (fun g _ => g * x⁻¹ * y) _ _ fun g hg => ⟨g * y⁻¹ * x, _⟩
  · simp (config := { contextual := true }) only [*, mem_filter, one_mul, MonoidHom.map_mul,
      mem_univ, mul_right_inv, eq_self_iff_true, MonoidHom.map_mul_inv, and_self_iff,
      forall_true_iff]
    -- porting note: added the following `simp`
    simp only [true_and, map_inv, mul_right_inv, one_mul, and_self, implies_true, forall_const]
  · simp only [mul_left_inj, imp_self, forall₂_true_iff]
  · simp only [true_and_iff, mem_filter, mem_univ] at hg
    simp only [hg, mem_filter, one_mul, MonoidHom.map_mul, mem_univ, mul_right_inv,
      eq_self_iff_true, exists_prop_of_true, MonoidHom.map_mul_inv, and_self_iff,
      mul_inv_cancel_right, inv_mul_cancel_right]
    -- porting note: added the next line.  It is weird!
    simp only [map_inv, mul_right_inv, one_mul, and_self, exists_prop]
#align card_fiber_eq_of_mem_range card_fiber_eq_of_mem_range

/-- In an integral domain, a sum indexed by a nontrivial homomorphism from a finite group is zero.
-/
theorem sum_hom_units_eq_zero (f : G →* R) (hf : f ≠ 1) : ∑ g : G, f g = 0 := by
  classical
    obtain ⟨x, hx⟩ :
      ∃ x : MonoidHom.range f.toHomUnits,
        ∀ y : MonoidHom.range f.toHomUnits, y ∈ Submonoid.powers x
    exact IsCyclic.exists_monoid_generator
    have hx1 : x ≠ 1 := by
      rintro rfl
      apply hf
      ext g
      rw [MonoidHom.one_apply]
      cases' hx ⟨f.toHomUnits g, g, rfl⟩ with n hn
      rwa [Subtype.ext_iff, Units.ext_iff, Subtype.coe_mk, MonoidHom.coe_toHomUnits, one_pow,
        eq_comm] at hn
    replace hx1 : (x.val : R) - 1 ≠ 0  -- porting note: was `(x : R)`
    exact fun h => hx1 (Subtype.eq (Units.ext (sub_eq_zero.1 h)))
    let c := (univ.filter fun g => f.toHomUnits g = 1).card
    calc
      ∑ g : G, f g = ∑ g : G, (f.toHomUnits g : R) := rfl
      _ = ∑ u : Rˣ in univ.image f.toHomUnits,
            (univ.filter fun g => f.toHomUnits g = u).card • (u : R) :=
        (sum_comp ((↑) : Rˣ → R) f.toHomUnits)
      _ = ∑ u : Rˣ in univ.image f.toHomUnits, c • (u : R) :=
        (sum_congr rfl fun u hu => congr_arg₂ _ ?_ rfl)
      -- remaining goal 1, proven below
      -- Porting note: have to change `(b : R)` into `((b : Rˣ) : R)`
      _ = ∑ b : MonoidHom.range f.toHomUnits, c • ((b : Rˣ) : R) :=
        (Finset.sum_subtype _ (by simp) _)
      _ = c • ∑ b : MonoidHom.range f.toHomUnits, ((b : Rˣ) : R) := smul_sum.symm
      _ = c • (0 : R) := (congr_arg₂ _ rfl ?_)
      -- remaining goal 2, proven below
      _ = (0 : R) := smul_zero _
    · -- remaining goal 1
      show (univ.filter fun g : G => f.toHomUnits g = u).card = c
      apply card_fiber_eq_of_mem_range f.toHomUnits
      · simpa only [mem_image, mem_univ, true_and, Set.mem_range] using hu
      · exact ⟨1, f.toHomUnits.map_one⟩
    -- remaining goal 2
    show (∑ b : MonoidHom.range f.toHomUnits, ((b : Rˣ) : R)) = 0
    calc
      (∑ b : MonoidHom.range f.toHomUnits, ((b : Rˣ) : R))
        = ∑ n in range (orderOf x), ((x : Rˣ) : R) ^ n :=
        Eq.symm <|
          sum_bij (fun n _ => x ^ n) (by simp only [mem_univ, forall_true_iff])
            (by simp only [imp_true_iff, eq_self_iff_true, Subgroup.coe_pow,
                Units.val_pow_eq_pow_val])
            (fun m n hm hn =>
              pow_injective_of_lt_orderOf _ (by simpa only [mem_range] using hm)
                (by simpa only [mem_range] using hn))
            (fun b _ => let ⟨n, hn⟩ := hx b
              ⟨n % orderOf x, mem_range.2 (Nat.mod_lt _ (orderOf_pos _)),
               -- Porting note: have to use `dsimp` to apply the function
               by dsimp at hn ⊢; rw [← pow_eq_mod_orderOf, hn]⟩)
      _ = 0 := ?_

    rw [← mul_left_inj' hx1, zero_mul, geom_sum_mul]
    norm_cast
    simp [pow_orderOf_eq_one]
#align sum_hom_units_eq_zero sum_hom_units_eq_zero

/-- In an integral domain, a sum indexed by a homomorphism from a finite group is zero,
unless the homomorphism is trivial, in which case the sum is equal to the cardinality of the group.
-/
theorem sum_hom_units (f : G →* R) [Decidable (f = 1)] :
    ∑ g : G, f g = if f = 1 then Fintype.card G else 0 := by
  split_ifs with h
  · simp [h, card_univ]
  · rw [cast_zero] -- porting note: added
    exact sum_hom_units_eq_zero f h
#align sum_hom_units sum_hom_units

end
