/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Chris Hughes
-/
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Fintype.Inv
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Tactic.FieldSimp

/-!
# Integral domains

Assorted theorems about integral domains.

## Main theorems

* `isCyclic_of_subgroup_isDomain`: A finite subgroup of the units of an integral domain is cyclic.
* `Fintype.fieldOfDomain`: A finite integral domain is a field.

## Notes

Wedderburn's little theorem, which shows that all finite division rings are actually fields,
is in `Mathlib/RingTheory/LittleWedderburn.lean`.

## Tags

integral domain, finite integral domain, finite field
-/

section

open Finset Polynomial Function Nat

section CancelMonoidWithZero

-- There doesn't seem to be a better home for these right now
variable {M : Type*} [CancelMonoidWithZero M] [Finite M]

theorem mul_right_bijective_of_finite₀ {a : M} (ha : a ≠ 0) : Bijective fun b => a * b :=
  Finite.injective_iff_bijective.1 <| mul_right_injective₀ ha

theorem mul_left_bijective_of_finite₀ {a : M} (ha : a ≠ 0) : Bijective fun b => b * a :=
  Finite.injective_iff_bijective.1 <| mul_left_injective₀ ha

/-- Every finite nontrivial cancel_monoid_with_zero is a group_with_zero. -/
def Fintype.groupWithZeroOfCancel (M : Type*) [CancelMonoidWithZero M] [DecidableEq M] [Fintype M]
    [Nontrivial M] : GroupWithZero M :=
  { ‹Nontrivial M›,
    ‹CancelMonoidWithZero M› with
    inv := fun a => if h : a = 0 then 0 else Fintype.bijInv (mul_right_bijective_of_finite₀ h) 1
    mul_inv_cancel := fun a ha => by
      simp only [dif_neg ha]
      exact Fintype.rightInverse_bijInv _ _
    inv_zero := by simp }

theorem exists_eq_pow_of_mul_eq_pow_of_coprime {R : Type*} [CommSemiring R] [IsDomain R]
    [GCDMonoid R] [Subsingleton Rˣ] {a b c : R} {n : ℕ} (cp : IsCoprime a b) (h : a * b = c ^ n) :
    ∃ d : R, a = d ^ n := by
  refine exists_eq_pow_of_mul_eq_pow (isUnit_of_dvd_one ?_) h
  obtain ⟨x, y, hxy⟩ := cp
  rw [← hxy]
  exact  -- Porting note: added `GCDMonoid.` twice
    dvd_add (dvd_mul_of_dvd_right (GCDMonoid.gcd_dvd_left _ _) _)
      (dvd_mul_of_dvd_right (GCDMonoid.gcd_dvd_right _ _) _)

nonrec
theorem Finset.exists_eq_pow_of_mul_eq_pow_of_coprime {ι R : Type*} [CommSemiring R] [IsDomain R]
    [GCDMonoid R] [Subsingleton Rˣ] {n : ℕ} {c : R} {s : Finset ι} {f : ι → R}
    (h : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → IsCoprime (f i) (f j))
    (hprod : ∏ i ∈ s, f i = c ^ n) : ∀ i ∈ s, ∃ d : R, f i = d ^ n := by
  classical
    intro i hi
    rw [← insert_erase hi, prod_insert (notMem_erase i s)] at hprod
    refine
      exists_eq_pow_of_mul_eq_pow_of_coprime
        (IsCoprime.prod_right fun j hj => h i hi j (erase_subset i s hj) fun hij => ?_) hprod
    rw [hij] at hj
    exact (s.notMem_erase _) hj

end CancelMonoidWithZero

variable {R : Type*} {G : Type*}

section Ring

variable [Ring R] [IsDomain R] [Fintype R]

/-- Every finite domain is a division ring. More generally, they are fields; this can be found in
`Mathlib/RingTheory/LittleWedderburn.lean`. -/
def Fintype.divisionRingOfIsDomain (R : Type*) [Ring R] [IsDomain R] [DecidableEq R] [Fintype R] :
    DivisionRing R where
  __ := (‹Ring R›:) -- this also works without the `( :)`, but it's slightly slow
  __ := Fintype.groupWithZeroOfCancel R
  nnqsmul := _
  nnqsmul_def := fun _ _ => rfl
  qsmul := _
  qsmul_def := fun _ _ => rfl

/-- Every finite commutative domain is a field. More generally, commutativity is not required: this
can be found in `Mathlib/RingTheory/LittleWedderburn.lean`. -/
def Fintype.fieldOfDomain (R) [CommRing R] [IsDomain R] [DecidableEq R] [Fintype R] : Field R :=
  { Fintype.divisionRingOfIsDomain R, ‹CommRing R› with }

theorem Finite.isField_of_domain (R) [CommRing R] [IsDomain R] [Finite R] : IsField R := by
  cases nonempty_fintype R
  exact @Field.toIsField R (@Fintype.fieldOfDomain R _ _ (Classical.decEq R) _)

end Ring

variable [CommRing R] [IsDomain R] [Group G]

theorem card_nthRoots_subgroup_units [Fintype G] [DecidableEq G] (f : G →* R) (hf : Injective f)
    {n : ℕ} (hn : 0 < n) (g₀ : G) :
    #{g | g ^ n = g₀} ≤ Multiset.card (nthRoots n (f g₀)) := by
  haveI : DecidableEq R := Classical.decEq _
  calc
    _ ≤ #(nthRoots n (f g₀)).toFinset :=
      card_le_card_of_injOn f (by aesop (add safe unfold Set.MapsTo)) hf.injOn
    _ ≤ _ := (nthRoots n (f g₀)).toFinset_card_le

/-- A finite subgroup of the unit group of an integral domain is cyclic. -/
theorem isCyclic_of_subgroup_isDomain [Finite G] (f : G →* R) (hf : Injective f) : IsCyclic G := by
  classical
    cases nonempty_fintype G
    apply isCyclic_of_card_pow_eq_one_le
    intro n hn
    exact le_trans (card_nthRoots_subgroup_units f hf hn 1) (card_nthRoots n (f 1))

/-- The unit group of a finite integral domain is cyclic.

To support `ℤˣ` and other infinite monoids with finite groups of units, this requires only
`Finite Rˣ` rather than deducing it from `Finite R`. -/
instance [Finite Rˣ] : IsCyclic Rˣ :=
  isCyclic_of_subgroup_isDomain (Units.coeHom R) Units.val_injective

section

variable (S : Subgroup Rˣ) [Finite S]

/-- A finite subgroup of the units of an integral domain is cyclic. -/
instance subgroup_units_cyclic : IsCyclic S := by
  -- Porting note: the original proof used a `coe`, but I was not able to get it to work.
  apply isCyclic_of_subgroup_isDomain (R := R) (G := S) _ _
  · exact MonoidHom.mk (OneHom.mk (fun s => ↑s.val) rfl) (by simp)
  · exact Units.val_injective.comp Subtype.val_injective

end

section EuclideanDivision

namespace Polynomial

variable (K : Type*) [Field K] [Algebra R[X] K] [IsFractionRing R[X] K]

theorem div_eq_quo_add_rem_div (f : R[X]) {g : R[X]} (hg : g.Monic) :
    ∃ q r : R[X], r.degree < g.degree ∧
      (algebraMap R[X] K f) / (algebraMap R[X] K g) =
        algebraMap R[X] K q + (algebraMap R[X] K r) / (algebraMap R[X] K g) := by
  refine ⟨f /ₘ g, f %ₘ g, ?_, ?_⟩
  · exact degree_modByMonic_lt _ hg
  · have hg' : algebraMap R[X] K g ≠ 0 :=
      -- Porting note: the proof was `by exact_mod_cast Monic.ne_zero hg`
      (map_ne_zero_iff _ (IsFractionRing.injective R[X] K)).mpr (Monic.ne_zero hg)
    field_simp
    -- Porting note: `norm_cast` was here, but does nothing.
    rw [add_comm, ← map_mul, ← map_add, modByMonic_add_div f hg]

end Polynomial

end EuclideanDivision

variable [Fintype G]

/-- In an integral domain, a sum indexed by a nontrivial homomorphism from a finite group is zero.
-/
theorem sum_hom_units_eq_zero (f : G →* R) (hf : f ≠ 1) : ∑ g : G, f g = 0 := by
  classical
    obtain ⟨x, hx⟩ : ∃ x : MonoidHom.range f.toHomUnits,
        ∀ y : MonoidHom.range f.toHomUnits, y ∈ Submonoid.powers x :=
      IsCyclic.exists_monoid_generator
    have hx1 : x ≠ 1 := by
      rintro rfl
      apply hf
      ext g
      rw [MonoidHom.one_apply]
      obtain ⟨n, hn⟩ := hx ⟨f.toHomUnits g, g, rfl⟩
      rwa [Subtype.ext_iff, Units.ext_iff, Subtype.coe_mk, MonoidHom.coe_toHomUnits, one_pow,
        eq_comm] at hn
    replace hx1 : (x.val : R) - 1 ≠ 0 := -- Porting note: was `(x : R)`
      fun h => hx1 (Subtype.eq (Units.ext (sub_eq_zero.1 h)))
    let c := #{g | f.toHomUnits g = 1}
    calc
      ∑ g : G, f g = ∑ g : G, (f.toHomUnits g : R) := rfl
      _ = ∑ u ∈ univ.image f.toHomUnits, #{g | f.toHomUnits g = u} • (u : R) :=
        sum_comp ((↑) : Rˣ → R) f.toHomUnits
      _ = ∑ u ∈ univ.image f.toHomUnits, c • (u : R) :=
        (sum_congr rfl fun u hu => congr_arg₂ _ ?_ rfl)
      -- remaining goal 1, proven below
      -- Porting note: have to change `(b : R)` into `((b : Rˣ) : R)`
      _ = ∑ b : MonoidHom.range f.toHomUnits, c • ((b : Rˣ) : R) :=
        (Finset.sum_subtype _ (by simp) _)
      _ = c • ∑ b : MonoidHom.range f.toHomUnits, ((b : Rˣ) : R) := smul_sum.symm
      _ = c • (0 : R) := congr_arg₂ _ rfl ?_
      -- remaining goal 2, proven below
      _ = (0 : R) := smul_zero _
    · -- remaining goal 1
      show #{g : G | f.toHomUnits g = u} = c
      apply MonoidHom.card_fiber_eq_of_mem_range f.toHomUnits
      · simpa only [mem_image, mem_univ, true_and, Set.mem_range] using hu
      · exact ⟨1, f.toHomUnits.map_one⟩
    -- remaining goal 2
    show (∑ b : MonoidHom.range f.toHomUnits, ((b : Rˣ) : R)) = 0
    calc
      (∑ b : MonoidHom.range f.toHomUnits, ((b : Rˣ) : R))
        = ∑ n ∈ range (orderOf x), ((x : Rˣ) : R) ^ n :=
        Eq.symm <|
          sum_nbij (x ^ ·) (by simp only [mem_univ, forall_true_iff])
            (by simpa using pow_injOn_Iio_orderOf)
            (fun b _ => let ⟨n, hn⟩ := hx b
              ⟨n % orderOf x, mem_range.2 (Nat.mod_lt _ (orderOf_pos _)),
               -- Porting note: have to use `dsimp` to apply the function
               by dsimp at hn ⊢; rw [pow_mod_orderOf, hn]⟩)
            (by simp only [imp_true_iff, Subgroup.coe_pow,
                Units.val_pow_eq_pow_val])
      _ = 0 := ?_
    rw [← mul_left_inj' hx1, zero_mul, geom_sum_mul]
    norm_cast
    simp [pow_orderOf_eq_one]

/-- In an integral domain, a sum indexed by a homomorphism from a finite group is zero,
unless the homomorphism is trivial, in which case the sum is equal to the cardinality of the group.
-/
theorem sum_hom_units (f : G →* R) [Decidable (f = 1)] :
    ∑ g : G, f g = if f = 1 then Fintype.card G else 0 := by
  split_ifs with h
  · simp [h]
  · rw [cast_zero] -- Porting note: added
    exact sum_hom_units_eq_zero f h

end
