/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
import Mathlib.RingTheory.Algebraic
import Mathlib.RingTheory.Localization.AtPrime
import Mathlib.RingTheory.Localization.Integral

#align_import ring_theory.ideal.over from "leanprover-community/mathlib"@"198cb64d5c961e1a8d0d3e219feb7058d5353861"

/-!
# Ideals over/under ideals

This file concerns ideals lying over other ideals.
Let `f : R →+* S` be a ring homomorphism (typically a ring extension), `I` an ideal of `R` and
`J` an ideal of `S`. We say `J` lies over `I` (and `I` under `J`) if `I` is the `f`-preimage of `J`.
This is expressed here by writing `I = J.comap f`.

## Implementation notes

The proofs of the `comap_ne_bot` and `comap_lt_comap` families use an approach
specific for their situation: we construct an element in `I.comap f` from the
coefficients of a minimal polynomial.
Once mathlib has more material on the localization at a prime ideal, the results
can be proven using more general going-up/going-down theory.
-/


variable {R : Type*} [CommRing R]

namespace Ideal

open Polynomial

open Polynomial

open Submodule

section CommRing

variable {S : Type*} [CommRing S] {f : R →+* S} {I J : Ideal S}

theorem coeff_zero_mem_comap_of_root_mem_of_eval_mem {r : S} (hr : r ∈ I) {p : R[X]}
    (hp : p.eval₂ f r ∈ I) : p.coeff 0 ∈ I.comap f := by
  rw [← p.divX_mul_X_add, eval₂_add, eval₂_C, eval₂_mul, eval₂_X] at hp
  refine mem_comap.mpr ((I.add_mem_iff_right ?_).mp hp)
  exact I.mul_mem_left _ hr
#align ideal.coeff_zero_mem_comap_of_root_mem_of_eval_mem Ideal.coeff_zero_mem_comap_of_root_mem_of_eval_mem

theorem coeff_zero_mem_comap_of_root_mem {r : S} (hr : r ∈ I) {p : R[X]} (hp : p.eval₂ f r = 0) :
    p.coeff 0 ∈ I.comap f :=
  coeff_zero_mem_comap_of_root_mem_of_eval_mem hr (hp.symm ▸ I.zero_mem)
#align ideal.coeff_zero_mem_comap_of_root_mem Ideal.coeff_zero_mem_comap_of_root_mem

theorem exists_coeff_ne_zero_mem_comap_of_non_zero_divisor_root_mem {r : S}
    (r_non_zero_divisor : ∀ {x}, x * r = 0 → x = 0) (hr : r ∈ I) {p : R[X]} :
    p ≠ 0 → p.eval₂ f r = 0 → ∃ i, p.coeff i ≠ 0 ∧ p.coeff i ∈ I.comap f := by
  refine p.recOnHorner ?_ ?_ ?_
  · intro h
    contradiction
  · intro p a coeff_eq_zero a_ne_zero _ _ hp
    refine ⟨0, ?_, coeff_zero_mem_comap_of_root_mem hr hp⟩
    simp [coeff_eq_zero, a_ne_zero]
  · intro p p_nonzero ih _ hp
    rw [eval₂_mul, eval₂_X] at hp
    obtain ⟨i, hi, mem⟩ := ih p_nonzero (r_non_zero_divisor hp)
    refine ⟨i + 1, ?_, ?_⟩
    · simp [hi, mem]
    · simpa [hi] using mem
#align ideal.exists_coeff_ne_zero_mem_comap_of_non_zero_divisor_root_mem Ideal.exists_coeff_ne_zero_mem_comap_of_non_zero_divisor_root_mem

/-- Let `P` be an ideal in `R[x]`.  The map
`R[x]/P → (R / (P ∩ R))[x] / (P / (P ∩ R))`
is injective.
-/
theorem injective_quotient_le_comap_map (P : Ideal R[X]) :
    Function.Injective <|
      Ideal.quotientMap
        (Ideal.map (Polynomial.mapRingHom (Quotient.mk (P.comap (C : R →+* R[X])))) P)
        (Polynomial.mapRingHom (Ideal.Quotient.mk (P.comap (C : R →+* R[X]))))
        le_comap_map := by
  refine quotientMap_injective' (le_of_eq ?_)
  rw [comap_map_of_surjective (mapRingHom (Ideal.Quotient.mk (P.comap (C : R →+* R[X]))))
      (map_surjective (Ideal.Quotient.mk (P.comap (C : R →+* R[X]))) Ideal.Quotient.mk_surjective)]
  refine le_antisymm (sup_le le_rfl ?_) (le_sup_of_le_left le_rfl)
  refine fun p hp =>
    polynomial_mem_ideal_of_coeff_mem_ideal P p fun n => Ideal.Quotient.eq_zero_iff_mem.mp ?_
  simpa only [coeff_map, coe_mapRingHom] using ext_iff.mp (Ideal.mem_bot.mp (mem_comap.mp hp)) n
#align ideal.injective_quotient_le_comap_map Ideal.injective_quotient_le_comap_map

/-- The identity in this lemma asserts that the "obvious" square
```
    R    → (R / (P ∩ R))
    ↓          ↓
R[x] / P → (R / (P ∩ R))[x] / (P / (P ∩ R))
```
commutes.  It is used, for instance, in the proof of `quotient_mk_comp_C_is_integral_of_jacobson`,
in the file `RingTheory.Jacobson`.
-/
theorem quotient_mk_maps_eq (P : Ideal R[X]) :
    ((Quotient.mk (map (mapRingHom (Quotient.mk (P.comap (C : R →+* R[X])))) P)).comp C).comp
        (Quotient.mk (P.comap (C : R →+* R[X]))) =
      (Ideal.quotientMap (map (mapRingHom (Quotient.mk (P.comap (C : R →+* R[X])))) P)
            (mapRingHom (Quotient.mk (P.comap (C : R →+* R[X])))) le_comap_map).comp
        ((Quotient.mk P).comp C) := by
  refine RingHom.ext fun x => ?_
  repeat' rw [RingHom.coe_comp, Function.comp_apply]
  rw [quotientMap_mk, coe_mapRingHom, map_C]
#align ideal.quotient_mk_maps_eq Ideal.quotient_mk_maps_eq

/-- This technical lemma asserts the existence of a polynomial `p` in an ideal `P ⊂ R[x]`
that is non-zero in the quotient `R / (P ∩ R) [x]`.  The assumptions are equivalent to
`P ≠ 0` and `P ∩ R = (0)`.
-/
theorem exists_nonzero_mem_of_ne_bot {P : Ideal R[X]} (Pb : P ≠ ⊥) (hP : ∀ x : R, C x ∈ P → x = 0) :
    ∃ p : R[X], p ∈ P ∧ Polynomial.map (Quotient.mk (P.comap (C : R →+* R[X]))) p ≠ 0 := by
  obtain ⟨m, hm⟩ := Submodule.nonzero_mem_of_bot_lt (bot_lt_iff_ne_bot.mpr Pb)
  refine ⟨m, Submodule.coe_mem m, fun pp0 => hm (Submodule.coe_eq_zero.mp ?_)⟩
  refine
    (injective_iff_map_eq_zero (Polynomial.mapRingHom (Ideal.Quotient.mk
      (P.comap (C : R →+* R[X]))))).mp
      ?_ _ pp0
  refine map_injective _ ((Ideal.Quotient.mk (P.comap C)).injective_iff_ker_eq_bot.mpr ?_)
  rw [mk_ker]
  exact (Submodule.eq_bot_iff _).mpr fun x hx => hP x (mem_comap.mp hx)
#align ideal.exists_nonzero_mem_of_ne_bot Ideal.exists_nonzero_mem_of_ne_bot

variable {p : Ideal R} {P : Ideal S}

/-- If there is an injective map `R/p → S/P` such that following diagram commutes:
```
R   → S
↓     ↓
R/p → S/P
```
then `P` lies over `p`.
-/
theorem comap_eq_of_scalar_tower_quotient [Algebra R S] [Algebra (R ⧸ p) (S ⧸ P)]
    [IsScalarTower R (R ⧸ p) (S ⧸ P)] (h : Function.Injective (algebraMap (R ⧸ p) (S ⧸ P))) :
    comap (algebraMap R S) P = p := by
  ext x
  rw [mem_comap, ← Quotient.eq_zero_iff_mem, ← Quotient.eq_zero_iff_mem, Quotient.mk_algebraMap,
    IsScalarTower.algebraMap_apply R (R ⧸ p) (S ⧸ P), Quotient.algebraMap_eq]
  constructor
  · intro hx
    exact (injective_iff_map_eq_zero (algebraMap (R ⧸ p) (S ⧸ P))).mp h _ hx
  · intro hx
    rw [hx, RingHom.map_zero]
#align ideal.comap_eq_of_scalar_tower_quotient Ideal.comap_eq_of_scalar_tower_quotient

/-- If `P` lies over `p`, then `R / p` has a canonical map to `S / P`. -/
def Quotient.algebraQuotientOfLEComap (h : p ≤ comap f P) : Algebra (R ⧸ p) (S ⧸ P) :=
  RingHom.toAlgebra <| quotientMap _ f h
#align ideal.quotient.algebra_quotient_of_le_comap Ideal.Quotient.algebraQuotientOfLEComap

/-- `R / p` has a canonical map to `S / pS`. -/
instance Quotient.algebraQuotientMapQuotient : Algebra (R ⧸ p) (S ⧸ map f p) :=
  Ideal.Quotient.algebraQuotientOfLEComap le_comap_map
#align ideal.quotient.algebra_quotient_map_quotient Ideal.Quotient.algebraQuotientMapQuotient

@[simp]
theorem Quotient.algebraMap_quotient_map_quotient (x : R) :
    algebraMap (R ⧸ p) (S ⧸ map f p) (Ideal.Quotient.mk p x) =
    Ideal.Quotient.mk (map f p) (f x) :=
  rfl
#align ideal.quotient.algebra_map_quotient_map_quotient Ideal.Quotient.algebraMap_quotient_map_quotient

@[simp]
theorem Quotient.mk_smul_mk_quotient_map_quotient (x : R) (y : S) :
    Quotient.mk p x • Quotient.mk (map f p) y = Quotient.mk (map f p) (f x * y) :=
  rfl
#align ideal.quotient.mk_smul_mk_quotient_map_quotient Ideal.Quotient.mk_smul_mk_quotient_map_quotient

instance Quotient.tower_quotient_map_quotient [Algebra R S] :
    IsScalarTower R (R ⧸ p) (S ⧸ map (algebraMap R S) p) :=
  IsScalarTower.of_algebraMap_eq fun x => by
    rw [Quotient.algebraMap_eq, Quotient.algebraMap_quotient_map_quotient,
      Quotient.mk_algebraMap]
#align ideal.quotient.tower_quotient_map_quotient Ideal.Quotient.tower_quotient_map_quotient

instance QuotientMapQuotient.isNoetherian [Algebra R S] [IsNoetherian R S] (I : Ideal R) :
    IsNoetherian (R ⧸ I) (S ⧸ Ideal.map (algebraMap R S) I) :=
  isNoetherian_of_tower R <|
    isNoetherian_of_surjective S (Ideal.Quotient.mkₐ R _).toLinearMap <|
      LinearMap.range_eq_top.mpr Ideal.Quotient.mk_surjective
#align ideal.quotient_map_quotient.is_noetherian Ideal.QuotientMapQuotient.isNoetherian

end CommRing

section IsDomain

variable {S : Type*} [CommRing S] {f : R →+* S} {I J : Ideal S}

theorem exists_coeff_ne_zero_mem_comap_of_root_mem [IsDomain S] {r : S} (r_ne_zero : r ≠ 0)
    (hr : r ∈ I) {p : R[X]} :
    p ≠ 0 → p.eval₂ f r = 0 → ∃ i, p.coeff i ≠ 0 ∧ p.coeff i ∈ I.comap f :=
  exists_coeff_ne_zero_mem_comap_of_non_zero_divisor_root_mem
    (fun {_} h => Or.resolve_right (mul_eq_zero.mp h) r_ne_zero) hr
#align ideal.exists_coeff_ne_zero_mem_comap_of_root_mem Ideal.exists_coeff_ne_zero_mem_comap_of_root_mem

theorem exists_coeff_mem_comap_sdiff_comap_of_root_mem_sdiff [IsPrime I] (hIJ : I ≤ J) {r : S}
    (hr : r ∈ (J : Set S) \ I) {p : R[X]} (p_ne_zero : p.map (Quotient.mk (I.comap f)) ≠ 0)
    (hpI : p.eval₂ f r ∈ I) : ∃ i, p.coeff i ∈ (J.comap f : Set R) \ I.comap f := by
  obtain ⟨hrJ, hrI⟩ := hr
  have rbar_ne_zero : Ideal.Quotient.mk I r ≠ 0 := mt (Quotient.mk_eq_zero I).mp hrI
  have rbar_mem_J : Ideal.Quotient.mk I r ∈ J.map (Ideal.Quotient.mk I) := mem_map_of_mem _ hrJ
  have quotient_f : ∀ x ∈ I.comap f, (Ideal.Quotient.mk I).comp f x = 0 := by
    simp [Quotient.eq_zero_iff_mem]
  have rbar_root :
    (p.map (Ideal.Quotient.mk (I.comap f))).eval₂ (Quotient.lift (I.comap f) _ quotient_f)
        (Ideal.Quotient.mk I r) =
      0 := by
    convert Quotient.eq_zero_iff_mem.mpr hpI
    exact _root_.trans (eval₂_map _ _ _) (hom_eval₂ p f (Ideal.Quotient.mk I) r).symm
  obtain ⟨i, ne_zero, mem⟩ :=
    exists_coeff_ne_zero_mem_comap_of_root_mem rbar_ne_zero rbar_mem_J p_ne_zero rbar_root
  rw [coeff_map] at ne_zero mem
  refine ⟨i, (mem_quotient_iff_mem hIJ).mp ?_, mt ?_ ne_zero⟩
  · simpa using mem
  simp [Quotient.eq_zero_iff_mem]
#align ideal.exists_coeff_mem_comap_sdiff_comap_of_root_mem_sdiff Ideal.exists_coeff_mem_comap_sdiff_comap_of_root_mem_sdiff

theorem comap_lt_comap_of_root_mem_sdiff [I.IsPrime] (hIJ : I ≤ J) {r : S}
    (hr : r ∈ (J : Set S) \ I) {p : R[X]} (p_ne_zero : p.map (Quotient.mk (I.comap f)) ≠ 0)
    (hp : p.eval₂ f r ∈ I) : I.comap f < J.comap f :=
  let ⟨i, hJ, hI⟩ := exists_coeff_mem_comap_sdiff_comap_of_root_mem_sdiff hIJ hr p_ne_zero hp
  SetLike.lt_iff_le_and_exists.mpr ⟨comap_mono hIJ, p.coeff i, hJ, hI⟩
#align ideal.comap_lt_comap_of_root_mem_sdiff Ideal.comap_lt_comap_of_root_mem_sdiff

theorem mem_of_one_mem (h : (1 : S) ∈ I) (x) : x ∈ I :=
  (I.eq_top_iff_one.mpr h).symm ▸ mem_top
#align ideal.mem_of_one_mem Ideal.mem_of_one_mem

theorem comap_lt_comap_of_integral_mem_sdiff [Algebra R S] [hI : I.IsPrime] (hIJ : I ≤ J) {x : S}
    (mem : x ∈ (J : Set S) \ I) (integral : IsIntegral R x) :
    I.comap (algebraMap R S) < J.comap (algebraMap R S) := by
  obtain ⟨p, p_monic, hpx⟩ := integral
  refine comap_lt_comap_of_root_mem_sdiff hIJ mem (map_monic_ne_zero p_monic) ?_
  convert I.zero_mem
#align ideal.comap_lt_comap_of_integral_mem_sdiff Ideal.comap_lt_comap_of_integral_mem_sdiff

theorem comap_ne_bot_of_root_mem [IsDomain S] {r : S} (r_ne_zero : r ≠ 0) (hr : r ∈ I) {p : R[X]}
    (p_ne_zero : p ≠ 0) (hp : p.eval₂ f r = 0) : I.comap f ≠ ⊥ := fun h =>
  let ⟨_, hi, mem⟩ := exists_coeff_ne_zero_mem_comap_of_root_mem r_ne_zero hr p_ne_zero hp
  absurd (mem_bot.mp (eq_bot_iff.mp h mem)) hi
#align ideal.comap_ne_bot_of_root_mem Ideal.comap_ne_bot_of_root_mem

theorem isMaximal_of_isIntegral_of_isMaximal_comap [Algebra R S] [Algebra.IsIntegral R S]
    (I : Ideal S) [I.IsPrime] (hI : IsMaximal (I.comap (algebraMap R S))) : IsMaximal I :=
  ⟨⟨mt comap_eq_top_iff.mpr hI.1.1, fun _ I_lt_J =>
      let ⟨I_le_J, x, hxJ, hxI⟩ := SetLike.lt_iff_le_and_exists.mp I_lt_J
      comap_eq_top_iff.1 <|
        hI.1.2 _ (comap_lt_comap_of_integral_mem_sdiff I_le_J ⟨hxJ, hxI⟩
          (Algebra.IsIntegral.isIntegral x))⟩⟩
#align ideal.is_maximal_of_is_integral_of_is_maximal_comap Ideal.isMaximal_of_isIntegral_of_isMaximal_comap

theorem isMaximal_of_isIntegral_of_isMaximal_comap' (f : R →+* S) (hf : f.IsIntegral) (I : Ideal S)
    [I.IsPrime] (hI : IsMaximal (I.comap f)) : IsMaximal I :=
  let _ : Algebra R S := f.toAlgebra
  have : Algebra.IsIntegral R S := ⟨hf⟩
  isMaximal_of_isIntegral_of_isMaximal_comap (R := R) (S := S) I hI
#align ideal.is_maximal_of_is_integral_of_is_maximal_comap' Ideal.isMaximal_of_isIntegral_of_isMaximal_comap'

variable [Algebra R S]

theorem comap_ne_bot_of_algebraic_mem [IsDomain S] {x : S} (x_ne_zero : x ≠ 0) (x_mem : x ∈ I)
    (hx : IsAlgebraic R x) : I.comap (algebraMap R S) ≠ ⊥ :=
  let ⟨_, p_ne_zero, hp⟩ := hx
  comap_ne_bot_of_root_mem x_ne_zero x_mem p_ne_zero hp
#align ideal.comap_ne_bot_of_algebraic_mem Ideal.comap_ne_bot_of_algebraic_mem

theorem comap_ne_bot_of_integral_mem [Nontrivial R] [IsDomain S] {x : S} (x_ne_zero : x ≠ 0)
    (x_mem : x ∈ I) (hx : IsIntegral R x) : I.comap (algebraMap R S) ≠ ⊥ :=
  comap_ne_bot_of_algebraic_mem x_ne_zero x_mem hx.isAlgebraic
#align ideal.comap_ne_bot_of_integral_mem Ideal.comap_ne_bot_of_integral_mem

theorem eq_bot_of_comap_eq_bot [Nontrivial R] [IsDomain S] [Algebra.IsIntegral R S]
    (hI : I.comap (algebraMap R S) = ⊥) : I = ⊥ := by
  refine eq_bot_iff.2 fun x hx => ?_
  by_cases hx0 : x = 0
  · exact hx0.symm ▸ Ideal.zero_mem ⊥
  · exact absurd hI (comap_ne_bot_of_integral_mem hx0 hx (Algebra.IsIntegral.isIntegral x))
#align ideal.eq_bot_of_comap_eq_bot Ideal.eq_bot_of_comap_eq_bot

theorem isMaximal_comap_of_isIntegral_of_isMaximal [Algebra.IsIntegral R S] (I : Ideal S)
    [hI : I.IsMaximal] : IsMaximal (I.comap (algebraMap R S)) := by
  refine Ideal.Quotient.maximal_of_isField _ ?_
  haveI : IsPrime (I.comap (algebraMap R S)) := comap_isPrime _ _
  exact isField_of_isIntegral_of_isField
    algebraMap_quotient_injective (by rwa [← Quotient.maximal_ideal_iff_isField_quotient])
#align ideal.is_maximal_comap_of_is_integral_of_is_maximal Ideal.isMaximal_comap_of_isIntegral_of_isMaximal

theorem isMaximal_comap_of_isIntegral_of_isMaximal' {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : f.IsIntegral) (I : Ideal S) [I.IsMaximal] : IsMaximal (I.comap f) :=
  let _ : Algebra R S := f.toAlgebra
  have : Algebra.IsIntegral R S := ⟨hf⟩
  isMaximal_comap_of_isIntegral_of_isMaximal (R := R) (S := S) I
#align ideal.is_maximal_comap_of_is_integral_of_is_maximal' Ideal.isMaximal_comap_of_isIntegral_of_isMaximal'

section IsIntegralClosure

variable (S) {A : Type*} [CommRing A]
variable [Algebra R A] [Algebra A S] [IsScalarTower R A S] [IsIntegralClosure A R S]

theorem IsIntegralClosure.comap_lt_comap {I J : Ideal A} [I.IsPrime] (I_lt_J : I < J) :
    I.comap (algebraMap R A) < J.comap (algebraMap R A) :=
  let ⟨I_le_J, x, hxJ, hxI⟩ := SetLike.lt_iff_le_and_exists.mp I_lt_J
  comap_lt_comap_of_integral_mem_sdiff I_le_J ⟨hxJ, hxI⟩ (IsIntegralClosure.isIntegral R S x)
#align ideal.is_integral_closure.comap_lt_comap Ideal.IsIntegralClosure.comap_lt_comap

theorem IsIntegralClosure.isMaximal_of_isMaximal_comap (I : Ideal A) [I.IsPrime]
    (hI : IsMaximal (I.comap (algebraMap R A))) : IsMaximal I :=
  have : Algebra.IsIntegral R A := IsIntegralClosure.isIntegral_algebra R S
  isMaximal_of_isIntegral_of_isMaximal_comap I hI
#align ideal.is_integral_closure.is_maximal_of_is_maximal_comap Ideal.IsIntegralClosure.isMaximal_of_isMaximal_comap

variable [IsDomain A]

theorem IsIntegralClosure.comap_ne_bot [Nontrivial R] {I : Ideal A} (I_ne_bot : I ≠ ⊥) :
    I.comap (algebraMap R A) ≠ ⊥ :=
  let ⟨x, x_mem, x_ne_zero⟩ := I.ne_bot_iff.mp I_ne_bot
  comap_ne_bot_of_integral_mem x_ne_zero x_mem (IsIntegralClosure.isIntegral R S x)
#align ideal.is_integral_closure.comap_ne_bot Ideal.IsIntegralClosure.comap_ne_bot

theorem IsIntegralClosure.eq_bot_of_comap_eq_bot [Nontrivial R] {I : Ideal A} :
    I.comap (algebraMap R A) = ⊥ → I = ⊥ := by
  -- Porting note: `imp_of_not_imp_not` seems not existing
  contrapose; exact (IsIntegralClosure.comap_ne_bot S)
#align ideal.is_integral_closure.eq_bot_of_comap_eq_bot Ideal.IsIntegralClosure.eq_bot_of_comap_eq_bot

end IsIntegralClosure

theorem IntegralClosure.comap_lt_comap {I J : Ideal (integralClosure R S)} [I.IsPrime]
    (I_lt_J : I < J) :
    I.comap (algebraMap R (integralClosure R S)) < J.comap (algebraMap R (integralClosure R S)) :=
  IsIntegralClosure.comap_lt_comap S I_lt_J
#align ideal.integral_closure.comap_lt_comap Ideal.IntegralClosure.comap_lt_comap

theorem IntegralClosure.isMaximal_of_isMaximal_comap (I : Ideal (integralClosure R S)) [I.IsPrime]
    (hI : IsMaximal (I.comap (algebraMap R (integralClosure R S)))) : IsMaximal I :=
  IsIntegralClosure.isMaximal_of_isMaximal_comap S I hI
#align ideal.integral_closure.is_maximal_of_is_maximal_comap Ideal.IntegralClosure.isMaximal_of_isMaximal_comap

section

variable [IsDomain S]

theorem IntegralClosure.comap_ne_bot [Nontrivial R] {I : Ideal (integralClosure R S)}
    (I_ne_bot : I ≠ ⊥) : I.comap (algebraMap R (integralClosure R S)) ≠ ⊥ :=
  IsIntegralClosure.comap_ne_bot S I_ne_bot
#align ideal.integral_closure.comap_ne_bot Ideal.IntegralClosure.comap_ne_bot

theorem IntegralClosure.eq_bot_of_comap_eq_bot [Nontrivial R] {I : Ideal (integralClosure R S)} :
    I.comap (algebraMap R (integralClosure R S)) = ⊥ → I = ⊥ :=
  IsIntegralClosure.eq_bot_of_comap_eq_bot S
#align ideal.integral_closure.eq_bot_of_comap_eq_bot Ideal.IntegralClosure.eq_bot_of_comap_eq_bot

/-- `comap (algebraMap R S)` is a surjection from the prime spec of `R` to prime spec of `S`.
`hP : (algebraMap R S).ker ≤ P` is a slight generalization of the extension being injective -/
theorem exists_ideal_over_prime_of_isIntegral_of_isDomain [Algebra.IsIntegral R S] (P : Ideal R)
    [IsPrime P] (hP : RingHom.ker (algebraMap R S) ≤ P) :
    ∃ Q : Ideal S, IsPrime Q ∧ Q.comap (algebraMap R S) = P := by
  have hP0 : (0 : S) ∉ Algebra.algebraMapSubmonoid S P.primeCompl := by
    rintro ⟨x, ⟨hx, x0⟩⟩
    exact absurd (hP x0) hx
  let Rₚ := Localization P.primeCompl
  let Sₚ := Localization (Algebra.algebraMapSubmonoid S P.primeCompl)
  letI : IsDomain (Localization (Algebra.algebraMapSubmonoid S P.primeCompl)) :=
    IsLocalization.isDomain_localization (le_nonZeroDivisors_of_noZeroDivisors hP0)
  obtain ⟨Qₚ : Ideal Sₚ, Qₚ_maximal⟩ := exists_maximal Sₚ
  let _ : Algebra Rₚ Sₚ := localizationAlgebra P.primeCompl S
  have : Algebra.IsIntegral Rₚ Sₚ := ⟨isIntegral_localization⟩
  have Qₚ_max : IsMaximal (comap _ Qₚ) :=
    isMaximal_comap_of_isIntegral_of_isMaximal (R := Rₚ) (S := Sₚ) Qₚ
  refine ⟨comap (algebraMap S Sₚ) Qₚ, ⟨comap_isPrime _ Qₚ, ?_⟩⟩
  convert Localization.AtPrime.comap_maximalIdeal (I := P)
  rw [comap_comap, ← LocalRing.eq_maximalIdeal Qₚ_max,
    ← @IsLocalization.map_comp (P := S) (Q := Sₚ) (g := algebraMap R S)
    (M := P.primeCompl) (T := Algebra.algebraMapSubmonoid S P.primeCompl) (S := Rₚ) _
    _ _ _ _ _ (fun p hp => Algebra.mem_algebraMapSubmonoid_of_mem ⟨p, hp⟩) _ _]
  rfl
#align ideal.exists_ideal_over_prime_of_is_integral' Ideal.exists_ideal_over_prime_of_isIntegral_of_isDomain

end

/-- More general going-up theorem than `exists_ideal_over_prime_of_isIntegral_of_isDomain`.
TODO: Version of going-up theorem with arbitrary length chains (by induction on this)?
  Not sure how best to write an ascending chain in Lean -/
theorem exists_ideal_over_prime_of_isIntegral_of_isPrime
    [Algebra.IsIntegral R S] (P : Ideal R) [IsPrime P]
    (I : Ideal S) [IsPrime I] (hIP : I.comap (algebraMap R S) ≤ P) :
    ∃ Q ≥ I, IsPrime Q ∧ Q.comap (algebraMap R S) = P := by
  obtain ⟨Q' : Ideal (S ⧸ I), ⟨Q'_prime, hQ'⟩⟩ :=
    @exists_ideal_over_prime_of_isIntegral_of_isDomain (R ⧸ I.comap (algebraMap R S)) _ (S ⧸ I) _
      Ideal.quotientAlgebra _ _
      (map (Ideal.Quotient.mk (I.comap (algebraMap R S))) P)
      (map_isPrime_of_surjective Quotient.mk_surjective (by simp [hIP]))
      (le_trans (le_of_eq ((RingHom.injective_iff_ker_eq_bot _).1 algebraMap_quotient_injective))
        bot_le)
  refine ⟨Q'.comap _, le_trans (le_of_eq mk_ker.symm) (ker_le_comap _), ⟨comap_isPrime _ Q', ?_⟩⟩
  rw [comap_comap]
  refine _root_.trans ?_ (_root_.trans (congr_arg (comap (Ideal.Quotient.mk
    (comap (algebraMap R S) I))) hQ') ?_)
  · rw [comap_comap]
    exact congr_arg (comap · Q') (RingHom.ext fun r => rfl)
  · refine _root_.trans (comap_map_of_surjective _ Quotient.mk_surjective _) (sup_eq_left.2 ?_)
    simpa [← RingHom.ker_eq_comap_bot] using hIP

lemma exists_ideal_comap_le_prime (P : Ideal R) [P.IsPrime]
    (I : Ideal S) (hI : I.comap (algebraMap R S) ≤ P) :
    ∃ Q ≥ I, Q.IsPrime ∧ Q.comap (algebraMap R S) ≤ P := by
  let Sₚ := Localization (Algebra.algebraMapSubmonoid S P.primeCompl)
  let Iₚ := I.map (algebraMap S Sₚ)
  have hI' : Disjoint (Algebra.algebraMapSubmonoid S P.primeCompl : Set S) I := by
    rw [Set.disjoint_iff]
    rintro _ ⟨⟨x, hx : x ∉ P, rfl⟩, hx'⟩
    exact (hx (hI hx')).elim
  have : Iₚ ≠ ⊤ := by
    rw [Ne, Ideal.eq_top_iff_one, IsLocalization.mem_map_algebraMap_iff
      (Algebra.algebraMapSubmonoid S P.primeCompl) Sₚ, not_exists]
    simp only [one_mul, IsLocalization.eq_iff_exists (Algebra.algebraMapSubmonoid S P.primeCompl),
      not_exists]
    exact fun x c ↦ hI'.ne_of_mem (mul_mem c.2 x.2.2) (I.mul_mem_left c x.1.2)
  obtain ⟨M, hM, hM'⟩ := Ideal.exists_le_maximal _ this
  refine ⟨_, Ideal.map_le_iff_le_comap.mp hM', hM.isPrime.comap _, ?_⟩
  intro x hx
  by_contra hx'
  exact Set.disjoint_left.mp ((IsLocalization.isPrime_iff_isPrime_disjoint
    (Algebra.algebraMapSubmonoid S P.primeCompl) Sₚ M).mp hM.isPrime).2 ⟨_, hx', rfl⟩ hx

theorem exists_ideal_over_prime_of_isIntegral [Algebra.IsIntegral R S] (P : Ideal R) [IsPrime P]
    (I : Ideal S) (hIP : I.comap (algebraMap R S) ≤ P) :
    ∃ Q ≥ I, IsPrime Q ∧ Q.comap (algebraMap R S) = P := by
  have ⟨P', hP, hP', hP''⟩ := exists_ideal_comap_le_prime P I hIP
  obtain ⟨Q, hQ, hQ', hQ''⟩ := exists_ideal_over_prime_of_isIntegral_of_isPrime P P' hP''
  exact ⟨Q, hP.trans hQ, hQ', hQ''⟩
#align ideal.exists_ideal_over_prime_of_is_integral Ideal.exists_ideal_over_prime_of_isIntegral

/-- `comap (algebraMap R S)` is a surjection from the max spec of `S` to max spec of `R`.
`hP : (algebraMap R S).ker ≤ P` is a slight generalization of the extension being injective -/
theorem exists_ideal_over_maximal_of_isIntegral [Algebra.IsIntegral R S]
    (P : Ideal R) [P_max : IsMaximal P] (hP : RingHom.ker (algebraMap R S) ≤ P) :
    ∃ Q : Ideal S, IsMaximal Q ∧ Q.comap (algebraMap R S) = P := by
  obtain ⟨Q, -, Q_prime, hQ⟩ := exists_ideal_over_prime_of_isIntegral P ⊥ hP
  exact ⟨Q, isMaximal_of_isIntegral_of_isMaximal_comap _ (hQ.symm ▸ P_max), hQ⟩
#align ideal.exists_ideal_over_maximal_of_is_integral Ideal.exists_ideal_over_maximal_of_isIntegral

lemma map_eq_top_iff_of_ker_le
    (f : R →+* S) {I : Ideal R} (hf₁ : RingHom.ker f ≤ I) (hf₂ : f.IsIntegral) :
    I.map f = ⊤ ↔ I = ⊤ := by
  constructor; swap
  · rintro rfl; exact Ideal.map_top _
  contrapose
  intro h
  obtain ⟨m, _, hm⟩ := Ideal.exists_le_maximal I h
  let _ := f.toAlgebra
  have : Algebra.IsIntegral _ _ := ⟨hf₂⟩
  obtain ⟨m', _, rfl⟩ := exists_ideal_over_maximal_of_isIntegral m (hf₁.trans hm)
  rw [← map_le_iff_le_comap] at hm
  exact (hm.trans_lt (lt_top_iff_ne_top.mpr (IsMaximal.ne_top ‹_›))).ne

lemma map_eq_top_iff
    (f : R →+* S) {I : Ideal R} (hf₁ : Function.Injective f) (hf₂ : f.IsIntegral) :
    I.map f = ⊤ ↔ I = ⊤ :=
  map_eq_top_iff_of_ker_le f (by simp [f.injective_iff_ker_eq_bot.mp hf₁]) hf₂

end IsDomain

end Ideal
