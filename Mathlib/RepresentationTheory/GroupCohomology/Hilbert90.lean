/-
Copyright (c) 2023 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston
-/
import Mathlib.FieldTheory.Fixed
import Mathlib.RingTheory.Norm
import Mathlib.RepresentationTheory.GroupCohomology.LowDegree
import Mathlib.LinearAlgebra.LinearIndependent

/-!
# Hilbert's Theorem 90

This file proves 2 versions of Hilbert's theorem 90.
The first is due to Noether, and is a generalization of Hilbert's original statement. It says that
given a finite extension of fields $L/K,$ the 1st group cohomology $H^1(Aut_K(L), Lˣ)$ is trivial.
We state it both in terms of $H^1$ and in terms of cocycles being coboundaries.
Noether's generalization also holds for infinite Galois extensions.

We then deduce Hilbert's original statement: if $L/K$ is finite and Galois, and $Gal(L/K)$ is
cyclic with a generator `σ`, then for every `x : L` such that $N_{L/K}(x) = 1,$ there exists `y : L`
such that $x = σ(y)/y.$ We prove this by showing that the function $Gal(L/K) → L^\times$
sending $σ^i \mapsto xσ(x)σ^2(x)...σ^{i-1}(x)$ is a 1-cocycle. Alternatively, we could derive it by
analyzing the cohomology of finite cyclic groups in general.

## Main statements

* `groupCohomology.isMulOneCoboundary_of_isMulOneCocycle_of_aut_to_units`: Noether's generalization
of Hilbert's Theorem 90: for all $f: Aut_K(L) \to L^\times$ satisfying the 1-cocycle
condition, there exists `β : Lˣ` such that $g(β)/β = f(g)$ for all `g : Aut_K(L)`.
* `groupCohomology.H1ofAutOnUnitsUnique`: Noether's generalization of Hilbert's Theorem 90:
$H^1(Aut_K(L), L^\times)$ is trivial.
* `groupCohomology.hilbert90Cyclic`: Given `L/K` finite, Galois and cyclic with generator
`g : Gal(L/K)`, then for any `x : L` such that $N_{L/K} = 1,$ there exists `y : L` such that
$g(y)/y = x.$

## Implementation notes

Given a commutative ring `k` and a group `G`, group cohomology is developed in terms of `k`-linear
`G`-representations on `k`-modules. Therefore stating Noether's generalization of Hilbert 90 in
terms of `H¹` requires us to turn the natural action of `Aut_K(L)` on `Lˣ` into a morphism
`Aut_K(L) →* (Additive Lˣ →ₗ[ℤ] Additive Lˣ)`. Thus we provide the non-`H¹` version too, as its
statement is clearer.

## TODO

* Develop Galois cohomology to extend Noether's result to infinite Galois extensions.
* "Additive Hilbert 90": let `L/K` be a finite Galois extension. Then $H^n(Gal(L/K), L)$ is trivial
for all $1 ≤ n.$

-/

open BigOperators
namespace groupCohomology
namespace Hilbert90

variable {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]

/-- Given `f : Aut_K(L) → Lˣ`, the sum `∑ f(φ) • φ` for `φ ∈ Aut_K(L)`, as a function `L → L`. -/
noncomputable def aux (f : (L ≃ₐ[K] L) → Lˣ) : L → L :=
  Finsupp.total (L ≃ₐ[K] L) (L → L) L (fun φ => φ)
    (Finsupp.equivFunOnFinite.symm (fun φ => (f φ : L)))

theorem aux_ne_zero (f : (L ≃ₐ[K] L) → Lˣ) : aux f ≠ 0 :=
/- the set `Aut_K(L)` is linearly independent in the `L`-vector space `L → L`, by Dedekind's
linear independence of characters -/
  have : LinearIndependent L (fun (f : L ≃ₐ[K] L) => (f : L → L)) :=
    LinearIndependent.comp (ι' := L ≃ₐ[K] L)
      (linearIndependent_monoidHom L L) (fun f => f)
      (fun x y h => by ext; exact DFunLike.ext_iff.1 h _)
  have h := linearIndependent_iff.1 this
    (Finsupp.equivFunOnFinite.symm (fun φ => (f φ : L)))
  fun H => Units.ne_zero (f 1) (DFunLike.ext_iff.1 (h H) 1)

end Hilbert90
section
open Hilbert90
variable {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]

/-- Noether's generalization of Hilbert's Theorem 90: given a finite extension of fields and a
function `f : Aut_K(L) → Lˣ` satisfying `f(gh) = g(f(h)) * f(g)` for all `g, h : Aut_K(L)`, there
exists `β : Lˣ` such that `g(β)/β = f(g)` for all `g : Aut_K(L).` -/
theorem isMulOneCoboundary_of_isMulOneCocycle_of_aut_to_units
    (f : (L ≃ₐ[K] L) → Lˣ) (hf : IsMulOneCocycle f) :
    IsMulOneCoboundary f := by
/- Let `z : L` be such that `∑ f(h) * h(z) ≠ 0`, for `h ∈ Aut_K(L)` -/
  obtain ⟨z, hz⟩ : ∃ z, aux f z ≠ 0 :=
    not_forall.1 (fun H => aux_ne_zero f <| funext <| fun x => H x)
  have : aux f z = ∑ h, f h * h z := by simp [aux, Finsupp.total, Finsupp.sum_fintype]
/- Let `β = (∑ f(h) * h(z))⁻¹.` -/
  use (Units.mk0 (aux f z) hz)⁻¹
  intro g
/- Then the equality follows from the hypothesis that `f` is a 1-cocycle. -/
  simp only [IsMulOneCocycle, IsMulOneCoboundary, AlgEquiv.smul_units_def,
    map_inv, div_inv_eq_mul, inv_mul_eq_iff_eq_mul, Units.ext_iff, this,
    Units.val_mul, Units.coe_map, Units.val_mk0, MonoidHom.coe_coe] at hf ⊢
  simp_rw [map_sum, map_mul, Finset.sum_mul, mul_assoc, mul_comm _ (f _ : L), ← mul_assoc, ← hf g]
  exact eq_comm.1 (Fintype.sum_bijective (fun i => g * i)
    (Group.mulLeft_bijective g) _ _ (fun i => rfl))

end
variable (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]

/-- Noether's generalization of Hilbert's Theorem 90: given a finite extension of fields `L/K`, the
first group cohomology `H¹(Aut_K(L), Lˣ)` is trivial. -/
noncomputable instance H1ofAutOnUnitsUnique : Unique (H1 (Rep.ofAlgebraAutOnUnits K L)) where
  default := 0
  uniq := fun a => Quotient.inductionOn' a fun x => (Submodule.Quotient.mk_eq_zero _).2 <| by
    refine' (oneCoboundariesOfIsMulOneCoboundary _).2
    rcases isMulOneCoboundary_of_isMulOneCocycle_of_aut_to_units x.1
      (isMulOneCocycle_of_oneCocycles x) with ⟨β, hβ⟩
    use β

end groupCohomology
open Rep

variable {K L : Type} [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

-- could move to `RepresentationTheory.Rep` but would have to add imports
/-- Given `L/K` finite and Galois, and `x : Lˣ`, this essentially says
`(∏ σ) • x = N_{L/K}(x)`, where the product is over `σ ∈ Gal(L/K)`. -/
theorem Rep.norm_ofAlgebraAutOnUnits_eq (x : Lˣ) :
    (Additive.toMul ((Rep.norm (Rep.ofAlgebraAutOnUnits K L)).hom (Additive.ofMul x))).1
      = algebraMap K L (Algebra.norm K (x : L)) := by
  simp_rw [Algebra.norm_eq_prod_automorphisms, ofAlgebraAutOnUnits]
  erw [norm_ofMulDistribMulAction_eq (G := L ≃ₐ[K] L) (M := Lˣ)]
  simp only [AlgEquiv.smul_units_def, Units.coe_prod, Units.coe_map, MonoidHom.coe_coe]

namespace groupCohomology
variable (g : L ≃ₐ[K] L) (hg : ∀ h, h ∈ Submonoid.powers g)

/-- Given a finite cyclic Galois extension `L/K`, an element `x : L` such that `N_{L/K}(x) = 1`,
and a generator `g` of `Gal(L/K)`, there exists `y : Lˣ` such that `g(y)/y = x`. -/
theorem hilbert90_cyclic (x : L) (hx : Algebra.norm K x = 1) : ∃ y : Lˣ, g y / y = x := by
  let xu : Lˣ := (Ne.isUnit (fun h0 => zero_ne_one ((Algebra.norm_zero).symm.trans
     (h0 ▸ hx))) : IsUnit x).unit
  have hx' : algebraMap K L (Algebra.norm K (xu : L)) = _ := congrArg (algebraMap K L) hx
  rw [← norm_ofAlgebraAutOnUnits_eq xu, map_one] at hx'
  let f := oneCocyclesOfGenerator (A := Rep.ofAlgebraAutOnUnits K L) (Additive.ofMul xu) g hg
    (Additive.toMul.injective (Units.ext hx'))
  obtain ⟨ε, hε⟩ := groupCohomology.hilbert90 _ (isMulOneCocycle_of_oneCocycles f)
  use ε
  specialize hε g
  simpa only [AlgEquiv.smul_units_def, Rep.ofAlgebraAutOnUnits, Function.comp_apply,
    oneCocyclesOfGenerator_self, Units.ext_iff, Units.val_div_eq_div_val, Units.coe_map,
    MonoidHom.coe_coe] using hε


end groupCohomology
