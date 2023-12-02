/-
Copyright (c) 2023 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston
-/
import Mathlib.FieldTheory.Galois
import Mathlib.RingTheory.Norm
import Mathlib.RepresentationTheory.GroupCohomology.LowDegree
import Mathlib.LinearAlgebra.LinearIndependent

/-!
# Hilbert's Theorem 90

Let `L/K` be a finite extension of fields. Then this file proves Noether's generalization of
Hilbert's Theorem 90: that the 1st group cohomology $H^1(Aut_K(L), Lˣ)$ is trivial. We state it
both in terms of $H^1$ and in terms of cocycles being coboundaries.

Hilbert's original statement was that if $L/K$ is Galois, and $Gal(L/K)$ is cyclic, generated
by an element `σ`, then for every `x : L` such that $N_{L/K}(x) = 1,$ there exists `y : L` such
that $x = y/σ(y).$ This can be deduced from the fact that the function $Gal(L/K) → L^\times$
sending $σ^i \mapsto xσ(x)σ^2(x)...σ^{i-1}(x)$ is a 1-cocycle. Alternatively, we can derive it by
analyzing the cohomology of finite cyclic groups in general.

Noether's generalization also holds for infinite Galois extensions.

## Main statements

* `groupCohomology.hilbert90`: for all $f: Aut_K(L) \to L^\times$ satisfying the 1-cocycle
condition, there exists `β : Lˣ` such that $g(β)/β = f(g)$ for all `g : Aut_K(L)`.
* `groupCohomology.H1ofAutOnUnitsUnique`: $H^1(Aut_K(L), L^\times)$ is trivial.

## Implementation notes

Given a commutative ring `k` and a group `G`, group cohomology is developed in terms of `k`-linear
`G`-representations on `k`-modules. Therefore stating Noether's generalization of Hilbert 90 in
terms of `H¹` requires us to turn the natural action of `Aut_K(L)` on `Lˣ` into a morphism
`Aut_K(L) →* (Additive Lˣ →ₗ[ℤ] Additive Lˣ)`. Thus we provide the non-`H¹` version too, as its
statement is clearer.

## TODO

* The original Hilbert's Theorem 90, deduced from the cohomology of general finite cyclic groups.
* Develop Galois cohomology to extend Noether's result to infinite Galois extensions.
* "Additive Hilbert 90": let `L/K` be a finite Galois extension. Then $H^n(Gal(L/K), L)$ is trivial
for all $1 ≤ n.$

-/
universe u
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
      (fun x y h => by ext; exact FunLike.ext_iff.1 h _)
  have h := linearIndependent_iff.1 this
    (Finsupp.equivFunOnFinite.symm (fun φ => (f φ : L)))
  fun H => Units.ne_zero (f 1) (FunLike.ext_iff.1 (h H) 1)

end Hilbert90
section
open Hilbert90
variable {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]

/-- Given a finite extension of fields and a function `f : Aut_K(L) → Lˣ` satisfying
`f(gh) = g(f(h)) * f(g)` for all `g, h : Aut_K(L)`, there exists `β : Lˣ` such that
`g(β)/β = f(g)` for all `g : Aut_K(L).` -/
theorem hilbert90 (f : (L ≃ₐ[K] L) → Lˣ) (hf : IsMulOneCocycle f) :
    IsMulOneCoboundary f := by
/- Let `z : L` be such that `∑ f(h) * h(z) ≠ 0`, for `h ∈ Aut_K(L)` -/
  obtain ⟨z, hz⟩ : ∃ z, aux f z ≠ 0 :=
    not_forall.1 (fun H => aux_ne_zero f $ funext $ fun x => H x)
  have : aux f z = ∑ h, f h * h z := by simp [aux, Finsupp.total, Finsupp.sum_fintype]
/- Let `β = (∑ f(h) * h(z))⁻¹.` -/
  use (Units.mk0 (aux f z) hz)⁻¹
  intro g
/- Then the equality follows from the hypothesis that `f` is a 1-cocycle. -/
  simp only [IsMulOneCocycle, IsMulOneCoboundary, AlgEquiv.smul_units_def,
    map_inv, div_inv_eq_mul, inv_mul_eq_iff_eq_mul, Units.ext_iff, this,
    Units.val_mul, Units.coe_map, Units.val_mk0, MonoidHom.coe_coe] at hf ⊢
  simp_rw [map_sum, map_mul, Finset.sum_mul, mul_assoc, mul_comm _ (f _ : L), ←mul_assoc, ←hf g]
  exact eq_comm.1 (Fintype.sum_bijective (fun i => g * i)
    (Group.mulLeft_bijective g) _ _ (fun i => rfl))

end
variable (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]

/-- Given a finite extension of fields `L/K`, the first group cohomology `H¹(Aut_K(L), Lˣ)` is
trivial. -/
noncomputable instance H1ofAutOnUnitsUnique : Unique (H1 (Rep.ofAlgebraAutOnUnits K L)) where
  default := 0
  uniq := fun a => Quotient.inductionOn' a fun x => (Submodule.Quotient.mk_eq_zero _).2 <| by
    refine' (oneCoboundariesOfIsMulOneCoboundary _ _).2
    rcases hilbert90 x.1 (isMulOneCocycle_of_oneCocycles x) with ⟨β, hβ⟩
    use β


open Rep

variable {k G : Type u} [CommRing k] [Group G] (A : Rep k G)

noncomputable def sumρPowers (g : G) (n : ℕ) : A →ₗ[k] A :=
∑ i in Finset.range n, A.ρ (g ^ i)

lemma sumρPowers_def (g : G) (n : ℕ) :
    sumρPowers A g n = ∑ i in Finset.range n, A.ρ (g ^ i) := rfl

@[simp] lemma sumρPowers_one (g : G) :
    sumρPowers A g 1 = 1 := by
  simp only [sumρPowers_def, Finset.range_one, map_pow, Finset.sum_singleton, pow_zero]

theorem sumρPowers_orderOf_eq_norm [Fintype G] (g : G) (hg : ∀ h, h ∈ Submonoid.powers g) :
    sumρPowers A g (orderOf g) = (norm A).hom := by
  ext
  rw [sumρPowers, Rep.norm]
  simp only [map_pow, LinearMap.coeFn_sum, Finset.sum_apply, Rep.homMk_hom]
  exact Finset.sum_bij (fun n _ => g ^ n) (fun a ha => Finset.mem_univ _)
    (fun a _ => by simp only [map_pow])
    (fun a b ha hb (hab : g ^ a = g ^ b) => Nat.ModEq.eq_of_lt_of_lt (pow_eq_pow_iff_modEq.1 hab)
      (Finset.mem_range.1 ha) (Finset.mem_range.1 hb))
    (fun b _ => by
    { rcases hg b with ⟨i, hi⟩
      exact ⟨i % orderOf g, Finset.mem_range.2 (Nat.mod_lt i $ IsOfFinOrder.orderOf_pos
        (isOfFinOrder_of_finite g)), by simp only [Finset.mem_univ, pow_mod_orderOf, hi] at *⟩ })

theorem sumρPowers_add (g : G) (m n : ℕ) :
    sumρPowers A g (m + n) = sumρPowers A g m + (A.ρ g) ^ m * sumρPowers A g n := by
  simp only [sumρPowers_def, map_pow, Finset.sum_range_add, pow_add, add_right_inj,
    ←Finset.mul_sum]

theorem sumρPowers_orderOf_mul (g : G) (i : ℕ) :
    sumρPowers A g (orderOf g * i) = i * sumρPowers A g (orderOf g) := by
  induction i with
  | zero =>
    simp only [Nat.zero_eq, mul_zero, sumρPowers_def, Finset.range_zero, map_pow,
      Finset.sum_empty, Nat.cast_zero, zero_mul]
  | succ i hi =>
    simp only [sumρPowers_def] at *
    simp only [Nat.cast_succ, mul_add, add_mul, ←hi, one_mul, mul_one, Nat.succ_eq_add_one,
      Finset.sum_range_add, pow_add, pow_mul, pow_orderOf_eq_one g, one_pow]

open groupCohomology

lemma finEquivPowers_symm_apply'
    {G : Type*} [Group G] (g : G) (hg : IsOfFinOrder g) (n : ℕ) :
    (finEquivPowers _ hg).symm ⟨g ^ n, n, rfl⟩ = n % (orderOf g) :=
  Fin.ext_iff.1 (finEquivPowers_symm_apply _ _ _)

lemma one_lt_orderOf_of_isOfFinOrder_ne_one {G : Type*} [Group G] (g : G)
    (hg : IsOfFinOrder g) (h1 : g ≠ 1) :
    1 < orderOf g := Nat.one_lt_iff_ne_zero_and_ne_one.2
  ⟨fun hnot => orderOf_eq_zero_iff.1 hnot hg, fun hnot => h1 (orderOf_eq_one_iff.1 hnot)⟩

lemma finEquivPowers_symm_self {G : Type*} [Group G] (g : G) (h1 : g ≠ 1) (hg : IsOfFinOrder g) :
    (finEquivPowers _ hg).symm ⟨g, 1, pow_one _⟩ = (1 : ℕ) := by
  convert Fin.ext_iff.1 (finEquivPowers_symm_apply g hg 1)
  · rw [pow_one]
  · simp_rw [Nat.mod_eq_of_lt (one_lt_orderOf_of_isOfFinOrder_ne_one g hg h1)]
  · exact ⟨1, rfl⟩

lemma finEquivPowers_symm_one {G : Type*} [Group G] (g : G) (hg : IsOfFinOrder g) :
    (finEquivPowers _ hg).symm ⟨1, 0, pow_zero _⟩ = (0 : ℕ) := by
  convert Fin.ext_iff.1 (finEquivPowers_symm_apply g hg 0)
  · rw [pow_zero]
  · exact ⟨0, rfl⟩

/-- Given a generator `g` of a finite group `G`, a representation `A` of `G`, and an element
`x : A` of norm zero, the map `G → A` sending `gⁱ ↦ ∑ ρ_A(gʲ)(x)` for `0 ≤ j < i` is
a 1-cocycle. -/
noncomputable def oneCocyclesOfGenerator [Fintype G] (x : A) (g : G)
    (hg : ∀ h, h ∈ Submonoid.powers g) (hx : (norm A).hom x = (0 : A)) :
  oneCocycles A where
    val :=
      let φ := (finEquivPowers _ (isOfFinOrder_of_finite g)).symm
      fun h => sumρPowers A g (φ ⟨h, hg h⟩) x
    property := by
      by_cases h1 : g = 1
      · cases h1
        rw [mem_oneCocycles_iff]
        intro g h
        rcases hg g with ⟨n, rfl⟩
        rcases hg h with ⟨m, rfl⟩
        simp only [mem_oneCocycles_iff, sumρPowers_def, one_pow, map_one, Finset.sum_const,
          Finset.card_range, nsmul_eq_mul, mul_one, Module.End.natCast_apply, map_nsmul,
          LinearMap.one_apply, self_eq_add_right, Nat.isUnit_iff, finEquivPowers_symm_one,
          zero_smul]
      refine' mem_oneCocycles_of_map_generator _ g hg fun j => _
      rcases Nat.dvd_sub_mod (n := orderOf g) j with ⟨b, hb⟩
      nth_rw 2 [(Nat.sub_eq_iff_eq_add (Nat.mod_le _ _)).1 hb]
      simp only [finEquivPowers_symm_apply, finEquivPowers_symm_self g h1, sumρPowers_one,
        LinearMap.one_apply, ←LinearMap.sum_apply, ←sumρPowers_def, sumρPowers_add,
        sumρPowers_orderOf_mul, ←map_pow, pow_mul, pow_orderOf_eq_one, one_pow, map_one, one_mul,
        LinearMap.add_apply, LinearMap.mul_apply, Module.End.natCast_apply, self_eq_add_left,
        Nat.isUnit_iff, sumρPowers_orderOf_eq_norm A g hg]
      erw [hx] -- why erw??
      rw [smul_zero]

end groupCohomology
