/-
Copyright (c) 2026 Lambert A'Campo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lambert A'Campo
-/
module

public import Mathlib.Algebra.Group.Submonoid.Membership
public import Mathlib.Algebra.Module.Injective
public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.RingTheory.Noetherian.Basic

/-!
# Injective modules over a Noetherian ring

This file proves Hartshorne's Lemma III.3.3: if `R` is a commutative
Noetherian ring and `I` is an injective `R`-module, then for
any `f : R` the localization map `I → I_f` is surjective.

## Main statement

* `Module.surjective_of_isLocalizedModule_of_injective`: for `R` Noetherian and `I` injective,
  the localization map `I → I_f` is surjective for any `f : R`.

## References

* [Hartshorne, *Algebraic Geometry*][har77], Lemma III.3.3
-/

public section

universe u

variable {R : Type u} [CommRing R]

private lemma ascending_ideal_b (f : R) : Monotone (fun i ↦ Ideal.torsionOf R R (f ^ i)) := by
  intro i j hle
  choose k hk using Nat.exists_eq_add_of_le hle
  intro a ha
  rw [Ideal.mem_torsionOf_iff] at ha
  rw [Ideal.mem_torsionOf_iff]
  have h : f ^ j = f ^ i * f ^ k := by
    rw [hk]
    ring_nf
  rw [h, smul_eq_mul]
  rw [smul_eq_mul] at ha
  rw [← mul_assoc, ha]
  exact zero_mul _

private abbrev ideal_b_order_hom (f : R) : ℕ →o Ideal R :=
  ⟨fun i ↦ Ideal.torsionOf R R (f ^ i), ascending_ideal_b f⟩

private lemma exists_divide_by_fn_map (f : R) (n : ℕ) (r : ℕ)
    (hr : ∀ (i : ℕ), Ideal.torsionOf R R (f ^ (r + i)) = Ideal.torsionOf R R (f ^ r))
    {M : Type u} [AddCommGroup M] [Module R M] (y : M) :
    ∃ phi : Ideal.span {f^(r + n)} →ₗ[R] M,
      phi ⟨f ^ (r + n), Ideal.mem_span_singleton_self _⟩ = f ^ r • y := by
  have hker0 : Ideal.torsionOf R R (f ^ r) ≤
      LinearMap.ker (LinearMap.toSpanSingleton R M (f ^ r • y)) := by
    intro c hc
    rw [Ideal.mem_torsionOf_iff, smul_eq_mul] at hc
    rw [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply, smul_smul, hc, zero_smul]
  have hker : Ideal.torsionOf R R (f ^ (r + n)) ≤
      LinearMap.ker (LinearMap.toSpanSingleton R M (f ^ r • y)) := by
    rwa [hr n]
  refine ⟨(Submodule.liftQ (Ideal.torsionOf R R (f ^ (r + n)))
      (LinearMap.toSpanSingleton R M (f ^ r • y)) hker).comp
    (Ideal.quotTorsionOfEquivSpanSingleton R R (f ^ (r + n))).symm.toLinearMap, ?_⟩
  have hmk : (Ideal.quotTorsionOfEquivSpanSingleton R R (f ^ (r + n))).symm
      (⟨f ^ (r + n), Ideal.mem_span_singleton_self _⟩ : Ideal.span {f^(r + n)})
      = Submodule.Quotient.mk (1 : R) := by
    rw [LinearEquiv.symm_apply_eq, Ideal.quotTorsionOfEquivSpanSingleton_apply_mk, one_smul]
  dsimp
  rw [hmk, Submodule.liftQ_apply, LinearMap.toSpanSingleton_apply, one_smul]

variable [IsNoetherianRing R]

private lemma stabilize_ideal_b (f : R) :
    ∃ (r : ℕ), ∀ (i : ℕ), Ideal.torsionOf R R (f ^ (r + i)) = Ideal.torsionOf R R (f ^ r) := by
  choose r hr using monotone_stabilizes_iff_noetherian.mpr inferInstance (ideal_b_order_hom f)
  use r
  intro i
  specialize hr (r + i)
  exact symm (hr (Nat.le_add_right r i))

/-- **Hartshorne III. Lemma 3.3.** If `R` is a Noetherian ring and `I` satisfies Baer's criterion,
then for any `f : R` the localization map `I → I_f` is surjective. -/
theorem Module.surjective_of_isLocalizedModule_of_baer {I : Type u}
    [AddCommGroup I] [Module R I] (hI : Module.Baer R I) (f : R) {I' : Type u} [AddCommGroup I']
    [Module R I'] (g : I →ₗ[R] I') [IsLocalizedModule (Submonoid.powers f) g] :
    Function.Surjective g := by
  intro x
  obtain ⟨n, a, ha⟩ : ∃ (n : ℕ) (a : I), g a = f ^ n • x := by
    obtain ⟨⟨a, s⟩, hs⟩ := IsLocalizedModule.surj (Submonoid.powers f) g x
    choose n hn using (Submonoid.mem_powers_iff s.1 f).1 s.2
    use n, a
    exact hn ▸ hs.symm
  choose r hr using stabilize_ideal_b f
  choose phi hphi using exists_divide_by_fn_map f n r hr a
  choose psi hpsi using hI (Ideal.span {f^(r + n)}) phi
  have hz : f ^ (r + n) • (psi 1) = f ^ r • a := by
    rw [← psi.map_smul (f ^ (r + n)) (1 : R), smul_eq_mul, mul_one, ← hphi]
    exact hpsi _ _
  have hz2 : f ^ (r + n) • (g (psi 1)) = f ^ r • (f ^ n • x) := by
    rw [← ha, ← g.map_smul, ← g.map_smul]
    exact congrArg g hz
  use psi 1
  have s_mem : f ^ (r + n) ∈ Submonoid.powers f :=
    (Submonoid.mem_powers_iff (f ^ (r + n)) f).mpr ⟨r + n, rfl⟩
  have hbij : Function.Bijective
    (algebraMap R (Module.End R I') (⟨f ^ (r + n), s_mem⟩ : Submonoid.powers f)) :=
    (Module.End.isUnit_iff _).mp (IsLocalizedModule.map_units g ⟨f ^ (r + n), s_mem⟩)
  apply hbij.1
  dsimp
  rw [hz2, smul_smul, ← pow_add]

/-- **Hartshorne III. Lemma 3.3.** Let `R` be a Noetherian ring and `I` an injective `R`-module.
For any `f : R`, the localization map `I → I_f` is surjective. -/
theorem Module.surjective_of_isLocalizedModule_of_injective {I : Type u}
    [AddCommGroup I] [Module R I] (hI : Module.Injective R I) (f : R) {I' : Type u}
    [AddCommGroup I'] [Module R I'] (g : I →ₗ[R] I') [IsLocalizedModule (Submonoid.powers f) g] :
    Function.Surjective g :=
  Module.surjective_of_isLocalizedModule_of_baer (Module.Baer.of_injective hI) f g
