/-
Copyright (c) 2026 Raphael Douglas Giles. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Douglas Giles
-/
import Mathlib.AlgebraicGeometry.AlgebraicCycle.CohomologyReduction
import Mathlib.AlgebraicGeometry.AlgebraicCycle.Degree
import Mathlib.AlgebraicGeometry.AlgebraicCycle.ResidueFieldFinite
import Mathlib.AlgebraicGeometry.AlgebraicCycle.StructureSheafIso

/-!
# Conditional Riemann-Roch

In this file we show a conditional form of the algebraic Riemann-Roch theorem for curves
(`riemann_roch`): if `X` is an integral Noetherian scheme which is regular in codimension one,
has Krull dimension at most one and is locally of finite type over a field `k`, and the
structure sheaf `𝒪ₓ` has a well-defined finite Euler characteristic
(`Scheme.Modules.HasFiniteEulerCharacteristic`: finite-dimensional cohomology which vanishes in all
sufficiently large degrees), then for every Weil divisor `D` we have
`χ(𝒪ₓ(D)) = deg(D) + χ(𝒪ₓ)`.

For `X` proper over `k` the finiteness of the Euler characteristic holds by the finiteness
theorem for coherent cohomology (EGA III 3.2.1) together with Grothendieck vanishing,
neither of which is yet available in Mathlib; we therefore take it as a hypothesis
(hence the "conditional" in the title).

Notes: The work here is reliant on WIP work by Brian Nugent (on the long exact sequence for sheaf
cohomology) and by Jesse Alama (on the Euler-Poincare formula). Notably, we needed a slightly
different form of the Euler-Poincare stuff, which I have proven (by copying Jesse's proof) purely
so that the results here can be sorry-free, but I expect the eventual form of Euler-Poincare that
lands in Mathlib will generalize both forms of the theorem.
-/

namespace AlgebraicGeometry.AlgebraicCycle.SheafViaSubmodule

open AlgebraicGeometry Scheme Order CategoryTheory Limits Opposite TopologicalSpace
open Function.locallyFinsupp Function.locallyFinsuppWithin

universe u

variable {X : Scheme.{u}} (k : Type u) [Field k] [X.Over (Spec (CommRingCat.of k))]
    [IsIntegral X] [IsNoetherian X] [IsRegularInCodimensionOne X]
    (D : AlgebraicCycle X ℤ)

lemma eulerChar_step {p : X} (hp : coheight p = 1)
    (E : AlgebraicCycle X ℤ) (o : ShortComplex X.Modules) (ho : o.ShortExact)
    (hχ₁ : o.X₁.HasFiniteEulerCharacteristic k)
    (hχ₂ : o.X₂.HasFiniteEulerCharacteristic k)
    (hχ₃ : (residueLineSheaf hp E).HasFiniteEulerCharacteristic k)
    (hC : o.X₃ = residueLineSheaf hp E) :
    o.X₂.eulerChar k = o.X₁.eulerChar k + Module.finrank k (X.residueField p) := by
  obtain ⟨N₁, hb₁⟩ := hχ₁.vanishing
  obtain ⟨N₂, hb₂⟩ := hχ₂.vanishing
  have hb : ∀ n, max N₁ N₂ < n → Subsingleton (o.X₁.H n) :=
    fun n hn => hb₁ n (lt_of_le_of_lt (le_max_left N₁ N₂) hn)
  have hb' : ∀ n, max N₁ N₂ < n → Subsingleton (o.X₂.H n) :=
    fun n hn => hb₂ n (lt_of_le_of_lt (le_max_right N₁ N₂) hn)
  have hf₃' : ∀ n, Module.Finite k (o.X₃.H n) := fun n => hC ▸ hχ₃.finite n
  have hb₃ : ∀ n, max N₁ N₂ < n → Subsingleton (o.X₃.H n) :=
    fun n hn => hC ▸ subsingleton_H_residueLineSheaf_of_pos hp E (by omega)
  rw [eulerChar_additive k o ho hχ₁.finite hχ₂.finite hf₃' hb hb' hb₃, hC,
    eulerChar_residueLineSheaf k hp E]

open Classical in
/-- Adding a codimension-one point `p` to a Weil divisor `E` raises `χ(𝒪ₓ(E))` by
`finrank k κ(p)`. -/
lemma eulerChar_add_step [Order.KrullDimLE 1 X]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k))]
    (hχ₀ : (structureSheafModule X).HasFiniteEulerCharacteristic k)
    (E : AlgebraicCycle X ℤ) (hE : IsWeilDivisor E) {p : X} (hp : coheight p = 1) :
    (sheaf (E + single p 1)).eulerChar k =
      (sheaf E).eulerChar k + Module.finrank k (X.residueField p) :=
  eulerChar_step k hp (E + single p 1)
    (twistedClosedSubschemeComplex₂ (D := E) (D' := E + single p 1) hp (by simp))
    (twistedClosedSubschemeComplex₂_shortExact hE hp (by simp)
      (eq_of_le_of_coheight_eq_one hp))
    (hasEulerCharacteristic_sheaf k hχ₀ hE)
    (hasEulerCharacteristic_sheaf k hχ₀
      (Function.locallyFinsupp.support_add_single_subset hE hp))
    (hasEulerCharacteristic_residueLineSheaf k hp (E + single p 1))
    rfl

open Classical in
/-- Subtracting a codimension-one point `p` from a Weil divisor `E` lowers `χ(𝒪ₓ(E))` by
`finrank k κ(p)`. -/
lemma eulerChar_sub_step [Order.KrullDimLE 1 X]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k))]
    (hχ₀ : (structureSheafModule X).HasFiniteEulerCharacteristic k)
    (E : AlgebraicCycle X ℤ) (hE : IsWeilDivisor E) {p : X} (hp : coheight p = 1) :
    (sheaf (E - single p 1)).eulerChar k =
      (sheaf E).eulerChar k - Module.finrank k (X.residueField p) := by
  have : (sheaf E).eulerChar k =
      (sheaf (E - single p 1)).eulerChar k + Module.finrank k (X.residueField p) :=
    eulerChar_step k hp E
      (twistedClosedSubschemeComplex₁ (D := E) (D' := E - single p 1) hp (by simp))
      (twistedClosedSubschemeComplex₁_shortExact hE hp (by simp)
        (eq_of_le_of_coheight_eq_one hp))
      (hasEulerCharacteristic_sheaf k hχ₀
        (Function.locallyFinsupp.support_sub_single_subset hE hp))
      (hasEulerCharacteristic_sheaf k hχ₀ hE)
      (hasEulerCharacteristic_residueLineSheaf k hp E)
      rfl
  lia

open Classical in
/--
**Conditional Riemann-Roch.** Let `X` be a curve over a field `k`: an integral Noetherian
scheme, regular in codimension one, of Krull dimension at most one and locally of finite type
over `k`. If the structure sheaf `𝒪ₓ` has a well-defined finite Euler characteristic (`Hⁿ(X, 𝒪ₓ)` is
finite dimensional for every `n` and vanishes in all sufficiently large degrees), then for
every Weil divisor `D`, `χ(𝒪ₓ(D)) = deg D + χ(𝒪ₓ)`.

Note that this claim that the Euler characteristic is finite is the reason I have labelled this
result "conditional". This holds whenever `X` is proper over `k`, but showing this is a nontrivial
task.
-/
theorem riemann_roch [Order.KrullDimLE 1 X]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k))]
    (hχ₀ : (structureSheafModule X).HasFiniteEulerCharacteristic k)
    (hD : IsWeilDivisor D) :
    (sheaf D).eulerChar k = D.degree k + (structureSheafModule X).eulerChar k := by
  rw [eulerChar_eq_of_iso k (unitIsoSheafZero (X := X))]
  induction D, hD using Function.locallyFinsupp.inductionOn with
  | zero => simp [degree]
  | add E hE ih p hp =>
    have step := eulerChar_add_step k hχ₀ E hE hp
    simp [step, ih]
    ring
  | minus E hE ih p hp =>
    have step := eulerChar_sub_step k hχ₀ E hE hp
    simp [step, ih]
    ring

end AlgebraicGeometry.AlgebraicCycle.SheafViaSubmodule
