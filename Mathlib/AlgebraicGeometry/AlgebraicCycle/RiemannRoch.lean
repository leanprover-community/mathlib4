/-
Copyright (c) 2026 Raphael Douglas Giles. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Douglas Giles
-/
import Mathlib.AlgebraicGeometry.AlgebraicCycle.SkyscraperEulerChar
import Mathlib.AlgebraicGeometry.AlgebraicCycle.Degree
import Mathlib.AlgebraicGeometry.AlgebraicCycle.LocallyFinsupp
import Mathlib.AlgebraicGeometry.AlgebraicCycle.KrullDimLE
import Mathlib.AlgebraicGeometry.AlgebraicCycle.CohomologyReduction
import Mathlib.AlgebraicGeometry.AlgebraicCycle.StructureSheafIso
import Mathlib.AlgebraicGeometry.AlgebraicCycle.ResidueFieldFinite

/-!
# Conditional Riemann-Roch

In this file we show a conditional form of the algebraic Riemann-Roch theorem for curves. In
particular, we show the usual Euler characteristic form of Riemann-Roch
(`χ(𝒪ₓ(D)) = deg(D) + χ(𝒪ₓ)`), but we show this for locally Noetherian, integral schemes `X`
which are regular in codimension one and of finite type over a field `k`,
 have krull dimension at most one and satisfy that `𝒪ₓ` has a well-defined Euler characteristic
 (`Scheme.Modules.HasEulerCharacteristic`: finite-dimensional cohomology which vanishes in all
 sufficiently large degrees). This cohomological assumption follows from `X` being proper over
 `k`, but we do not yet show this implication (hence the "conditional" in the title).

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

/-- The canonical cokernel `Q_p(E)` has a well-defined Euler characteristic as soon as its
cohomology is finite dimensional: its positive-degree cohomology vanishes by flasqueness. -/
lemma hasEulerCharacteristic_residueLineSheaf {p : X} (hp : coheight p = 1)
    (E : AlgebraicCycle X ℤ)
    (hf : ∀ n, Module.Finite k ((residueLineSheaf hp E).H n)) :
    (residueLineSheaf hp E).HasEulerCharacteristic k :=
  ⟨hf, 0, fun _ hn => subsingleton_H_residueLineSheaf_of_pos hp E hn⟩

/-- Additivity of `χ` on a short exact sequence whose third term is the canonical cokernel
`Q_p(E)`: if the terms have well-defined Euler characteristics, the middle one exceeds the
first by `dim_k κ(p)`. -/
lemma eulerChar_step {p : X} (hp : coheight p = 1)
    (E : AlgebraicCycle X ℤ) (o : ShortComplex X.Modules) (ho : o.ShortExact)
    (hχ₁ : o.X₁.HasEulerCharacteristic k) (hχ₂ : o.X₂.HasEulerCharacteristic k)
    (hχ₃ : (residueLineSheaf hp E).HasEulerCharacteristic k)
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
/-- Adding a codimension-one point `p` to `E` raises `χ(𝒪ₓ(E))` by `finrank k κ(p)`. -/
lemma eulerChar_add_step
    (hχ : ∀ E : AlgebraicCycle X ℤ, (sheaf E).HasEulerCharacteristic k)
    (hX : ∀ x : X, coheight x = 1 → ∀ y, y ≤ x → y = x)
    (E : AlgebraicCycle X ℤ) (hE : IsWeilDivisor E) {p : X} (hp : coheight p = 1) :
    (sheaf (E + single p 1)).eulerChar k =
      (sheaf E).eulerChar k + Module.finrank k (X.residueField p) :=
  eulerChar_step k hp (E + single p 1)
    (twistedClosedSubschemeComplex₂ (D := E) (D' := E + single p 1) hp (by simp))
    (twistedClosedSubschemeComplex₂_shortExact hE hp (by simp) (hX p hp))
    (hχ E) (hχ (E + single p 1))
    (hasEulerCharacteristic_residueLineSheaf k hp (E + single p 1)
      (fun n => finite_H_residueLineSheaf k hp (E + single p 1)
        (fun F => (hχ F).finite) (hX p hp) n))
    rfl

open Classical in
/-- Subtracting a codimension-one point `p` from `E` lowers `χ(𝒪ₓ(E))` by `finrank k κ(p)`. -/
lemma eulerChar_sub_step
    (hχ : ∀ E : AlgebraicCycle X ℤ, (sheaf E).HasEulerCharacteristic k)
    (hX : ∀ x : X, coheight x = 1 → ∀ y, y ≤ x → y = x)
    (E : AlgebraicCycle X ℤ) (hE : IsWeilDivisor E) {p : X} (hp : coheight p = 1) :
    (sheaf (E - single p 1)).eulerChar k =
      (sheaf E).eulerChar k - Module.finrank k (X.residueField p) := by
  have hkey : (sheaf E).eulerChar k =
      (sheaf (E - single p 1)).eulerChar k + Module.finrank k (X.residueField p) :=
    eulerChar_step k hp E
      (twistedClosedSubschemeComplex₁ (D := E) (D' := E - single p 1) hp (by simp))
      (twistedClosedSubschemeComplex₁_shortExact hE hp (by simp) (hX p hp))
      (hχ (E - single p 1)) (hχ E)
      (hasEulerCharacteristic_residueLineSheaf k hp E
        (fun n => finite_H_residueLineSheaf k hp E (fun F => (hχ F).finite) (hX p hp) n))
      rfl
  lia

/--
**Conditional Riemann-Roch**
If `X` is a curve over a field `k`, and every `𝒪ₓ(D)` has a well-defined Euler characteristic
(finite-dimensional cohomology which vanishes in all sufficiently large degrees), then for any
Weil divisor `D`, `χ(𝒪ₓ(D)) = deg D + χ(𝒪ₓ)`.
-/
theorem riemann_roch
    (hχ : ∀ E : AlgebraicCycle X ℤ, (sheaf E).HasEulerCharacteristic k)
    (hD : IsWeilDivisor D) [Order.KrullDimLE 1 X] :
    (sheaf D).eulerChar k =
      D.degree k + (sheaf (0 : AlgebraicCycle X ℤ)).eulerChar k := by
  classical
  have hX : ∀ x : X, coheight x = 1 → ∀ y, y ≤ x → y = x := fun x hx y hy =>
    have hmin : IsMin x :=
      Order.KrullDimLE.isMin_of_le_coheight (n := 1) (by simpa using hx.ge)
    ((Scheme.le_iff_specializes.mp (hmin hy)).antisymm (Scheme.le_iff_specializes.mp hy)).eq
  induction D, hD using Function.locallyFinsupp.inductionOn with
  | zero => simp [degree]
  | add E hE ih p hp =>
    have step := eulerChar_add_step k hχ hX E hE hp
    simp [step, ih]
    ring
  | minus E hE ih p hp =>
    have step := eulerChar_sub_step k hχ hX E hE hp
    simp [step, ih]
    ring

/-!
The above form of Riemann-Roch is admittedly slightly unsatisfying in terms of its assumptions. The
following are some (arguable) simplifications of the underlying assumptions which get us closer to
the form of the familiar result. I am not quite sure which of these I would say is the canonical
form of Riemann-Roch I have here (because of course the canonical thing is to not rephrase the
properness assumption).

We can use a similar argument to Riemann-Roch above to reduce the above assumptions to the case of
`𝒪ₓ(0)`. Namely, by induction on divisors `D`, and the following exact sequence
`0 → 𝒪ₓ(D) → 𝒪ₓ(D + P) → k(P) → 0`, which gives `H^n(𝒪ₓ(D)) → H^n(𝒪ₓ(D + P) → 0`, and so by
induction `h^n(𝒪ₓ(D + P))` is finite (the proof works the same for the other cases of the
induction). Note that for the `H^0` case, we get `0 → H^0(𝒪ₓ(D)) → H^0(𝒪ₓ(D + P)) → κ(P)`, for which
we need finiteness of `κ(P)` over `k`, meaning `X` needs to be finite type over `k`. Of course, this
is implied by a morphism being proper, but the fact that these assumptions which encapsulate
properness over k now split into more assumptions make it debatable whether this is a
simplification.

These reductions are carried out in
`Mathlib.AlgebraicGeometry.AlgebraicCycle.CohomologyReduction` (transfer of finiteness and
vanishing from `𝒪ₓ(0)` to every `𝒪ₓ(D)`),
`Mathlib.AlgebraicGeometry.AlgebraicCycle.StructureSheafIso` (the identification
`𝒪ₓ(0) ≅ 𝒪ₓ`) and `Mathlib.AlgebraicGeometry.AlgebraicCycle.ResidueFieldFinite` (finiteness
of residue fields at closed points, by Zariski's lemma); here we only assemble them into the
improved statements.
-/

open Classical in
/--
**Riemann–Roch from the structure sheaf.** Let `X` be a curve over `k` (integral, Noetherian,
regular in codimension one, of Krull dimension at most one) whose codimension-one residue
fields are finite over `k`. If `𝒪ₓ` has a well-defined Euler characteristic (`Hⁿ(X, 𝒪ₓ)` is
finite dimensional for every `n` and vanishes in all sufficiently large degrees), then for
every Weil divisor `D`, `χ(𝒪ₓ(D)) = deg D + χ(𝒪ₓ)`.

Here `𝒪ₓ` is the structure sheaf itself — the free rank-one sheaf of modules
`SheafOfModules.unit X.ringCatSheaf` — identified with the divisorial sheaf `𝒪ₓ(0)` by
`unitIsoSheafZero`.

For `X` proper over `k` the three hypotheses hold by the finiteness theorem for coherent
cohomology (EGA III 3.2.1), Grothendieck vanishing, and finiteness of residue fields at closed
points of schemes of finite type; none of these is yet available in Mathlib. For the
residue-field hypothesis see `riemann_roch_of_structureSheaf_of_locallyOfFiniteType`.
-/
theorem riemann_roch_of_structureSheaf [Order.KrullDimLE 1 X]
    (hκ : ∀ q : X, coheight q = 1 → Module.Finite k (X.residueField q))
    (hχ₀ : (structureSheafModule X).HasEulerCharacteristic k)
    (hD : IsWeilDivisor D) :
    (sheaf D).eulerChar k =
      D.degree k + (structureSheafModule X).eulerChar k := by
  have hf₀ := hχ₀.finite
  obtain ⟨N, hb₀⟩ := hχ₀.vanishing
  -- transport the hypotheses along `𝒪ₓ ≅ 𝒪ₓ(0)`
  have hf₀' : (sheaf (0 : AlgebraicCycle X ℤ)).HasFiniteCohomology k := fun n =>
    haveI := hf₀ n
    Module.Finite.equiv (hLinearEquivOfIso k (unitIsoSheafZero (X := X)) n)
  have hb₀' : ∀ n, N < n → Subsingleton ((sheaf (0 : AlgebraicCycle X ℤ)).H n) := fun n hn =>
    haveI := hb₀ n hn
    ((hLinearEquivOfIso k (unitIsoSheafZero (X := X)) n).symm.toEquiv).subsingleton
  rw [eulerChar_eq_of_iso k (unitIsoSheafZero (X := X))]
  have hX : ∀ x : X, coheight x = 1 → ∀ y, y ≤ x → y = x := fun x hx y hy =>
    have hmin : IsMin x :=
      Order.KrullDimLE.isMin_of_le_coheight (n := 1) (by simpa using hx.ge)
    ((Scheme.le_iff_specializes.mp (hmin hy)).antisymm (Scheme.le_iff_specializes.mp hy)).eq
  have hχ : ∀ E : AlgebraicCycle X ℤ, IsWeilDivisor E → (sheaf E).HasEulerCharacteristic k :=
    fun E hE => ⟨finite_H_sheaf_of_structureSheaf k hκ hf₀' hX hE, max N 1,
      subsingleton_H_sheaf_of_structureSheaf k hb₀' hX hE⟩
  induction D, hD using Function.locallyFinsupp.inductionOn with
  | zero => simp [degree]
  | add E hE ih p hp =>
    have hE' := Function.locallyFinsupp.support_add_single_subset hE hp
    have step : (sheaf (E + single p 1)).eulerChar k =
        (sheaf E).eulerChar k + Module.finrank k (X.residueField p) :=
      eulerChar_step k hp (E + single p 1)
      (twistedClosedSubschemeComplex₂ (D := E) (D' := E + single p 1) hp (by simp))
      (twistedClosedSubschemeComplex₂_shortExact hE hp (by simp) (hX p hp))
      (hχ E hE) (hχ (E + single p 1) hE')
      (hasEulerCharacteristic_residueLineSheaf k hp (E + single p 1)
        (fun n => finite_H_residueLineSheaf_of_finite_residueField k hp (E + single p 1)
          (hκ p hp) n))
      rfl
    simp [step, ih]
    ring
  | minus E hE ih p hp =>
    have hE' := Function.locallyFinsupp.support_sub_single_subset hE hp
    have hkey : (sheaf E).eulerChar k =
        (sheaf (E - single p 1)).eulerChar k + Module.finrank k (X.residueField p) :=
      eulerChar_step k hp E
      (twistedClosedSubschemeComplex₁ (D := E) (D' := E - single p 1) hp (by simp))
      (twistedClosedSubschemeComplex₁_shortExact hE hp (by simp) (hX p hp))
      (hχ (E - single p 1) hE') (hχ E hE)
      (hasEulerCharacteristic_residueLineSheaf k hp E
        (fun n => finite_H_residueLineSheaf_of_finite_residueField k hp E (hκ p hp) n))
      rfl
    have step : (sheaf (E - single p 1)).eulerChar k =
        (sheaf E).eulerChar k - Module.finrank k (X.residueField p) := by lia
    simp [step, ih]
    ring


theorem riemann_roch_of_structureSheaf_of_locallyOfFiniteType
    [Order.KrullDimLE 1 X] [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k))]
    (hχ₀ : (structureSheafModule X).HasEulerCharacteristic k)
    (hD : IsWeilDivisor D) :
    (sheaf D).eulerChar k =
      D.degree k + (structureSheafModule X).eulerChar k :=
  riemann_roch_of_structureSheaf k D
    (fun _ hq => finite_residueField_of_isClosed k (isClosed_singleton_of_coheight_eq_one hq))
    hχ₀ hD

end AlgebraicGeometry.AlgebraicCycle.SheafViaSubmodule
