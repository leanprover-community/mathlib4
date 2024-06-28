/-
Copyright (c) 2024 Weihong Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weihong Xu
-/

import Mathlib.AlgebraicGeometry.Spec
import Mathlib.Algebra.Category.ModuleCat.Sheaf

/-!

# Construction of M^~

Given any commutative ring `R` and `R`-module `M`, we construct the sheaf `M^~` of `𝒪_SpecR`-modules
such that `M^~(U)` is the set of dependent functions that are locally fractions.

## Main definitions

* `AlgebraicGeometry.TildeInAddCommGrp` : `M^~` as a sheaf of abelian groups.
* `AlgebraicGeometry.TildeInModules` : `M^~` as a sheaf of `𝒪_{Spec R}`-modules.

-/

universe u

open TopCat AlgebraicGeometry TopologicalSpace CategoryTheory Opposite

variable (R : Type u) [CommRing R] (M : Type u) [AddCommGroup M] [Module R M]

namespace AlgebraicGeometry

namespace Tilde

/-- For an `R`-module `M` and a point `P` in `Spec R`, `Localizations P` is the localized module
`M` at the prime ideal `P`. -/
abbrev Localizations (P : PrimeSpectrum.Top R) :=
LocalizedModule P.asIdeal.primeCompl M

/-- For any open subset `U ⊆ Spec R`, `IsFraction` is the predicate expressing that a function
`f : ∏_{x ∈ U}, Mₓ` is such that for any `𝔭 ∈ U`, `f 𝔭 = m / s` for some `m : M` and `s ∉ 𝔭`.
In short `f` is a fraction on `U`. -/
def IsFraction {U : Opens (PrimeSpectrum R)} (f : ∀ 𝔭 : U, Localizations R M 𝔭.1) : Prop :=
  ∃ (m : M) (s : R),
    ∀ x : U, ¬s ∈ x.1.asIdeal ∧ s • f x = LocalizedModule.mkLinearMap x.1.asIdeal.primeCompl M m

/--
The property of a function `f : ∏_{x ∈ U}, Mₓ` being a fraction is stable under restriction.
-/
def isFractionPrelocal : PrelocalPredicate (Localizations R M) where
  pred {U} f := IsFraction R M f
  res := by rintro V U i f ⟨m, s, w⟩; exact ⟨m, s, fun x => w (i x)⟩

/--
For any open subset `U ⊆ Spec R`, `IsLocallyFraction` is the predicate expressing that a function
`f : ∏_{x ∈ U}, Mₓ` is such that for any `𝔭 ∈ U`, there exists an open neighbourhood `V ∋ 𝔭`, such
that for any `𝔮 ∈ V`, `f 𝔮 = m / s` for some `m : M` and `s ∉ 𝔮`.
In short `f` is locally a fraction on `U`.
-/
def isLocallyFraction : LocalPredicate (Localizations R M) := (isFractionPrelocal R M).sheafify

end Tilde

/--
For any `R`-module `M`, `TildeInType R M` is the sheaf of set on `Spec R` whose sections on `U` are
the dependent functions that are locally fractions. This is often denoted by `M^~`.

See also `Tilde.isLocallyFraction`.
-/
def TildeInType : Sheaf (Type u) (PrimeSpectrum.Top R) :=
  subsheafToTypes (Tilde.isLocallyFraction R M)

namespace Tilde

@[simp]
theorem isLocallyFraction_pred {U : Opens (PrimeSpectrum.Top R)}
    (f : ∀ x : U, Localizations R M x) :
    (isLocallyFraction R M).pred f =
      ∀ y : U,
        ∃ (V : _) (_ : y.1 ∈ V) (i : V ⟶ U),
          ∃ (m: M) (s: R), ∀ x : V, ¬s ∈ x.1.asIdeal ∧ s• f (i x) =
            LocalizedModule.mkLinearMap x.1.asIdeal.primeCompl M m :=
  rfl

/- M_x is an O_SpecR(U)-module when x is in U -/
noncomputable instance (U : (Opens (PrimeSpectrum.Top R))ᵒᵖ) (x : U.unop):
    Module ((Spec.structureSheaf R).val.obj U) (Localizations R M ↑x):=
  Module.compHom (R := (Localization.AtPrime x.1.asIdeal)) _
    (StructureSheaf.openToLocalization R U.unop x x.2 :
      (Spec.structureSheaf R).val.obj U →+* Localization.AtPrime x.1.asIdeal)

lemma sections_smul_localizations_def (U : (Opens (PrimeSpectrum.Top R))ᵒᵖ) (x : U.unop)
    (r : (Spec.structureSheaf R).val.obj U)
    (m : Localizations R M ↑x) :
  r • m = r.1 x • m := rfl

/--
For any `R`-module `M` and any open subset `U ⊆ Spec R`, `M^~(U)` is an `𝒪_{Spec R}(U)`-submodule
of `∏_{𝔭 ∈ U} M_𝔭`. -/
def sectionsSubmodule (U : (Opens (PrimeSpectrum R))ᵒᵖ) :
    Submodule ((Spec.structureSheaf R).1.obj U) (∀ x : U.unop, Localizations R M x.1) where
  carrier := { f | (isLocallyFraction R M).pred f }
  zero_mem' := by
    refine fun x => ⟨unop U, x.2, 𝟙 _, 0, 1, fun y => ⟨?_, ?_⟩⟩
    · rw [← Ideal.ne_top_iff_one]; exact y.1.isPrime.1
    · simp
  add_mem' := by
    intro a b ha hb x
    rcases ha x with ⟨Va, ma, ia, ra, sa, wa⟩
    rcases hb x with ⟨Vb, mb, ib, rb, sb, wb⟩
    refine ⟨Va ⊓ Vb, ⟨ma, mb⟩, Opens.infLELeft _ _ ≫ ia,  sb• ra+ sa•rb , sa * sb, ?_⟩
    intro y
    rcases wa (Opens.infLELeft _ _ y : Va) with ⟨nma, wa⟩
    rcases wb (Opens.infLERight _ _ y : Vb) with ⟨nmb, wb⟩
    fconstructor
    · intro H; cases y.1.isPrime.mem_or_mem H <;> contradiction
    · simp only [Opens.coe_inf, Pi.add_apply, smul_add, map_add, LinearMapClass.map_smul]
      dsimp at wa wb ⊢
      rw [← wa, ← wb, ← mul_smul, ← mul_smul]
      congr 2
      simp [mul_comm]
  smul_mem' := by
    intro r a ha x
    rcases ha x with ⟨Va, ma, ia, ra, sa, wa⟩
    rcases r.2 x with ⟨Vr, mr, ir, rr, sr, wr⟩
    refine ⟨Va ⊓ Vr, ⟨ma, mr⟩, Opens.infLELeft _ _ ≫ ia, rr•ra, sr*sa, ?_⟩
    intro y
    rcases wa (Opens.infLELeft _ _ y : Va) with ⟨nma, wa⟩
    rcases wr (Opens.infLERight _ _ y) with ⟨nmr, wr⟩
    fconstructor
    · intro H; cases y.1.isPrime.mem_or_mem H <;> contradiction
    · simp only [Opens.coe_inf, Pi.smul_apply, LinearMapClass.map_smul]
      dsimp at wa wr ⊢
      rw [mul_comm, ← Algebra.smul_def] at wr
      rw [sections_smul_localizations_def, ← wa, ← mul_smul, ← smul_assoc, mul_comm sr,
        mul_smul, wr, mul_comm rr, Algebra.smul_def, ← map_mul]
      rfl

instance (U : (Opens (PrimeSpectrum.Top R))ᵒᵖ) :
    AddCommGroup ((TildeInType R M).1.obj U) :=
  inferInstanceAs $ AddCommGroup (sectionsSubmodule R M U)

/--
`M^~` as a presheaf of abelian groups over `Spec R`
-/
def presheafInAddCommGrp : Presheaf AddCommGrp (PrimeSpectrum.Top R) where
  obj U := AddCommGrp.of ((TildeInType R M).1.obj U)
  map {U V} i :=
    { toFun := (TildeInType R M).1.map i
      map_zero' := rfl
      map_add' := fun x y => rfl}

/--
Implementation details:
checking that after forgeting the abelian group structure of `M^~` as sheaf of abelian groups, we
get the original sheaf of sets.
-/
def presheafCompForget :
    presheafInAddCommGrp R M ⋙ forget AddCommGrp ≅ (TildeInType R M).1 :=
  NatIso.ofComponents fun U => Iso.refl _

end Tilde

/--
`M^~` as a sheaf of abelian groups over `Spec R`
-/
def TildeInAddCommGrp : Sheaf AddCommGrp (PrimeSpectrum.Top R) :=
  ⟨Tilde.presheafInAddCommGrp R M,
    (TopCat.Presheaf.isSheaf_iff_isSheaf_comp _ _).mpr
      (TopCat.Presheaf.isSheaf_of_iso (Tilde.presheafCompForget R M).symm (TildeInType R M).cond)⟩

-- `SheafOfModules` want `Sheaf ... RingCat`; but we have a `Sheaf ... CommRingCat`, so we forget.
local notation3 "𝒪_SpecR" =>
  sheafCompose (Opens.grothendieckTopology (PrimeSpectrum.Top R))
    (forget₂ CommRingCat RingCat) |>.obj (Spec.structureSheaf R)

noncomputable instance (U : (Opens (PrimeSpectrum.Top R))ᵒᵖ) :
    Module ((𝒪_SpecR).val.obj U) ((Tilde.presheafInAddCommGrp R M).obj U) :=
  inferInstanceAs $ Module _ (Tilde.sectionsSubmodule R M U)

open Tilde in
/--
`M^~` as a sheaf of `𝒪_{Spec R}`-modules
-/
noncomputable def TildeInModules : SheafOfModules (𝒪_SpecR) where
  val := {
    presheaf := (presheafInAddCommGrp R M)
    module := inferInstance
    map_smul := by
      intro U V f r m
      dsimp [TildeInAddCommGrp, presheafInAddCommGrp, TildeInType]
      ext x
      change (Spec.structureSheaf R).val.obj U at r
      change r • (m.1 ⟨x.1, _⟩) = _
      rw [sections_smul_localizations_def]
      rfl
  }
  isSheaf := (TildeInAddCommGrp R M).2

end AlgebraicGeometry
