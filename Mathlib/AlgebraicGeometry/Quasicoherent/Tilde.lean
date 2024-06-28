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

-/

open TopCat AlgebraicGeometry TopologicalSpace CategoryTheory Opposite

variable (R: Type) [CommRing R] (M: Type) [AddCommGroup M] [Module R M]

namespace Tilde

/--p-->M_p-/
abbrev Localizations (P: PrimeSpectrum.Top R) : Type :=
LocalizedModule P.asIdeal.primeCompl M

/--a section is globally a fraction m/s-/
def IsFraction {U : Opens (PrimeSpectrum.Top R)} (f : ∀ ℘ : U, Localizations R M ℘) : Prop :=
  ∃ (m: M) (s: R), ∀ x : U, ¬s ∈ x.1.asIdeal ∧ s •
    f x = LocalizedModule.mkLinearMap x.1.asIdeal.primeCompl M m

def isFractionPrelocal : PrelocalPredicate (Localizations R M) where
  pred {U} f := IsFraction R M f
  res := by rintro V U i f ⟨m, s, w⟩; exact ⟨m, s, fun x => w (i x)⟩

/--a section is locally a fraction-/
def isLocallyFraction : LocalPredicate (Localizations R M) := (isFractionPrelocal R M).sheafify

end Tilde

def TildeInType : Sheaf (Type) (PrimeSpectrum.Top R):=subsheafToTypes (Tilde.isLocallyFraction R M)

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

-- def sectionsAddSubgroup (U : (Opens (PrimeSpectrum.Top R))ᵒᵖ) :
--     AddSubgroup (∀ x : U.unop, Localizations R M x) where
--   carrier := { f | (isLocallyFraction R M).pred f }
--   zero_mem' := by
--     refine fun x => ⟨unop U, x.2, 𝟙 _, 0, 1, fun y => ⟨?_, ?_⟩⟩
--     · rw [← Ideal.ne_top_iff_one]; exact y.1.isPrime.1
--     · simp
--   add_mem' := by
--     intro a b ha hb x
--     rcases ha x with ⟨Va, ma, ia, ra, sa, wa⟩
--     rcases hb x with ⟨Vb, mb, ib, rb, sb, wb⟩
--     refine ⟨Va ⊓ Vb, ⟨ma, mb⟩, Opens.infLELeft _ _ ≫ ia,  sb• ra+ sa•rb , sa * sb, ?_⟩
--     intro y
--     rcases wa (Opens.infLELeft _ _ y) with ⟨nma, wa⟩
--     rcases wb (Opens.infLERight _ _ y) with ⟨nmb, wb⟩
--     fconstructor
--     · intro H; cases y.1.isPrime.mem_or_mem H <;> contradiction
--     · simp only [Opens.coe_inf, Pi.add_apply, smul_add, map_add, LinearMapClass.map_smul]
--       erw [← wa, ← wb]
--       dsimp
--       rw [← smul_assoc,← smul_assoc]
--       congr 2
--       simp [mul_comm]
--   neg_mem' := by
--     intro a ha x
--     rcases ha x with ⟨V, m, i, r, s, w⟩
--     refine ⟨V, m, i, -r, s, ?_⟩
--     intro y
--     rcases w y with ⟨nm, w⟩
--     fconstructor
--     · exact nm
--     · simp only [Pi.neg_apply, smul_neg, map_neg, neg_inj]
--       erw [← w]

/--M_x is an O_SpecR(U)-module when x is in U-/
noncomputable instance (U : (Opens (PrimeSpectrum.Top R))ᵒᵖ) (x : U.unop):
    Module ((Spec.structureSheaf R).val.obj U) (Localizations R M ↑x):=
  Module.compHom (R := (Localization.AtPrime x.1.asIdeal)) _
    (StructureSheaf.openToLocalization R U.unop x x.2 :
      (Spec.structureSheaf R).val.obj U →+* Localization.AtPrime x.1.asIdeal)

lemma smul_def (U : (Opens (PrimeSpectrum.Top R))ᵒᵖ) (x : U.unop)
    (r : (Spec.structureSheaf R).val.obj U)
    (m : Localizations R M ↑x) :
  r • m = r.1 x • m := rfl

/--M(U) is a O(U)-submodule of Π M_x-/
def sectionsSubmodule (U : (Opens (PrimeSpectrum.Top R))ᵒᵖ) :
    Submodule ((Spec.structureSheaf R).1.obj U) (∀ x : U.unop, Localizations R M x) where
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
    rcases wa (Opens.infLELeft _ _ y) with ⟨nma, wa⟩
    rcases wb (Opens.infLERight _ _ y) with ⟨nmb, wb⟩
    fconstructor
    · intro H; cases y.1.isPrime.mem_or_mem H <;> contradiction
    · simp only [Opens.coe_inf, Pi.add_apply, smul_add, map_add, LinearMapClass.map_smul]
      erw [← wa, ← wb]
      dsimp
      rw [← smul_assoc,← smul_assoc]
      congr 2
      simp [mul_comm]
  smul_mem' := by
    intro r a ha x
    rcases ha x with ⟨Va, ma, ia, ra, sa, wa⟩
    rcases r.2 x with ⟨Vr, mr, ir, rr, sr, wr⟩
    refine ⟨Va ⊓ Vr, ⟨ma, mr⟩, Opens.infLELeft _ _ ≫ ia, rr•ra, sr*sa, ?_⟩
    intro y
    rcases wa (Opens.infLELeft _ _ y) with ⟨nma, wa⟩
    rcases wr (Opens.infLERight _ _ y) with ⟨nmr, wr⟩
    fconstructor
    · intro H; cases y.1.isPrime.mem_or_mem H <;> contradiction
    · simp only [Opens.coe_inf, Pi.smul_apply, LinearMapClass.map_smul]
      dsimp at wa wr ⊢
      rw[smul_def]
      erw [← wa]
      rw [← smul_assoc,← smul_assoc]
      congr 2
      simp [mul_comm]
      erw [← wr]
      erw [mul_left_comm,← RingHom.map_mul]
      conv_rhs => rw [mul_comm]
      rw [Algebra.smul_def]
      rfl

instance (U : (Opens (PrimeSpectrum.Top R))ᵒᵖ) :
    AddCommGroup ((TildeInType R M).1.obj U) :=
  inferInstanceAs $ AddCommGroup (sectionsSubmodule R M U)

def PresheafInAddCommGrp : Presheaf AddCommGrp (PrimeSpectrum.Top R) where
  obj U := AddCommGrp.of ((TildeInType R M).1.obj U)
  map {U V} i :=
    { toFun := (TildeInType R M).1.map i
      map_zero' := rfl
      map_add' := fun x y => rfl}

def PresheafCompForget :
    PresheafInAddCommGrp R M ⋙ forget AddCommGrp ≅ (TildeInType R M).1 :=
  NatIso.ofComponents fun U => Iso.refl _

def TildeInAddCommGrp : Sheaf AddCommGrp (PrimeSpectrum.Top R) :=
  ⟨PresheafInAddCommGrp R M,
    (-- We check the sheaf condition under `forget CommRingCat`.
          TopCat.Presheaf.isSheaf_iff_isSheaf_comp
          _ _).mpr
      (TopCat.Presheaf.isSheaf_of_iso (PresheafCompForget R M).symm (TildeInType R M).cond)⟩

/--sheaf of comm ring--sheaf of ring>-/
def forget2Ring :=
  sheafCompose (Opens.grothendieckTopology (PrimeSpectrum.Top R))
    (forget₂ CommRingCat RingCat) |>.obj (Spec.structureSheaf R)

noncomputable instance (U : (Opens (PrimeSpectrum.Top R))ᵒᵖ) :
    Module ((forget2Ring R).val.obj U) ((PresheafInAddCommGrp R M).obj U) :=
  inferInstanceAs $ Module _ (sectionsSubmodule R M U)

noncomputable def TildeInModules : SheafOfModules (forget2Ring R) where
  val := {
    presheaf := (PresheafInAddCommGrp R M)
    module := inferInstance
    map_smul := by
      intro U V f r m
      dsimp [TildeInAddCommGrp, PresheafInAddCommGrp, TildeInType]
      rw [Subtype.ext_iff]
      ext x
      dsimp [subpresheafToTypes]
      simp only [forget2Ring, sheafCompose_obj_val, Functor.comp_obj, Functor.comp_map] at r ⊢
      change (Spec.structureSheaf R).val.obj U at r
      change r • (m.1 ⟨x.1, _⟩) = _
      rw [smul_def]
      rfl
  }
  isSheaf := (TildeInAddCommGrp R M).2

noncomputable def structurePresheafCompForget :
    (TildeInModules R M).val.presheaf ≅ (TildeInAddCommGrp R M).1 :=
  NatIso.ofComponents fun U => Iso.refl _

-- Todo: the isomorphism between the stalk of TildeInModules R M at x and the localization of
-- M at x.

end Tilde
