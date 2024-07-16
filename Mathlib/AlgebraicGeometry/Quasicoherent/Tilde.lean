/-
Copyright (c) 2024 Weihong Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Johan Commelin, Amelia Livingston, Sophie Morel, Jujian Zhang, Weihong Xu
-/

import Mathlib.Algebra.Module.LocalizedModule
import Mathlib.AlgebraicGeometry.StructureSheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits

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

noncomputable instance (U : (Opens (PrimeSpectrum.Top R))ᵒᵖ) :
    Module ((Spec.structureSheaf R).1.obj U) ((Tilde.presheafInAddCommGrp R M).obj U) :=
  inferInstanceAs $ Module _ (Tilde.sectionsSubmodule R M U)

open Tilde in
/--
`M^~` as a sheaf of `𝒪_{Spec R}`-modules
-/
noncomputable def TildeAsSheafOfModules : SheafOfModules (𝒪_SpecR) where
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

noncomputable def TildeInModuleCat :
    TopCat.Presheaf (ModuleCat R) (PrimeSpectrum.Top R) :=
  (PresheafOfModules.forgetToPresheafModuleCat (op ⊤) $
    Limits.initialOpOfTerminal Limits.isTerminalTop).obj (TildeAsSheafOfModules R M).1 ⋙
  ModuleCat.restrictScalars (StructureSheaf.globalSectionsIso R).hom

namespace Tilde

@[simp]
theorem res_apply (U V : Opens (PrimeSpectrum.Top R)) (i : V ⟶ U)
    (s : (TildeInModuleCat R M).obj (op U)) (x : V) :
    ((TildeInModuleCat R M).map i.op s).1 x = (s.1 (i x) : _) :=
  rfl

lemma smul_section_apply (r : R) (U : Opens (PrimeSpectrum.Top R))
    (s : (TildeInModuleCat R M).1.obj (op U)) (x : U) :
    (r • s).1 x = r • (s.1 x) := rfl

lemma smul_germ (r : R) (U : Opens (PrimeSpectrum.Top R)) (x : U)
    (s : (TildeInModuleCat R M).1.obj (op U)) :
    r • (TildeInModuleCat R M).germ x s =
    (TildeInModuleCat R M).germ x (r • s) := by rw [map_smul]

/-- The ring homomorphism that takes a section of the structure sheaf of `R` on the open set `U`,
implemented as a subtype of dependent functions to localizations at prime ideals, and evaluates
the section on the point corresponding to a given prime ideal. -/
def openToLocalization (U : Opens (PrimeSpectrum.Top R)) (x : PrimeSpectrum.Top R) (hx : x ∈ U) :
    (TildeInModuleCat R M).1.obj (op U) ⟶
    ModuleCat.of R (LocalizedModule x.asIdeal.primeCompl M) where
  toFun s := (s.1 ⟨x, hx⟩ : _)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem coe_openToLocalization (U : Opens (PrimeSpectrum.Top R)) (x : PrimeSpectrum.Top R)
    (hx : x ∈ U) :
    (openToLocalization R M U x hx :
        (TildeInAddCommGrp R M).1.obj (op U) → LocalizedModule x.asIdeal.primeCompl M) =
      fun s => (s.1 ⟨x, hx⟩ : _) :=
  rfl

theorem openToLocalization_apply (U : Opens (PrimeSpectrum.Top R)) (x : PrimeSpectrum.Top R)
    (hx : x ∈ U) (s : (TildeInAddCommGrp R M).1.obj (op U)) :
    openToLocalization R M U x hx s = (s.1 ⟨x, hx⟩ : _) :=
  rfl

noncomputable def stalkToFiberLinearMap (x : PrimeSpectrum.Top R) :
    TopCat.Presheaf.stalk (TildeInModuleCat R M) x ⟶
    ModuleCat.of R (LocalizedModule x.asIdeal.primeCompl M) :=
  Limits.colimit.desc ((OpenNhds.inclusion x).op ⋙ (TildeInModuleCat R M))
    { pt := _
      ι :=
      { app := fun U =>
          (openToLocalization R M ((OpenNhds.inclusion _).obj (unop U)) x (unop U).2)
        naturality := fun {U V} i => by aesop_cat } }

@[simp]
theorem germ_comp_stalkToFiberLinearMap (U : Opens (PrimeSpectrum.Top R)) (x : U) :
    TopCat.Presheaf.germ (TildeInModuleCat R M) x ≫ stalkToFiberLinearMap R M x =
    openToLocalization R M U x x.2 :=
  Limits.colimit.ι_desc _ _

@[simp]
theorem stalkToFiberLinearMap_germ' (U : Opens (PrimeSpectrum.Top R)) (x : PrimeSpectrum.Top R)
    (hx : x ∈ U) (s : (TildeInModuleCat R M).1.obj (op U)) :
    stalkToFiberLinearMap R M x
      (TopCat.Presheaf.germ (TildeInModuleCat R M) ⟨x, hx⟩ s) = (s.1 ⟨x, hx⟩ : _) :=
  DFunLike.ext_iff.1 (germ_comp_stalkToFiberLinearMap R M U ⟨x, hx⟩ : _) s

@[simp]
theorem stalkToFiberLinearMap_germ (U : Opens (PrimeSpectrum.Top R)) (x : U)
    (s : (TildeInModuleCat R M).1.obj (op U)) :
    stalkToFiberLinearMap R M x (TopCat.Presheaf.germ (TildeInModuleCat R M) x s) =
    s.1 x := by
  cases x; exact stalkToFiberLinearMap_germ' R M U _ _ _

def toOpen (U : Opens (PrimeSpectrum.Top R)) :
    ModuleCat.of R M ⟶ (TildeInModuleCat R M).1.obj (op U) where
  toFun f :=
  ⟨fun x => LocalizedModule.mkLinearMap _ _ f, fun x =>
    ⟨U, x.2, 𝟙 _, f, 1, fun y => ⟨(Ideal.ne_top_iff_one _).1 y.1.2.1, by simp⟩⟩⟩
  map_add' f g := Subtype.eq <| funext fun x => LinearMap.map_add _ _ _
  map_smul' r m := by
    simp only [isLocallyFraction_pred, LocalizedModule.mkLinearMap_apply, LinearMapClass.map_smul,
      RingHom.id_apply]
    rfl

@[simp]
theorem toOpen_res (U V : Opens (PrimeSpectrum.Top R)) (i : V ⟶ U) :
    toOpen R M U ≫ (TildeInModuleCat R M).map i.op = toOpen R M V :=
  rfl

noncomputable def toStalk (x : PrimeSpectrum.Top R) :
    ModuleCat.of R M ⟶ TopCat.Presheaf.stalk (TildeInModuleCat R M) x :=
  (toOpen R M ⊤ ≫ TopCat.Presheaf.germ (TildeInModuleCat R M) ⟨x, by trivial⟩)

@[simp]
theorem toOpen_germ (U : Opens (PrimeSpectrum.Top R)) (x : U) :
    toOpen R M U ≫ TopCat.Presheaf.germ (TildeInModuleCat R M) x = toStalk R M x := by
  rw [← toOpen_res R M ⊤ U (homOfLE le_top : U ⟶ ⊤), Category.assoc, Presheaf.germ_res]; rfl

@[simp]
theorem germ_toOpen (U : Opens (PrimeSpectrum.Top R)) (x : U) (f : M) :
    TopCat.Presheaf.germ (TildeInModuleCat R M) x
      (toOpen R M U f) = toStalk R M x f := by rw [← toOpen_germ]; rfl

lemma isUnit_toStalk (x : PrimeSpectrum.Top R) (r : x.asIdeal.primeCompl) :
    IsUnit ((algebraMap R (Module.End R ((TildeInModuleCat R M).stalk x))) r) := by
  rw [Module.End_isUnit_iff]
  refine ⟨?_, ?_⟩
  · rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro st h
    simp only [LinearMap.mem_ker, Module.algebraMap_end_apply] at h
    change st = 0
    obtain ⟨U, mem, s, rfl⟩ := TopCat.Presheaf.germ_exist (F := (TildeInModuleCat R M)) x st
    erw [smul_germ] at h
    rw [show (0 : (TildeInModuleCat R M).stalk x) = (TildeInModuleCat R M).germ ⟨x, mem⟩ 0 by
      rw [map_zero]] at h

    obtain ⟨W, mem_W, iU, iV, h⟩ := TopCat.Presheaf.germ_eq (h := h)
    rw [map_smul, map_zero] at h
    obtain ⟨W', (mem_W' : x ∈ W'), (iW : W' ⟶ W), num, den, eq1⟩ :=
      ((TildeInModuleCat R M).map iU.op) s |>.2 ⟨x, mem_W⟩
    let O := W' ⊓ (PrimeSpectrum.basicOpen r)
    suffices (TildeInModuleCat R M).map
        (op $ (homOfLE $ inf_le_left.trans (leOfHom $ iW ≫ iU) : O ⟶ U)) s = 0 by
      apply_fun (TildeInModuleCat R M).germ
        (⟨x, ⟨mem_W', r.2⟩⟩ : (W' ⊓ PrimeSpectrum.basicOpen r.1 : Opens _)) at this
      erw [TopCat.Presheaf.germ_res_apply] at this
      rw [this, map_zero]

    refine Subtype.ext $ funext fun q => show _ = 0 from ?_
    obtain ⟨_, eq1⟩ := eq1 ⟨q.1, q.2.1⟩
    simp only [isLocallyFraction_pred, LocalizedModule.mkLinearMap_apply, res_apply] at eq1
    change s.1 ⟨q, _⟩ = 0
    apply_fun (TildeInModuleCat R M).map (op iW) at h
    rw [map_smul] at h
    replace h := congr_fun (Subtype.ext_iff.1 h) ⟨q.1, q.2.1⟩
    change r.1 • s.1 ⟨q.1, _⟩ = 0 at h
    set x := s.1 ⟨q.1, _⟩
    clear_value x
    induction x using LocalizedModule.induction_on with
    | h a b =>
      rw [LocalizedModule.smul'_mk, show (0 : Localizations R M q) = LocalizedModule.mk 0 1 by rfl,
        LocalizedModule.mk_eq] at h
      obtain ⟨(c : q.1.asIdeal.primeCompl), hc⟩ := h
      simp only [Quiver.Hom.unop_op', one_smul, smul_zero] at hc
      rw [show (0 : Localizations R M q) = LocalizedModule.mk 0 1 by rfl, LocalizedModule.mk_eq]
      refine ⟨c * ⟨r, q.2.2⟩, ?_⟩
      simp only [Quiver.Hom.unop_op', one_smul, smul_zero, mul_smul]
      exact hc

  · intro st
    obtain ⟨U, mem, s, rfl⟩ := TopCat.Presheaf.germ_exist (F := (TildeInModuleCat R M)) x st
    let O := U ⊓ (PrimeSpectrum.basicOpen r)
    have mem_O : x ∈ O := ⟨mem, r.2⟩
    refine ⟨TopCat.Presheaf.germ (TildeInModuleCat R M) ⟨x, mem_O⟩
      ⟨fun q => (Localization.mk 1 ⟨r, q.2.2⟩ : Localization.AtPrime q.1.asIdeal) • s.1
        ⟨q.1, q.2.1⟩, fun q => ?_⟩, ?_⟩
    · obtain ⟨V, mem_V, (iV : V ⟶ U), num, den, hV⟩ := s.2 ⟨q.1, q.2.1⟩
      refine ⟨V ⊓ O, ⟨mem_V, q.2⟩, homOfLE inf_le_right, num, r * den, fun y => ?_⟩
      obtain ⟨h1, h2⟩ := hV ⟨y, y.2.1⟩
      refine ⟨y.1.asIdeal.primeCompl.mul_mem y.2.2.2 h1, ?_⟩
      simp only [Opens.coe_inf, isLocallyFraction_pred, LocalizedModule.mkLinearMap_apply] at h2 ⊢
      set x := s.1 ⟨y.1, _⟩
      clear_value x
      induction x using LocalizedModule.induction_on with
      | h a b =>
      rw [LocalizedModule.mk_smul_mk, one_smul, LocalizedModule.smul'_mk, ← h2,
        LocalizedModule.smul'_mk, LocalizedModule.mk_eq]
      refine ⟨1, ?_⟩
      simp only [one_smul]
      rw [mul_comm _ b, mul_smul, mul_smul]
      rfl
    · simp only [isLocallyFraction_pred, LocalizedModule.mkLinearMap_apply,
        Module.algebraMap_end_apply]
      rw [← map_smul]
      fapply TopCat.Presheaf.germ_ext
      · exact O
      · exact mem_O
      · exact 𝟙 _
      · exact homOfLE inf_le_left
      refine Subtype.eq <| funext fun y => ?_
      simp only [isLocallyFraction_pred, LocalizedModule.mkLinearMap_apply, op_id,
        CategoryTheory.Functor.map_id, LinearMapClass.map_smul,
        id_apply]
      rw [smul_section_apply]
      change _ = s.1 ⟨y.1, _⟩
      set x := s.1 ⟨y.1, _⟩
      change r.1 • Localization.mk 1 _ • x = _
      clear_value x

      induction x using LocalizedModule.induction_on with
      | h a b =>
        rw [LocalizedModule.mk_smul_mk, one_smul, LocalizedModule.smul'_mk, LocalizedModule.mk_eq]
        refine ⟨1, ?_⟩
        simp only [one_smul]
        rw [mul_comm _ b, mul_smul]
        rfl

noncomputable def localizationToStalk (x : PrimeSpectrum.Top R) :
    ModuleCat.of R (LocalizedModule x.asIdeal.primeCompl M) ⟶
    (TopCat.Presheaf.stalk (TildeInModuleCat R M) x) :=
  LocalizedModule.lift _ (toStalk R M x) $ isUnit_toStalk R M x

@[simp]
theorem toStalk_comp_stalkToFiberLinearMap (x : PrimeSpectrum.Top R) :
    -- Porting note: now `algebraMap _ _` needs to be explicitly typed
    toStalk R M x ≫ stalkToFiberLinearMap R M x =
    LocalizedModule.mkLinearMap x.asIdeal.primeCompl M := by
  erw [toStalk, Category.assoc, germ_comp_stalkToFiberLinearMap]; rfl

@[simp]
theorem stalkToFiberRingHom_toStalk (x : PrimeSpectrum.Top R) (m : M) :
    stalkToFiberLinearMap R M x (toStalk R M x m) =
    LocalizedModule.mk m 1 :=
  LinearMap.ext_iff.1 (toStalk_comp_stalkToFiberLinearMap R M x) _

def const (m : M) (r : R) (U : Opens (PrimeSpectrum.Top R))
    (hu : ∀ x ∈ U, r ∈ (x : PrimeSpectrum.Top R).asIdeal.primeCompl) :
    (TildeInModuleCat R M).obj (op U) :=
  ⟨fun x => LocalizedModule.mk m ⟨r, hu x x.2⟩, fun x =>
    ⟨U, x.2, 𝟙 _, m, r, fun y => ⟨hu _ y.2, by
      simp only [LocalizedModule.mkLinearMap_apply, LocalizedModule.smul'_mk]
      rw [LocalizedModule.mk_eq]
      exact ⟨1, by simp⟩⟩⟩⟩

@[simp]
theorem const_apply (m : M) (r : R) (U : Opens (PrimeSpectrum.Top R))
    (hu : ∀ x ∈ U, r ∈ (x : PrimeSpectrum.Top R).asIdeal.primeCompl) (x : U) :
    (const R M m r U hu).1 x = LocalizedModule.mk m ⟨r, hu x x.2⟩ :=
  rfl

theorem const_apply' (m : M) (r : R) (U : Opens (PrimeSpectrum.Top R))
    (hu : ∀ x ∈ U, r ∈ (x : PrimeSpectrum.Top R).asIdeal.primeCompl) (x : U)
    (hx : r ∈ (x : PrimeSpectrum.Top R).asIdeal.primeCompl) :
    (const R M m r U hu).1 x = LocalizedModule.mk m ⟨r, hx⟩ :=
  rfl

theorem exists_const (U) (s : (TildeInModuleCat R M).obj (op U)) (x : PrimeSpectrum.Top R)
    (hx : x ∈ U) :
    ∃ (V : Opens (PrimeSpectrum.Top R)) (_ : x ∈ V) (i : V ⟶ U) (f : M) (g : R) (hg : _),
      const R M f g V hg = (TildeInModuleCat R M).map i.op s :=
  let ⟨V, hxV, iVU, f, g, hfg⟩ := s.2 ⟨x, hx⟩
  ⟨V, hxV, iVU, f, g, fun y hyV => (hfg ⟨y, hyV⟩).1,
    Subtype.eq <| funext fun y => by
    simp only [isLocallyFraction_pred, LocalizedModule.mkLinearMap_apply, const_apply, res_apply]
    obtain ⟨h1, (h2 : g • s.1 ⟨y, _⟩ = LocalizedModule.mk f 1)⟩ := hfg y
    replace h2 : s.1 (iVU y) = LocalizedModule.mk f ⟨g, by exact h1⟩ := by
      let x := s.1 (iVU y)
      change g • x = _ at h2
      change x = _
      clear_value x
      induction x using LocalizedModule.induction_on with
      | h a b =>
        rw [LocalizedModule.smul'_mk, LocalizedModule.mk_eq] at h2
        obtain ⟨c, hc⟩ := h2
        refine LocalizedModule.mk_eq.mpr ⟨c, by simpa using hc⟩
    rw [h2]⟩


@[simp]
theorem res_const (f : M) (g : R) (U hu V hv i) :
    (TildeInModuleCat R M).map i (const R M f g U hu) = const R M f g V hv :=
  rfl

theorem res_const' (f : M) (g : R) (V hv) :
    (TildeInModuleCat R M).map (homOfLE hv).op (const R M f g (PrimeSpectrum.basicOpen g) fun _ => id) =
      const R M f g V hv :=
  rfl

@[simp]
theorem localizationToStalk_mk' (x : PrimeSpectrum.Top R) (f : M) (s : x.asIdeal.primeCompl) :
    localizationToStalk R M x (LocalizedModule.mk f s) =
      (TildeInModuleCat R M).germ (⟨x, s.2⟩ : PrimeSpectrum.basicOpen (s : R))
        (const R M f s (PrimeSpectrum.basicOpen s) fun _ => id) := by
  simp only [localizationToStalk]
  erw [LocalizedModule.lift_mk]
  change (isUnit_toStalk R M x s).unit.inv _ = _
  apply_fun (isUnit_toStalk R M x s).unit.1 using
    (Module.End_isUnit_iff _ |>.1 (isUnit_toStalk R M x s)).injective
  rw [← LinearMap.mul_apply]
  simp only [IsUnit.unit_spec, Units.inv_eq_val_inv, IsUnit.mul_val_inv, LinearMap.one_apply,
    Module.algebraMap_end_apply]
  delta toStalk
  erw [comp_apply]
  rw [smul_germ]
  fapply TopCat.Presheaf.germ_ext
  · exact PrimeSpectrum.basicOpen s
  · exact s.2
  · exact homOfLE le_top
  · exact 𝟙 _
  simp only [op_id, CategoryTheory.Functor.map_id, LinearMapClass.map_smul, id_apply]
  refine Subtype.eq <| funext fun y => ?_
  change LocalizedModule.mk _ _ = _
  rw [smul_section_apply]
  simp only [Opens.coe_top, Quiver.Hom.unop_op, isLocallyFraction_pred,
    LocalizedModule.mkLinearMap_apply, const_apply]
  rw [LocalizedModule.smul'_mk, LocalizedModule.mk_eq]
  refine ⟨1, ?_⟩
  simp only [smul_comm, one_smul]
  rfl

@[simps]
noncomputable def stalkIso (x : PrimeSpectrum.Top R) :
    TopCat.Presheaf.stalk (TildeInModuleCat R M) x ≅
    ModuleCat.of R (LocalizedModule x.asIdeal.primeCompl M) where
  hom := stalkToFiberLinearMap R M x
  inv := localizationToStalk R M x
  hom_inv_id := by
    fapply TopCat.Presheaf.stalk_hom_ext
    intro U hxU
    ext s
    simp only [Category.comp_id]
    erw [comp_apply, comp_apply, stalkToFiberLinearMap_germ']
    obtain ⟨V, hxV, iVU, f, g, (hg : V ≤ PrimeSpectrum.basicOpen _), hs⟩ :=
      exists_const _ _ _ s x hxU
    erw [← res_apply R M U V iVU s ⟨x, hxV⟩, ← hs, const_apply, localizationToStalk_mk']
    refine (TildeInModuleCat R M).germ_ext V hxV (homOfLE hg) iVU ?_
    dsimp
    erw [← hs, res_const']
  inv_hom_id := by
    ext x
    induction x using LocalizedModule.induction_on with
    | h m s =>
      simp only [ModuleCat.coe_comp, Function.comp_apply, localizationToStalk_mk',
        ModuleCat.id_apply]
      erw [stalkToFiberLinearMap_germ']
      simp

end Tilde

end AlgebraicGeometry
