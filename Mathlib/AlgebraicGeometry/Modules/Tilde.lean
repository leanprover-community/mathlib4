/-
Copyright (c) 2024 Weihong Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Johan Commelin, Amelia Livingston, Sophie Morel, Jujian Zhang, Weihong Xu
-/

import Mathlib.Algebra.Module.LocalizedModule
import Mathlib.AlgebraicGeometry.StructureSheaf
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits

/-!

# Construction of M^~

Given any commutative ring `R` and `R`-module `M`, we construct the sheaf `M^~` of `𝒪_SpecR`-modules
such that `M^~(U)` is the set of dependent functions that are locally fractions.

## Main definitions

* `ModuleCat.tildeInAddCommGrp` : `M^~` as a sheaf of abelian groups.
* `ModuleCat.tilde` : `M^~` as a sheaf of `𝒪_{Spec R}`-modules.

## Technical note

To get the `R`-module structure on the stalks on `M^~`, we had to define
`ModuleCat.tildeInModuleCat`, which is `M^~` seen as sheaf of `R`-modules. We get it by
applying a forgetful functor to `ModuleCat.tilde M`.

-/

universe u

open TopCat AlgebraicGeometry TopologicalSpace CategoryTheory Opposite

variable {R : Type u} [CommRing R] (M : ModuleCat.{u} R)

namespace ModuleCat

namespace Tilde

/-- For an `R`-module `M` and a point `P` in `Spec R`, `Localizations P` is the localized module
`M` at the prime ideal `P`. -/
abbrev Localizations (P : PrimeSpectrum.Top R) :=
LocalizedModule P.asIdeal.primeCompl M

/-- For any open subset `U ⊆ Spec R`, `IsFraction` is the predicate expressing that a function
`f : ∏_{x ∈ U}, Mₓ` is such that for any `𝔭 ∈ U`, `f 𝔭 = m / s` for some `m : M` and `s ∉ 𝔭`.
In short `f` is a fraction on `U`. -/
def isFraction {U : Opens (PrimeSpectrum R)} (f : ∀ 𝔭 : U, Localizations M 𝔭.1) : Prop :=
  ∃ (m : M) (s : R),
    ∀ x : U, ¬s ∈ x.1.asIdeal ∧ s • f x = LocalizedModule.mkLinearMap x.1.asIdeal.primeCompl M m

/--
The property of a function `f : ∏_{x ∈ U}, Mₓ` being a fraction is stable under restriction.
-/
def isFractionPrelocal : PrelocalPredicate (Localizations M) where
  pred {U} f := isFraction M f
  res := by rintro V U i f ⟨m, s, w⟩; exact ⟨m, s, fun x ↦ w (i x)⟩

/--
For any open subset `U ⊆ Spec R`, `IsLocallyFraction` is the predicate expressing that a function
`f : ∏_{x ∈ U}, Mₓ` is such that for any `𝔭 ∈ U`, there exists an open neighbourhood `V ∋ 𝔭`, such
that for any `𝔮 ∈ V`, `f 𝔮 = m / s` for some `m : M` and `s ∉ 𝔮`.
In short `f` is locally a fraction on `U`.
-/
def isLocallyFraction : LocalPredicate (Localizations M) := (isFractionPrelocal M).sheafify

@[simp]
theorem isLocallyFraction_pred {U : Opens (PrimeSpectrum.Top R)}
    (f : ∀ x : U, Localizations M x) :
    (isLocallyFraction M).pred f =
      ∀ y : U,
        ∃ (V : _) (_ : y.1 ∈ V) (i : V ⟶ U),
          ∃ (m : M) (s: R), ∀ x : V, ¬s ∈ x.1.asIdeal ∧ s • f (i x) =
            LocalizedModule.mkLinearMap x.1.asIdeal.primeCompl M m :=
  rfl

/- M_x is an O_SpecR(U)-module when x is in U -/
noncomputable instance (U : (Opens (PrimeSpectrum.Top R))ᵒᵖ) (x : U.unop):
    Module ((Spec.structureSheaf R).val.obj U) (Localizations M x):=
  Module.compHom (R := (Localization.AtPrime x.1.asIdeal)) _
    (StructureSheaf.openToLocalization R U.unop x x.2 :
      (Spec.structureSheaf R).val.obj U →+* Localization.AtPrime x.1.asIdeal)

@[simp]
lemma sections_smul_localizations_def
    {U : (Opens (PrimeSpectrum.Top R))ᵒᵖ} (x : U.unop)
    (r : (Spec.structureSheaf R).val.obj U)
    (m : Localizations M ↑x) :
  r • m = r.1 x • m := rfl

/--
For any `R`-module `M` and any open subset `U ⊆ Spec R`, `M^~(U)` is an `𝒪_{Spec R}(U)`-submodule
of `∏_{𝔭 ∈ U} M_𝔭`. -/
def sectionsSubmodule (U : (Opens (PrimeSpectrum R))ᵒᵖ) :
    Submodule ((Spec.structureSheaf R).1.obj U) (∀ x : U.unop, Localizations M x.1) where
  carrier := { f | (isLocallyFraction M).pred f }
  zero_mem' x := ⟨unop U, x.2, 𝟙 _, 0, 1, fun y ↦
    ⟨Ideal.ne_top_iff_one _ |>.1 y.1.isPrime.1, by simp⟩⟩
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
    · simp only [Opens.coe_inf, Pi.add_apply, smul_add, map_add,
        LinearMapClass.map_smul] at wa wb ⊢
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
    · simp only [Opens.coe_inf, Pi.smul_apply, LinearMapClass.map_smul] at wa wr ⊢
      rw [mul_comm, ← Algebra.smul_def] at wr
      rw [sections_smul_localizations_def, ← wa, ← mul_smul, ← smul_assoc, mul_comm sr, mul_smul,
        wr, mul_comm rr, Algebra.smul_def, ← map_mul]
      rfl

end Tilde

/--
For any `R`-module `M`, `TildeInType R M` is the sheaf of set on `Spec R` whose sections on `U` are
the dependent functions that are locally fractions. This is often denoted by `M^~`.

See also `Tilde.isLocallyFraction`.
-/
def tildeInType : Sheaf (Type u) (PrimeSpectrum.Top R) :=
  subsheafToTypes (Tilde.isLocallyFraction M)

instance (U : (Opens (PrimeSpectrum.Top R))ᵒᵖ) :
    AddCommGroup (M.tildeInType.1.obj U) :=
  inferInstanceAs $ AddCommGroup (Tilde.sectionsSubmodule M U)

/--
`M^~` as a presheaf of abelian groups over `Spec R`
-/
def preTildeInAddCommGrp : Presheaf AddCommGrp (PrimeSpectrum.Top R) where
  obj U := .of ((M.tildeInType).1.obj U)
  map {U V} i :=
    { toFun := M.tildeInType.1.map i
      map_zero' := rfl
      map_add' := fun x y ↦ rfl}

/--
`M^~` as a sheaf of abelian groups over `Spec R`
-/
def tildeInAddCommGrp : Sheaf AddCommGrp (PrimeSpectrum.Top R) :=
  ⟨M.preTildeInAddCommGrp,
    TopCat.Presheaf.isSheaf_iff_isSheaf_comp (forget AddCommGrp) _ |>.mpr
      (TopCat.Presheaf.isSheaf_of_iso (NatIso.ofComponents (fun _ ↦ Iso.refl _) fun _ ↦ rfl)
        M.tildeInType.2)⟩

noncomputable instance (U : (Opens (PrimeSpectrum.Top R))ᵒᵖ) :
    Module ((Spec (.of R)).ringCatSheaf.1.obj U) (M.tildeInAddCommGrp.1.obj U) :=
  inferInstanceAs $ Module _ (Tilde.sectionsSubmodule M U)

/--
`M^~` as a sheaf of `𝒪_{Spec R}`-modules
-/
noncomputable def tilde : (Spec (CommRingCat.of R)).Modules where
  val :=
  { presheaf := M.tildeInAddCommGrp.1
    module := inferInstance
    map_smul := fun _ _ _ ↦ rfl }
  isSheaf := M.tildeInAddCommGrp.2

/--
This is `M^~` as a sheaf of `R`-modules.
-/
noncomputable def tildeInModuleCat :
    TopCat.Presheaf (ModuleCat R) (PrimeSpectrum.Top R) :=
  (PresheafOfModules.forgetToPresheafModuleCat (op ⊤) $
    Limits.initialOpOfTerminal Limits.isTerminalTop).obj (tilde M).1 ⋙
  ModuleCat.restrictScalars (StructureSheaf.globalSectionsIso R).hom

namespace Tilde

@[simp]
theorem res_apply (U V : Opens (PrimeSpectrum.Top R)) (i : V ⟶ U)
    (s : (tildeInModuleCat M).obj (op U)) (x : V) :
    ((tildeInModuleCat M).map i.op s).1 x = (s.1 (i x) : _) :=
  rfl

lemma smul_section_apply (r : R) (U : Opens (PrimeSpectrum.Top R))
    (s : (tildeInModuleCat M).1.obj (op U)) (x : U) :
    (r • s).1 x = r • (s.1 x) := rfl

/--
If `U` is an open subset of `Spec R`, this is the morphism of `R`-modules from `M` to
`M^~(U)`.
-/
def toOpen (U : Opens (PrimeSpectrum.Top R)) :
    ModuleCat.of R M ⟶ (tildeInModuleCat M).1.obj (op U) where
  toFun f :=
  ⟨fun x ↦ LocalizedModule.mkLinearMap _ _ f, fun x ↦
    ⟨U, x.2, 𝟙 _, f, 1, fun y ↦ ⟨(Ideal.ne_top_iff_one _).1 y.1.2.1, by simp⟩⟩⟩
  map_add' f g := Subtype.eq <| funext fun x ↦ LinearMap.map_add _ _ _
  map_smul' r m := by
    simp only [isLocallyFraction_pred, LocalizedModule.mkLinearMap_apply, LinearMapClass.map_smul,
      RingHom.id_apply]
    rfl

@[simp]
theorem toOpen_res (U V : Opens (PrimeSpectrum.Top R)) (i : V ⟶ U) :
    toOpen M U ≫ (tildeInModuleCat M).map i.op = toOpen M V :=
  rfl

/--
If `x` is a point of `Spec R`, this is the morphism of `R`-modules from `M` to the stalk of
`M^~` at `x`.
-/
noncomputable def toStalk (x : PrimeSpectrum.Top R) :
    ModuleCat.of R M ⟶ TopCat.Presheaf.stalk (tildeInModuleCat M) x :=
  (toOpen M ⊤ ≫ TopCat.Presheaf.germ (tildeInModuleCat M) ⟨x, by trivial⟩)


lemma isUnit_toStalk (x : PrimeSpectrum.Top R) (r : x.asIdeal.primeCompl) :
    IsUnit ((algebraMap R (Module.End R ((tildeInModuleCat M).stalk x))) r) := by
  rw [Module.End_isUnit_iff]
  refine ⟨LinearMap.ker_eq_bot.1 $ eq_bot_iff.2 fun st (h : r.1 • st = 0) ↦ ?_, fun st ↦ ?_⟩
  · simp only [LinearMap.mem_ker, Module.algebraMap_end_apply, Submodule.mem_bot] at h ⊢
    obtain ⟨U, mem, s, rfl⟩ := TopCat.Presheaf.germ_exist (F := (tildeInModuleCat M)) x st
    erw [← (M.tildeInModuleCat.germ ⟨x, mem⟩).map_smul r.1 s] at h
    obtain ⟨⟨⟨W, (mem_W : x ∈ W)⟩⟩, iU, (h : M.tildeInModuleCat.map _ _ = 0)⟩ :=
      Limits.Concrete.colimit_rep_eq_zero (hx := h)
    obtain ⟨W', (mem_W' : x ∈ W'), (iW : W' ⟶ W), num, _, _⟩ :=
      ((tildeInModuleCat M).map iU) s |>.2 ⟨x, mem_W⟩
    let O := W' ⊓ (PrimeSpectrum.basicOpen r)
    suffices (tildeInModuleCat M).map
        (op $ (homOfLE $ inf_le_left.trans (leOfHom $ iW ≫ iU.unop) : O ⟶ U)) s = 0 by
      rw [congr((tildeInModuleCat M).germ (⟨x, ⟨mem_W', r.2⟩⟩ :
        (W' ⊓ PrimeSpectrum.basicOpen r.1 : Opens _)) $this).symm.trans
        (TopCat.Presheaf.germ_res_apply _ _ _ _) |>.symm, map_zero]

    exact Subtype.ext $ funext fun q ↦ LocalizedModule.eq_zero_of_smul_eq_zero
      (hx := congr_fun (Subtype.ext_iff.1 congr((tildeInModuleCat M).map (op iW) $h)) ⟨q.1, q.2.1⟩)
      q.2.2

  · obtain ⟨U, mem, s, rfl⟩ := TopCat.Presheaf.germ_exist (F := (tildeInModuleCat M)) x st
    let O := U ⊓ (PrimeSpectrum.basicOpen r)
    have mem_O : x ∈ O := ⟨mem, r.2⟩
    refine ⟨TopCat.Presheaf.germ (tildeInModuleCat M) ⟨x, mem_O⟩
      ⟨fun q ↦ (Localization.mk 1 ⟨r, q.2.2⟩ : Localization.AtPrime q.1.asIdeal) • s.1
        ⟨q.1, q.2.1⟩, fun q ↦ ?_⟩, ?_⟩
    · obtain ⟨V, mem_V, (iV : V ⟶ U), num, den, hV⟩ := s.2 ⟨q.1, q.2.1⟩
      refine ⟨V ⊓ O, ⟨mem_V, q.2⟩, homOfLE inf_le_right, num, r * den, fun y ↦ ?_⟩
      obtain ⟨h1, h2⟩ := hV ⟨y, y.2.1⟩
      refine ⟨y.1.asIdeal.primeCompl.mul_mem y.2.2.2 h1, ?_⟩
      simp only [Opens.coe_inf, isLocallyFraction_pred, LocalizedModule.mkLinearMap_apply] at h2 ⊢
      rw [LocalizedModule.smul_eq_iff_of_mem (S := y.1.asIdeal.primeCompl) (hr := h1),
        LocalizedModule.mk_smul_mk, one_smul, mul_one] at h2
      rw [h2, LocalizedModule.mk_smul_mk, one_smul, LocalizedModule.smul'_mk, LocalizedModule.mk_eq]
      refine ⟨1, by simp only [one_smul]; rfl⟩
    · simp only [isLocallyFraction_pred, LocalizedModule.mkLinearMap_apply,
        Module.algebraMap_end_apply]
      rw [← map_smul]
      refine TopCat.Presheaf.germ_ext (W := O) (hxW := mem_O) (iWU := 𝟙 _)
        (iWV := homOfLE inf_le_left) _ $ Subtype.eq <| funext fun y ↦ ?_
      simp only [isLocallyFraction_pred, LocalizedModule.mkLinearMap_apply, op_id,
        CategoryTheory.Functor.map_id, LinearMapClass.map_smul,
        id_apply]
      rw [smul_section_apply, LocalizedModule.smul_eq_iff_of_mem]
      rfl

/--
The morphism of `R`-modules from the localization of `M` at the prime ideal corresponding to `x`
to the stalk of `M^~` at `x`.
-/
noncomputable def localizationToStalk (x : PrimeSpectrum.Top R) :
    ModuleCat.of R (LocalizedModule x.asIdeal.primeCompl M) ⟶
    (TopCat.Presheaf.stalk (tildeInModuleCat M) x) :=
  LocalizedModule.lift _ (toStalk M x) $ isUnit_toStalk M x

end Tilde

end ModuleCat
