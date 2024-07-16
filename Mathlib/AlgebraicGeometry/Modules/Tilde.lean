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
* `ModuleCat.tilde.stalkIso`: The isomorphism of `R`-modules from the stalk of `M^~` at `x` to
the localization of `M` at the prime ideal corresponding to `x`.

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
  res := by rintro V U i f ⟨m, s, w⟩; exact ⟨m, s, fun x => w (i x)⟩

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
  zero_mem' x := ⟨unop U, x.2, 𝟙 _, 0, 1, fun y =>
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
def pretildeInAddCommGrp : Presheaf AddCommGrp (PrimeSpectrum.Top R) where
  obj U := .of ((M.tildeInType).1.obj U)
  map {U V} i :=
    { toFun := M.tildeInType.1.map i
      map_zero' := rfl
      map_add' := fun x y => rfl}

/--
`M^~` as a sheaf of abelian groups over `Spec R`
-/
def tildeInAddCommGrp : Sheaf AddCommGrp (PrimeSpectrum.Top R) :=
  ⟨M.pretildeInAddCommGrp,
    TopCat.Presheaf.isSheaf_iff_isSheaf_comp (forget AddCommGrp) _ |>.mpr
      (TopCat.Presheaf.isSheaf_of_iso (NatIso.ofComponents (fun _ => Iso.refl _) fun _ => rfl)
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
    map_smul := fun _ _ _ => rfl }
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

lemma smul_germ (r : R) (U : Opens (PrimeSpectrum.Top R)) (x : U)
    (s : (tildeInModuleCat M).1.obj (op U)) :
    r • (tildeInModuleCat M).germ x s =
    (tildeInModuleCat M).germ x (r • s) := by rw [map_smul]

/-- The ring homomorphism that takes a section of the structure sheaf of `R` on the open set `U`,
implemented as a subtype of dependent functions to localizations at prime ideals, and evaluates
the section on the point corresponding to a given prime ideal. -/
def openToLocalization (U : Opens (PrimeSpectrum.Top R)) (x : PrimeSpectrum.Top R) (hx : x ∈ U) :
    (tildeInModuleCat M).1.obj (op U) ⟶
    ModuleCat.of R (LocalizedModule x.asIdeal.primeCompl M) where
  toFun s := (s.1 ⟨x, hx⟩ : _)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem coe_openToLocalization (U : Opens (PrimeSpectrum.Top R)) (x : PrimeSpectrum.Top R)
    (hx : x ∈ U) :
    (openToLocalization M U x hx :
        (tildeInAddCommGrp M).1.obj (op U) → LocalizedModule x.asIdeal.primeCompl M) =
      fun s => (s.1 ⟨x, hx⟩ : _) :=
  rfl

theorem openToLocalization_apply (U : Opens (PrimeSpectrum.Top R)) (x : PrimeSpectrum.Top R)
    (hx : x ∈ U) (s : (tildeInAddCommGrp M).1.obj (op U)) :
    openToLocalization M U x hx s = (s.1 ⟨x, hx⟩ : _) :=
  rfl

/--
The morphism of `R`-modules from the stalk of `M^~` at `x` to the localization of `M` at the
prime ideal of `R` corresponding to `x`.
-/
noncomputable def stalkToFiberLinearMap (x : PrimeSpectrum.Top R) :
    TopCat.Presheaf.stalk (tildeInModuleCat M) x ⟶
    ModuleCat.of R (LocalizedModule x.asIdeal.primeCompl M) :=
  Limits.colimit.desc ((OpenNhds.inclusion x).op ⋙ (tildeInModuleCat M))
    { pt := _
      ι :=
      { app := fun U =>
          (openToLocalization M ((OpenNhds.inclusion _).obj (unop U)) x (unop U).2)
        naturality := fun {U V} i => by aesop_cat } }

@[simp]
theorem germ_comp_stalkToFiberLinearMap (U : Opens (PrimeSpectrum.Top R)) (x : U) :
    TopCat.Presheaf.germ (tildeInModuleCat M) x ≫ stalkToFiberLinearMap M x =
    openToLocalization M U x x.2 :=
  Limits.colimit.ι_desc _ _

@[simp]
theorem stalkToFiberLinearMap_germ' (U : Opens (PrimeSpectrum.Top R)) (x : PrimeSpectrum.Top R)
    (hx : x ∈ U) (s : (tildeInModuleCat M).1.obj (op U)) :
    stalkToFiberLinearMap M x
      (TopCat.Presheaf.germ (tildeInModuleCat M) ⟨x, hx⟩ s) = (s.1 ⟨x, hx⟩ : _) :=
  DFunLike.ext_iff.1 (germ_comp_stalkToFiberLinearMap M U ⟨x, hx⟩ : _) s

@[simp]
theorem stalkToFiberLinearMap_germ (U : Opens (PrimeSpectrum.Top R)) (x : U)
    (s : (tildeInModuleCat M).1.obj (op U)) :
    stalkToFiberLinearMap M x (TopCat.Presheaf.germ (tildeInModuleCat M) x s) =
    s.1 x := by
  cases x; exact stalkToFiberLinearMap_germ' M U _ _ _

/--
If `U` is an open subset of `Spec R`, this is the morphism of `R`-modules from `M` to
`M^~(U)`.
-/
def toOpen (U : Opens (PrimeSpectrum.Top R)) :
    ModuleCat.of R M ⟶ (tildeInModuleCat M).1.obj (op U) where
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
    toOpen M U ≫ (tildeInModuleCat M).map i.op = toOpen M V :=
  rfl

/--
If `x` is a point of `Spec R`, this is the morphism of `R`-modules from `M` to the stalk of
`M^~` at `x`.
-/
noncomputable def toStalk (x : PrimeSpectrum.Top R) :
    ModuleCat.of R M ⟶ TopCat.Presheaf.stalk (tildeInModuleCat M) x :=
  (toOpen M ⊤ ≫ TopCat.Presheaf.germ (tildeInModuleCat M) ⟨x, by trivial⟩)

@[simp]
theorem toOpen_germ (U : Opens (PrimeSpectrum.Top R)) (x : U) :
    toOpen M U ≫ TopCat.Presheaf.germ (tildeInModuleCat M) x = toStalk M x := by
  rw [← toOpen_res M ⊤ U (homOfLE le_top : U ⟶ ⊤), Category.assoc, Presheaf.germ_res]; rfl

theorem germ_toOpen (U : Opens (PrimeSpectrum.Top R)) (x : U) (f : M) :
    (M.tildeInModuleCat.germ x) ((ModuleCat.Tilde.toOpen M U) f) = toStalk M x f := by
  rw [← toOpen_germ]; rfl

lemma isUnit_toStalk (x : PrimeSpectrum.Top R) (r : x.asIdeal.primeCompl) :
    IsUnit ((algebraMap R (Module.End R ((tildeInModuleCat M).stalk x))) r) := by
  rw [Module.End_isUnit_iff]
  refine ⟨?_, ?_⟩
  · rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    rintro st (h : r.1 • st = 0)
    simp only [LinearMap.mem_ker, Module.algebraMap_end_apply, Submodule.mem_bot] at h ⊢

    obtain ⟨U, mem, s, rfl⟩ := TopCat.Presheaf.germ_exist (F := (tildeInModuleCat M)) x st
    erw [← (M.tildeInModuleCat.germ ⟨x, mem⟩).map_smul r.1 s] at h
    obtain ⟨⟨⟨W, (mem_W : x ∈ W)⟩⟩, iU, (h : M.tildeInModuleCat.map _ _ = 0)⟩ :=
      Limits.Concrete.colimit_rep_eq_zero (hx := h)
    dsimp only [Functor.comp_obj, Functor.op_obj, OpenNhds.inclusion_obj, Functor.comp_map,
      Functor.op_map] at h

    obtain ⟨W', (mem_W' : x ∈ W'), (iW : W' ⟶ W), num, _, _⟩ :=
      ((tildeInModuleCat M).map iU) s |>.2 ⟨x, mem_W⟩
    let O := W' ⊓ (PrimeSpectrum.basicOpen r)
    suffices (tildeInModuleCat M).map
        (op $ (homOfLE $ inf_le_left.trans (leOfHom $ iW ≫ iU.unop) : O ⟶ U)) s = 0 by
      have := congr((tildeInModuleCat M).germ (⟨x, ⟨mem_W', r.2⟩⟩ :
        (W' ⊓ PrimeSpectrum.basicOpen r.1 : Opens _)) $this)
      rw [this.symm.trans (TopCat.Presheaf.germ_res_apply _ _ _ _) |>.symm, map_zero]

    refine Subtype.ext $ funext fun q => show _ = 0 from ?_
    apply_fun (tildeInModuleCat M).map (op iW) at h
    rw [map_smul] at h
    replace h := congr_fun (Subtype.ext_iff.1 h) ⟨q.1, q.2.1⟩
    exact LocalizedModule.eq_zero_of_smul_eq_zero (hx := h) q.2.2

  · intro st
    obtain ⟨U, mem, s, rfl⟩ := TopCat.Presheaf.germ_exist (F := (tildeInModuleCat M)) x st
    let O := U ⊓ (PrimeSpectrum.basicOpen r)
    have mem_O : x ∈ O := ⟨mem, r.2⟩
    refine ⟨TopCat.Presheaf.germ (tildeInModuleCat M) ⟨x, mem_O⟩
      ⟨fun q => (Localization.mk 1 ⟨r, q.2.2⟩ : Localization.AtPrime q.1.asIdeal) • s.1
        ⟨q.1, q.2.1⟩, fun q => ?_⟩, ?_⟩
    · obtain ⟨V, mem_V, (iV : V ⟶ U), num, den, hV⟩ := s.2 ⟨q.1, q.2.1⟩
      refine ⟨V ⊓ O, ⟨mem_V, q.2⟩, homOfLE inf_le_right, num, r * den, fun y => ?_⟩
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
      fapply TopCat.Presheaf.germ_ext
      · exact O
      · exact mem_O
      · exact 𝟙 _
      · exact homOfLE inf_le_left
      refine Subtype.eq <| funext fun y => ?_
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

@[simp]
theorem toStalk_comp_stalkToFiberLinearMap (x : PrimeSpectrum.Top R) :
    toStalk M x ≫ stalkToFiberLinearMap M x =
    LocalizedModule.mkLinearMap x.asIdeal.primeCompl M := by
  erw [toStalk, Category.assoc, germ_comp_stalkToFiberLinearMap]; rfl

theorem stalkToFiberRingHom_toStalk (x : PrimeSpectrum.Top R) (m : M) :
    (stalkToFiberLinearMap M x) ((toStalk M x) m) =
    LocalizedModule.mk m 1 :=
  LinearMap.ext_iff.1 (toStalk_comp_stalkToFiberLinearMap M x) _

/--
If `U` is an open subset of `Spec R`, `m` is an element of `M` and `r` is an element of `R`
that is invertible on `U` (i.e. does not belong to any prime ideal corresponding to a point
in `U`), this is `m / r` seen as a section of `M^~` over `U`.
-/
def const (m : M) (r : R) (U : Opens (PrimeSpectrum.Top R))
    (hu : ∀ x ∈ U, r ∈ (x : PrimeSpectrum.Top R).asIdeal.primeCompl) :
    (tildeInModuleCat M).obj (op U) :=
  ⟨fun x => LocalizedModule.mk m ⟨r, hu x x.2⟩, fun x =>
    ⟨U, x.2, 𝟙 _, m, r, fun y => ⟨hu _ y.2, by
      simp only [LocalizedModule.mkLinearMap_apply, LocalizedModule.smul'_mk]
      rw [LocalizedModule.mk_eq]
      exact ⟨1, by simp⟩⟩⟩⟩

@[simp]
theorem const_apply (m : M) (r : R) (U : Opens (PrimeSpectrum.Top R))
    (hu : ∀ x ∈ U, r ∈ (x : PrimeSpectrum.Top R).asIdeal.primeCompl) (x : U) :
    (const M m r U hu).1 x = LocalizedModule.mk m ⟨r, hu x x.2⟩ :=
  rfl

theorem const_apply' (m : M) (r : R) (U : Opens (PrimeSpectrum.Top R))
    (hu : ∀ x ∈ U, r ∈ (x : PrimeSpectrum.Top R).asIdeal.primeCompl) (x : U)
    (hx : r ∈ (x : PrimeSpectrum.Top R).asIdeal.primeCompl) :
    (const M m r U hu).1 x = LocalizedModule.mk m ⟨r, hx⟩ :=
  rfl

theorem exists_const (U) (s : (tildeInModuleCat M).obj (op U)) (x : PrimeSpectrum.Top R)
    (hx : x ∈ U) :
    ∃ (V : Opens (PrimeSpectrum.Top R)) (_ : x ∈ V) (i : V ⟶ U) (f : M) (g : R) (hg : _),
      const M f g V hg = (tildeInModuleCat M).map i.op s :=
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
    (tildeInModuleCat M).map i (const M f g U hu) = const M f g V hv :=
  rfl

theorem res_const' (f : M) (g : R) (V hv) : (tildeInModuleCat M).map (homOfLE hv).op
    (const M f g (PrimeSpectrum.basicOpen g) fun _ => id) =
      const M f g V hv :=
  rfl

@[simp]
theorem localizationToStalk_mk' (x : PrimeSpectrum.Top R) (f : M) (s : x.asIdeal.primeCompl) :
    localizationToStalk M x (LocalizedModule.mk f s) =
      (tildeInModuleCat M).germ (⟨x, s.2⟩ : PrimeSpectrum.basicOpen (s : R))
        (const M f s (PrimeSpectrum.basicOpen s) fun _ => id) := by
  simp only [localizationToStalk]
  erw [LocalizedModule.lift_mk]
  change (isUnit_toStalk M x s).unit.inv _ = _
  apply_fun (isUnit_toStalk M x s).unit.1 using
    (Module.End_isUnit_iff _ |>.1 (isUnit_toStalk M x s)).injective
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
  erw [LocalizedModule.smul'_mk, LocalizedModule.mk_eq]
  refine ⟨1, ?_⟩
  simp only [smul_comm, one_smul]
  rfl

/--
The isomorphism of `R`-modules from the stalk of `M^~` at `x` to the localization of `M` at the
prime ideal corresponding to `x`.
-/
@[simps]
noncomputable def stalkIso (x : PrimeSpectrum.Top R) :
    TopCat.Presheaf.stalk (tildeInModuleCat M) x ≅
    ModuleCat.of R (LocalizedModule x.asIdeal.primeCompl M) where
  hom := stalkToFiberLinearMap M x
  inv := localizationToStalk M x
  hom_inv_id := by
    fapply TopCat.Presheaf.stalk_hom_ext
    intro U hxU
    ext s
    simp only [Category.comp_id]
    erw [comp_apply, comp_apply, stalkToFiberLinearMap_germ']
    obtain ⟨V, hxV, iVU, f, g, (hg : V ≤ PrimeSpectrum.basicOpen _), hs⟩ :=
      exists_const _ _ s x hxU
    erw [← res_apply M U V iVU s ⟨x, hxV⟩, ← hs, const_apply, localizationToStalk_mk']
    refine (tildeInModuleCat M).germ_ext V hxV (homOfLE hg) iVU ?_
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

end ModuleCat
