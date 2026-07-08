/-
Copyright (c) 2026 Raphael Douglas Giles. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Douglas Giles
-/
import Mathlib.AlgebraicGeometry.AlgebraicCycle.Sheaf
import Mathlib.AlgebraicGeometry.AlgebraicCycle.SkyscraperTopos
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule

/-!
# `𝒪ₓ(D)` as a submodule of the sheaf of rational functions

This file is a parallel implementation of the divisorial sheaf `𝒪ₓ(D)` of
`Mathlib.AlgebraicGeometry.AlgebraicCycle.Sheaf`, for design comparison. Instead of building the
presheaf of modules from scratch, we:

1. define the sheaf of rational functions `functionFieldSheaf X` as the skyscraper sheaf of
   modules at the generic point valued in the function field, using the topos-point skyscraper
   of `Mathlib.AlgebraicGeometry.AlgebraicCycle.SkyscraperTopos`. Since `X` is irreducible, the
   generic point lies in every nonempty open, so this has sections `k(X)` over nonempty opens
   and `0` over `∅`; being a skyscraper, it is a sheaf (and flasque) with no further work;
2. carve out `𝒪ₓ(D)` as a `PresheafOfModules.Submodule` of the ambient sheaf
   (`divisorSubmodule`), whose membership predicate is the pointwise order bound
   `Sheaf.carrier` of the original construction, imposed on the value `eval x s` of a section
   at a witness `x` that the generic point lies in the open. All the algebraic content
   (closure under addition, scalar multiplication, restriction, monotonicity in `D`) is
   inherited verbatim from the lemmas of `Mathlib.AlgebraicGeometry.AlgebraicCycle.Sheaf`;
   this file contains no new mathematics, only structure;
3. prove the sheaf property intrinsically (`isSheaf`): a compatible family glues in the ambient
   sheaf, and the glued section satisfies the divisor bound because the bound is pointwise,
   hence local. This is the argument that a `J`-closed submodule of a sheaf is a sheaf,
   specialized to `𝒪ₓ(D)`; compare the from-scratch gluing argument in
   `AlgebraicCycle.Sheaf.isSheaf`, which in addition has to glue the underlying rational
   functions by hand (via irreducibility of `X`).

The payoffs visible in this file: no case split on `Nonempty U` anywhere, no hand-rolled
`AddCommGroup`/`Module` transport onto sections, and the inclusion `𝒪ₓ(D₁) ⟶ 𝒪ₓ(D₂)` for
`D₁ ≤ D₂` is `PresheafOfModules.Submodule.homOfLE` of a one-line monotonicity lemma, with its
`Mono` instance found by instance search.

## TODO

* Once `SheafOfModules.Submodule` (a `PresheafOfModules.Submodule` closed under local sections)
  is available, `divisorSubmodule` should be upgraded to one, with `isSheaf` refactored through
  the general statement.
* Prove that the stalk of a `PresheafOfModules.Submodule` injects into the stalk of the ambient
  presheaf with image `⨆ (U ∋ x), im (N.obj U →ₗ Mₓ)`, and re-derive
  `stalkToFunctionField_injective`/`range_stalkToFunctionField` from it.
* Upstream `eval_smul` (the computation of the skyscraper scalar action on components in terms
  of germs) to `SkyscraperTopos.lean`.
-/

universe u

open AlgebraicGeometry Scheme CategoryTheory CategoryTheory.Limits
  CategoryTheory.GrothendieckTopology Order Opposite TopologicalSpace

namespace AlgebraicGeometry.AlgebraicCycle
namespace SheafViaSubmodule

variable {X : Scheme.{u}} [IsIntegral X]

/-!
### The ambient sheaf of rational functions
-/

/-- The function field is a module over the `RingCat`-valued stalk of the structure sheaf at
the generic point, via the canonical comparison map to the `CommRingCat`-valued stalk (which is
the function field itself). Compare the analogous instance for residue fields in
`Mathlib.AlgebraicGeometry.AlgebraicCycle.SkyscraperTopos`. -/
noncomputable instance :
    Module ↑(X.ringCatSheaf.presheaf.stalk (genericPoint X)) ↑X.functionField :=
  letI : Module ↑((forget₂ CommRingCat RingCat).obj X.functionField) ↑X.functionField :=
    inferInstanceAs (Module ↑X.functionField ↑X.functionField)
  Module.compHom _ (RingCat.Hom.hom
    (show X.ringCatSheaf.presheaf.stalk (genericPoint X) ⟶
        (forget₂ CommRingCat RingCat).obj X.functionField from
      colimit.post ((OpenNhds.inclusion (genericPoint X)).op ⋙ X.presheaf)
        (forget₂ CommRingCat RingCat)))

variable (X) in
/-- The sheaf of rational functions on an integral scheme: the skyscraper sheaf of modules at
the generic point, valued in the function field. Sections over a nonempty open are `k(X)`
(every nonempty open contains the generic point); sections over `∅` are zero. -/
noncomputable def functionFieldSheaf : X.Modules :=
  skyscraperSheafOfModules (genericPoint X) X.ringCatSheaf ↑X.functionField

/-- The value of a section of the sheaf of rational functions at a witness that the generic
point lies in the open: the underlying rational function. -/
noncomputable def eval {U : (TopologicalSpace.Opens ↥X)ᵒᵖ}
    (x : (Opens.pointGrothendieckTopology (genericPoint X)).fiber.obj (unop U))
    (s : ↑((functionFieldSheaf X).val.obj U)) : ↑X.functionField :=
  (Pi.π (fun _ => AddCommGrpCat.of ↑X.functionField) x).hom s

lemma eval_add {U : (TopologicalSpace.Opens ↥X)ᵒᵖ}
    (x : (Opens.pointGrothendieckTopology (genericPoint X)).fiber.obj (unop U))
    (s t : ↑((functionFieldSheaf X).val.obj U)) :
    eval x (s + t) = eval x s + eval x t :=
  map_add _ s t

lemma eval_zero {U : (TopologicalSpace.Opens ↥X)ᵒᵖ}
    (x : (Opens.pointGrothendieckTopology (genericPoint X)).fiber.obj (unop U)) :
    eval x (0 : ↑((functionFieldSheaf X).val.obj U)) = 0 :=
  map_zero _

/-- Evaluation intertwines restriction with reindexing of the witness: the underlying rational
function of a section does not change under restriction. -/
lemma eval_map {U V : (TopologicalSpace.Opens ↥X)ᵒᵖ} (r : U ⟶ V)
    (x : (Opens.pointGrothendieckTopology (genericPoint X)).fiber.obj (unop V))
    (s : ↑((functionFieldSheaf X).val.obj U)) :
    eval x ((functionFieldSheaf X).val.map r s) =
      eval ((Opens.pointGrothendieckTopology (genericPoint X)).fiber.map r.unop x) s :=
  ConcreteCategory.congr_hom
    (Point.skyscraperPresheaf_map_π (Opens.pointGrothendieckTopology (genericPoint X))
      (AddCommGrpCat.of ↑X.functionField) r x) s

/-- `eval_map`, phrased for the underlying `Ab`-valued presheaf (the form appearing in the
sheaf-condition machinery). -/
lemma eval_presheaf_map {U V : (TopologicalSpace.Opens ↥X)ᵒᵖ} (r : U ⟶ V)
    (x : (Opens.pointGrothendieckTopology (genericPoint X)).fiber.obj (unop V))
    (s : ↑((functionFieldSheaf X).val.obj U)) :
    eval x ((functionFieldSheaf X).val.presheaf.map r s) =
      eval ((Opens.pointGrothendieckTopology (genericPoint X)).fiber.map r.unop x) s :=
  eval_map r x s

/-- The scalar action of a section `a` of the structure sheaf on a section of the sheaf of
rational functions is, on values, multiplication by the germ of `a` at the generic point (i.e.
by the image of `a` in the function field). -/
lemma eval_smul {U : (TopologicalSpace.Opens ↥X)ᵒᵖ}
    (x : (Opens.pointGrothendieckTopology (genericPoint X)).fiber.obj (unop U))
    (a : ↑(X.ringCatSheaf.obj.obj U)) (s : ↑((functionFieldSheaf X).val.obj U)) :
    eval x (a • s) =
      X.presheaf.germ (unop U) (genericPoint X) x.down.down a * eval x s := by
  letI : Module ↑((Opens.pointGrothendieckTopology (genericPoint X)).presheafFiber.obj
      X.ringCatSheaf.presheaf) ↑X.functionField :=
    pointSheafFiberModule (genericPoint X) X.ringCatSheaf ↑X.functionField
  have h1 : eval x (a • s) =
      ((Opens.pointGrothendieckTopology (genericPoint X)).toPresheafFiber (unop U) x
        X.ringCatSheaf.presheaf).hom a • eval x s := by
    refine (ConcreteCategory.congr_hom
      (Point.skyscraperSMul_π (Opens.pointGrothendieckTopology (genericPoint X))
        X.ringCatSheaf.presheaf (ModuleCat.of _ ↑X.functionField) U a x) s).trans ?_
    exact Point.skyscraperSMulComponent_apply _ _ _ _ _ _ _
  rw [h1]
  -- The action of the presheaf fiber on `k(X)` factors through the stalk
  -- (`hfibsmul`, by definition), where the fiber element of `a` is the germ of `a`
  -- (`toPresheafFiber_pointPresheafFiberToStalk`); the stalk acts through the comparison to
  -- the `CommRingCat`-valued stalk (`hsmul`, by definition), which turns that germ into the
  -- image of `a` in the function field (`colimit.ι_post`).
  have hfibsmul : ∀ (r : ↑((Opens.pointGrothendieckTopology
      (genericPoint X)).presheafFiber.obj X.ringCatSheaf.presheaf)) (m : ↑X.functionField),
      r • m = (pointPresheafFiberToStalk (genericPoint X) X.ringCatSheaf).hom r • m :=
    fun _ _ => rfl
  have hsmul : ∀ (t : ↑(X.ringCatSheaf.presheaf.stalk (genericPoint X)))
      (m : ↑X.functionField),
      t • m = (show ↑X.functionField from (RingCat.Hom.hom
        (colimit.post ((OpenNhds.inclusion (genericPoint X)).op ⋙ X.presheaf)
          (forget₂ CommRingCat RingCat))) t) * m :=
    fun _ _ => rfl
  have hfib : (pointPresheafFiberToStalk (genericPoint X) X.ringCatSheaf).hom
      (((Opens.pointGrothendieckTopology (genericPoint X)).toPresheafFiber (unop U) x
        X.ringCatSheaf.presheaf).hom a) =
      (X.ringCatSheaf.presheaf.germ (unop U) (genericPoint X) x.down.down).hom a :=
    ConcreteCategory.congr_hom
      (toPresheafFiber_pointPresheafFiberToStalk (genericPoint X) X.ringCatSheaf
        (unop U) x.down.down) a
  have hpost : (RingCat.Hom.hom
      (colimit.post ((OpenNhds.inclusion (genericPoint X)).op ⋙ X.presheaf)
        (forget₂ CommRingCat RingCat)))
        ((X.ringCatSheaf.presheaf.germ (unop U) (genericPoint X) x.down.down).hom a) =
      (X.presheaf.germ (unop U) (genericPoint X) x.down.down).hom a := by
    have h := colimit.ι_post ((OpenNhds.inclusion (genericPoint X)).op ⋙ X.presheaf)
      (forget₂ CommRingCat RingCat) (op ⟨unop U, x.down.down⟩)
    exact congrArg (fun f => (RingCat.Hom.hom f) a) h
  rw [hfibsmul, hsmul, hfib, hpost]

/-!
### `𝒪ₓ(D)` as a submodule

The membership predicate is `Sheaf.carrier D U` — the pointwise bound `0 ≤ ord f z + D z` for
`z ∈ U` — imposed on the values of a section. All closure properties are the corresponding
lemmas about `Sheaf.carrier`.
-/

variable [IsLocallyNoetherian X] [IsRegularInCodimensionOne X]

omit [IsRegularInCodimensionOne X] in
open Sheaf in
/-- If `D₁ ≤ D₂` then sections of `𝒪ₓ(D₁)` are sections of `𝒪ₓ(D₂)`; a rephrasing of
`AlgebraicCycle.Sheaf.carrier_mono` (which lives downstream, in `ExactSequence.lean`, and
should be moved to `Sheaf.lean`). -/
lemma carrier_mono {D₁ D₂ : AlgebraicCycle X ℤ} (h : D₁ ≤ D₂) {U : X.Opens}
    {f : X.functionField} (hf : f ∈ carrier D₁ U) : f ∈ carrier D₂ U :=
  mem_carrier_iff.mpr fun hne =>
    ⟨(mem_carrier_iff.mp hf hne).1, fun z hz => by
      have h1 := (mem_carrier_iff.mp hf hne).2 z hz
      have h2 : D₁ z ≤ D₂ z := h z
      omega⟩

open Sheaf in
/-- The family of submodules `Γ(𝒪ₓ(D), U) ⊆ Γ(K_X, U)`, stable under restriction: a section of
the sheaf of rational functions belongs to it iff its value satisfies the divisor bound
`0 ≤ ord f z + D z` on `U`. -/
noncomputable def divisorSubmodule (D : AlgebraicCycle X ℤ) :
    PresheafOfModules.Submodule (functionFieldSheaf X).val where
  obj U :=
    { carrier := {s | ∀ x, eval x s ∈ carrier D (unop U)}
      add_mem' := fun hs ht x => eval_add x _ _ ▸ add_mem' D (unop U) (hs x) (ht x)
      zero_mem' := fun x => eval_zero x ▸ zero_mem' D (unop U)
      smul_mem' := fun a s hs x => by
        haveI : Nonempty ↑(unop U) := ⟨⟨genericPoint X, x.down.down⟩⟩
        rw [eval_smul]
        exact smul_mem_nonempty D (unop U) a (hs x) }
  map {U V} r := fun s hs => Submodule.mem_comap.mpr fun x => by
    haveI : Nonempty ↑(unop V) := ⟨⟨genericPoint X, x.down.down⟩⟩
    rw [PresheafOfModules.restrictₛₗ_apply, eval_map]
    exact mem_carrier_of_le D r.unop.le (hs _)

/-- `𝒪ₓ(D)` as a presheaf of modules, realized as a submodule of the sheaf of rational
functions. Compare `AlgebraicCycle.presheaf`. -/
noncomputable def presheaf (D : AlgebraicCycle X ℤ) : PresheafOfModules X.ringCatSheaf.obj :=
  (divisorSubmodule D).toPresheafOfModules

/-- Monotonicity of `divisorSubmodule` in the divisor; inherited from `carrier_mono`. -/
lemma divisorSubmodule_mono {D₁ D₂ : AlgebraicCycle X ℤ} (hD : D₁ ≤ D₂) :
    divisorSubmodule (X := X) D₁ ≤ divisorSubmodule D₂ :=
  fun _ _ hs x => carrier_mono hD (hs x)

/-- The inclusion `𝒪ₓ(D₁) ⟶ 𝒪ₓ(D₂)` for `D₁ ≤ D₂`. Compare `Sheaf.extendLe`: here it is an
instance of the general `PresheafOfModules.Submodule.homOfLE`. -/
noncomputable def extendLe {D₁ D₂ : AlgebraicCycle X ℤ} (hD : D₁ ≤ D₂) :
    presheaf (X := X) D₁ ⟶ presheaf D₂ :=
  PresheafOfModules.Submodule.homOfLE (divisorSubmodule_mono hD)

/-- The inclusion is a monomorphism, inherited from the general submodule inclusion; compare
`Sheaf.extendLe_mono`. -/
instance {D₁ D₂ : AlgebraicCycle X ℤ} (hD : D₁ ≤ D₂) : Mono (extendLe hD) :=
  inferInstanceAs (Mono (PresheafOfModules.Submodule.homOfLE (divisorSubmodule_mono hD)))

/-!
### The sheaf property

A compatible family of sections of `𝒪ₓ(D)` is in particular a compatible family in the ambient
sheaf of rational functions, so it glues there; the glued section satisfies the divisor bound
because the bound is pointwise: near any `z` the glued section restricts to a member of the
family. This is the specialization to `𝒪ₓ(D)` of "a locally-detected submodule of a sheaf is
a sheaf", requiring no bespoke gluing of rational functions.
-/

open Sheaf in
lemma isSheaf (D : AlgebraicCycle X ℤ) :
    TopCat.Presheaf.IsSheaf (presheaf D).presheaf := by
  rw [TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing]
  intro ι U sf hsf
  -- The family of underlying rational-function sections is compatible, so it glues in the
  -- ambient sheaf.
  have hamb : TopCat.Presheaf.IsSheaf (functionFieldSheaf X).val.presheaf :=
    (functionFieldSheaf X).isSheaf
  rw [TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing] at hamb
  obtain ⟨s, hs, huniq⟩ := hamb U (fun i => (sf i).1)
    (fun i j => congrArg Subtype.val (hsf i j))
  -- The glued section satisfies the divisor bound: the bound is pointwise, and near any point
  -- of the cover the glued section restricts to a member of the family.
  have hmem : s ∈ (divisorSubmodule D).obj (op (iSup U)) := by
    intro x
    refine mem_carrier_iff.mpr fun hne => ⟨⟨⟨genericPoint X, x.down.down⟩⟩, fun z hz => ?_⟩
    obtain ⟨i, hzi⟩ := Opens.mem_iSup.mp hz
    have hηi : genericPoint X ∈ U i :=
      ((genericPoint_spec X).mem_open_set_iff (U i).isOpen).mpr
        (by simpa using Set.nonempty_of_mem hzi)
    -- Restrict `s` to `U i`, where it is `sf i`; its value there is the value of `s`.
    have hsi : (functionFieldSheaf X).val.presheaf.map (Opens.leSupr U i).op s = (sf i).1 :=
      hs i
    have hvi : eval ⟨⟨hηi⟩⟩ ((sf i).1 :
        ↑((functionFieldSheaf X).val.obj (op (U i)))) = eval x s := by
      rw [← hsi]
      -- the two witnesses that the generic point lies in `iSup U` agree by proof irrelevance
      exact (eval_presheaf_map (Opens.leSupr U i).op ⟨⟨hηi⟩⟩ s).trans rfl
    have hbound := mem_carrier_iff.mp ((sf i).2 ⟨⟨hηi⟩⟩) (by rw [hvi]; exact hne)
    rw [hvi] at hbound
    exact hbound.2 z hzi
  -- Gluing and uniqueness in the submodule follow from the ambient ones.
  refine ⟨⟨s, hmem⟩, fun i => Subtype.ext (hs i), fun t ht => Subtype.ext ?_⟩
  exact huniq t.1 fun i => congrArg Subtype.val (ht i)

/-- `𝒪ₓ(D)` as a sheaf of modules, via the submodule construction.
Compare `AlgebraicCycle.sheaf`. -/
noncomputable def sheaf (D : AlgebraicCycle X ℤ) : X.Modules where
  val := presheaf D
  isSheaf := isSheaf D

end SheafViaSubmodule
end AlgebraicGeometry.AlgebraicCycle
