/-
Copyright (c) 2026 Raphael Douglas Giles. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Douglas Giles
-/
import Mathlib.AlgebraicGeometry.AlgebraicCycle.ExactSequence

/-!
# `𝒪ₓ(0)` is the structure sheaf

In this file we show that on a curve (`Order.KrullDimLE 1 X`), the divisorial sheaf `𝒪ₓ(0)` of
`SheafViaSubmodule` is isomorphic, as a sheaf of modules, to the structure sheaf `𝒪ₓ` — the
free rank-one sheaf of modules `SheafOfModules.unit X.ringCatSheaf`, here abbreviated
`structureSheafModule X`.

The canonical morphism `𝒪ₓ ⟶ 𝒪ₓ(0)` sends a section `a` to `a • 1`, viewing the rational
function `1` as a section of `𝒪ₓ(0)`; on an open `U` its underlying rational function is the
generic germ of `a`. Injectivity is injectivity of germs on an integral scheme. Surjectivity
is where the curve hypothesis enters: a section of `𝒪ₓ(0)` over `U` is a rational function `f`
with `0 ≤ ord f z` at every codimension-one `z ∈ U`, so `f` lies in the image of the local
ring at every codimension-one point of `U`; since every other point of `U` is the generic
point (where there is no condition), `f` is locally a section everywhere on `U`, and the local
liftings glue to a section with generic germ `f` (`exists_germ_eq_of_mem_carrier`).

The main result is `unitIsoSheafZero : structureSheafModule X ≅ sheaf 0`.

TODO: Here we present a proof of this fact that relies on `X` being a curve. This assumption is
unecessary - the proper thing to do is to show this under the assumption that `X` is normal.
However, the argument goes via algebraic Hartog's lemma, which is within reach for Mathlib and
something that should be done, but it is significantly more difficult than the little argument
presented here.
-/

namespace AlgebraicGeometry.AlgebraicCycle.SheafViaSubmodule

open AlgebraicGeometry Scheme Order CategoryTheory Limits Opposite TopologicalSpace
open Function.locallyFinsupp Function.locallyFinsuppWithin

universe u

variable {X : Scheme.{u}} [IsIntegral X] [IsNoetherian X] [IsRegularInCodimensionOne X]

variable (X) in
/-- The structure sheaf `𝒪ₓ`, as the free rank-one sheaf of modules over itself. -/
noncomputable abbrev structureSheafModule : X.Modules :=
  SheafOfModules.unit X.ringCatSheaf

omit [IsNoetherian X] [IsRegularInCodimensionOne X] in
/-- On an irreducible scheme of Krull dimension at most one, every point other than the
generic point has coheight one. -/
lemma coheight_eq_one_of_ne_genericPoint [Order.KrullDimLE 1 X] {z : X}
    (hz : z ≠ genericPoint X) : coheight z = 1 := by
  have hle : z ≤ genericPoint X :=
    Scheme.le_iff_specializes.mpr ((genericPoint_spec X).specializes trivial)
  have hlt : z < genericPoint X := lt_of_le_not_ge hle fun hge => hz
    (((Scheme.le_iff_specializes.mp hge).antisymm (Scheme.le_iff_specializes.mp hle)).eq)
  have h1 : 1 ≤ coheight z :=
    le_trans le_add_self (Order.coheight_add_one_le hlt)
  have h2 : coheight z ≤ 1 := by
    have h := (Order.coheight_le_krullDim z).trans
      (Order.KrullDimLE.krullDim_le (n := 1) (α := ↥X))
    exact_mod_cast h
  exact le_antisymm h2 h1

omit [IsIntegral X] [IsNoetherian X] [IsRegularInCodimensionOne X] in
/-- Sections of the structure sheaf over an empty open form a subsingleton. -/
lemma subsingleton_sections_of_isEmpty {W : X.Opens} (hW : ¬Nonempty ↥W) :
    Subsingleton Γ(X, W) := by
  refine ⟨fun s t => ?_⟩
  refine X.sheaf.eq_of_locally_eq' (fun i : PEmpty.{u + 1} => i.elim) W (fun i => i.elim)
    (fun x hx => absurd ⟨⟨x, hx⟩⟩ hW) s t (fun i => i.elim)

/-- Sections of `𝒪ₓ(D)` over an empty open form a subsingleton: there is no witness that the
generic point lies in the open, so the ambient skyscraper sections are trivial. -/
lemma subsingleton_divisorSubmodule_obj {U : (TopologicalSpace.Opens ↥X)ᵒᵖ}
    (hU : ¬Nonempty ↥(unop U)) (E : AlgebraicCycle X ℤ) :
    Subsingleton ↥((divisorSubmodule (X := X) E).obj U) := by
  refine ⟨fun a b => Subtype.ext ?_⟩
  exact pi_ext _ fun x => absurd ⟨⟨genericPoint X, x.down.down⟩⟩ hU

omit [IsRegularInCodimensionOne X] in
/-- The rational function `1` satisfies the section condition of `𝒪ₓ(0)` on any nonempty
open. -/
lemma one_mem_carrier {U : X.Opens} [hU : Nonempty ↥U] :
    (1 : X.functionField) ∈ Sheaf.carrier (0 : AlgebraicCycle X ℤ) U := by
  refine Sheaf.mem_carrier_iff.mpr fun _ => ⟨hU, fun z hz => ?_⟩
  have hord : X.ord (1 : X.functionField) z = 0 := by
    by_cases h1 : coheight z = 1
    · rw [ord_eq_iff h1 one_ne_zero, map_one]
      simp
    · exact ord_eq_zero_of_coheight_neq_one h1 _
  simp [hord, Function.locallyFinsuppWithin.coe_zero]

/-- The constant section `1` of the sheaf of rational functions is a section of `𝒪ₓ(0)`. -/
lemma constSection_one_mem (U : (TopologicalSpace.Opens ↥X)ᵒᵖ) :
    constSection (U := U) (1 : X.functionField) ∈
      (divisorSubmodule (X := X) (0 : AlgebraicCycle X ℤ)).obj U := by
  intro x
  rw [eval_constSection]
  haveI : Nonempty ↥(unop U) := ⟨⟨genericPoint X, x.down.down⟩⟩
  exact one_mem_carrier

omit [IsNoetherian X] [IsRegularInCodimensionOne X] in
/-- Restriction maps of the sheaf of rational functions fix constant sections. -/
lemma map_constSection {U V : (TopologicalSpace.Opens ↥X)ᵒᵖ} (r : U ⟶ V)
    (f : ↑X.functionField) :
    (functionFieldSheaf X).val.map r (constSection (U := U) f) = constSection (U := V) f :=
  pi_ext _ fun x =>
    ((eval_map r x (constSection (U := U) f)).trans
      (eval_constSection _ f)).trans (eval_constSection x f).symm

/-- The section `1` of `𝒪ₓ(0)` over an open, as an element of the module of sections. -/
noncomputable def oneSectionElt (U : (TopologicalSpace.Opens ↥X)ᵒᵖ) :
    ↑((presheaf (X := X) (0 : AlgebraicCycle X ℤ)).obj U) :=
  ⟨constSection (U := U) (1 : X.functionField), constSection_one_mem U⟩

/-- The global section `1` of `𝒪ₓ(0)`. -/
noncomputable def oneSection :
    (presheaf (X := X) (0 : AlgebraicCycle X ℤ)).sections :=
  PresheafOfModules.sectionsMk (fun U => oneSectionElt U)
    (fun _ _ r => Subtype.ext (map_constSection r 1))

/-- The canonical morphism `𝒪ₓ ⟶ 𝒪ₓ(0)` of presheaves of modules, sending a section `a` to
`a • 1`. -/
noncomputable def unitToSheafZero :
    PresheafOfModules.unit X.ringCatSheaf.obj ⟶ presheaf (X := X) (0 : AlgebraicCycle X ℤ) :=
  (presheaf (X := X) (0 : AlgebraicCycle X ℤ)).unitHomEquiv.symm (oneSection (X := X))

lemma unitToSheafZero_app_apply (U : (TopologicalSpace.Opens ↥X)ᵒᵖ)
    (a : ↑(X.ringCatSheaf.obj.obj U)) :
    unitToSheafZero.app U a = a • oneSectionElt U := rfl

/-- The underlying rational function of `a • 1` is the generic germ of `a`. -/
lemma eval_unitToSheafZero_app (U : (TopologicalSpace.Opens ↥X)ᵒᵖ)
    (x : (Opens.pointGrothendieckTopology (genericPoint X)).fiber.obj (unop U))
    (a : ↑(X.ringCatSheaf.obj.obj U)) :
    eval x (unitToSheafZero.app U a).val =
      X.presheaf.germ (unop U) (genericPoint X) x.down.down a * 1 := by
  rw [unitToSheafZero_app_apply]
  have hval : ((a • oneSectionElt U :
      ↑((presheaf (X := X) (0 : AlgebraicCycle X ℤ)).obj U))).val =
      a • constSection (U := U) (1 : X.functionField) := rfl
  rw [hval, eval_smul, eval_constSection]

/-- On a curve, a rational function satisfying the section condition of `𝒪ₓ(0)` on `U` is the
generic germ of an honest section of the structure sheaf over `U`. -/
lemma exists_germ_eq_of_mem_carrier [Order.KrullDimLE 1 X] {U : X.Opens}
    (hη : genericPoint X ∈ U) {f : X.functionField}
    (hf : f ∈ Sheaf.carrier (0 : AlgebraicCycle X ℤ) U) :
    ∃ a : Γ(X, U), X.presheaf.germ U (genericPoint X) hη a = f := by
  classical
  rcases eq_or_ne f 0 with rfl | hf0
  · exact ⟨0, map_zero _⟩
  have hbound : ∀ z ∈ U, coheight z = 1 → 0 ≤ X.ord f z := by
    intro z hzU hz1
    have h := (Sheaf.mem_carrier_iff.mp hf hf0).2 z hzU
    simpa using h
  -- every point of `U` has a neighbourhood in `U` on which `f` is a section
  have hlocal : ∀ z ∈ U, ∃ (V : X.Opens) (hzV : z ∈ V), V ≤ U ∧
      ∃ s : Γ(X, V), algebraMap (X.presheaf.stalk z) X.functionField
        (X.presheaf.germ V z hzV s) = f := by
    intro z hzU
    have hstalk : ∃ t : ↑(X.presheaf.stalk z),
        algebraMap (X.presheaf.stalk z) X.functionField t = f := by
      rcases eq_or_ne z (genericPoint X) with rfl | hzη
      · -- at the generic point, `f` is the germ of a section near the generic point
        obtain ⟨W, hηW, s₀, hs₀⟩ := TopCat.Presheaf.exists_germ_eq X.presheaf
          (show ↑(X.presheaf.stalk (genericPoint X)) from f)
        haveI : Nonempty ↑W := ⟨⟨genericPoint X, hηW⟩⟩
        refine ⟨X.presheaf.germ W (genericPoint X) hηW s₀, ?_⟩
        rw [Scheme.algebraMap_germ_eq_germToFunctionField hηW]
        exact hs₀
      · have hz1 : coheight z = 1 := coheight_eq_one_of_ne_genericPoint hzη
        exact (mem_range_algebraMap_iff_ord_nonneg hz1 f).mpr
          fun _ => hbound z hzU hz1
    obtain ⟨t, ht⟩ := hstalk
    obtain ⟨W, hzW, s₀, hs₀⟩ := TopCat.Presheaf.exists_germ_eq X.presheaf t
    refine ⟨W ⊓ U, ⟨hzW, hzU⟩, inf_le_right,
      X.presheaf.map (homOfLE (inf_le_left : W ⊓ U ≤ W)).op s₀, ?_⟩
    rw [TopCat.Presheaf.germ_res_apply, hs₀]
    exact ht
  choose V hzV hVU s hs using hlocal
  -- the generic point lies in every member of the covering
  have hηV : ∀ i : ↥U, genericPoint X ∈ V i.1 i.2 := fun i =>
    ((genericPoint_spec X).mem_open_set_iff (V i.1 i.2).isOpen).mpr
      (by simpa using Set.nonempty_of_mem (hzV i.1 i.2))
  -- each local lifting has generic germ `f`
  have hgermη : ∀ i : ↥U,
      X.presheaf.germ (V i.1 i.2) (genericPoint X) (hηV i) (s i.1 i.2) = f := by
    intro i
    haveI : Nonempty ↑(V i.1 i.2) := ⟨⟨i.1, hzV i.1 i.2⟩⟩
    have h := hs i.1 i.2
    rw [Scheme.algebraMap_germ_eq_germToFunctionField (hzV i.1 i.2)] at h
    exact h
  -- the local liftings agree on overlaps, since they agree at the generic point
  have hcomp : TopCat.Presheaf.IsCompatible X.sheaf.1 (fun i : ↥U => V i.1 i.2)
      (fun i => s i.1 i.2) := by
    intro i j
    change X.presheaf.map (Opens.infLELeft (V i.1 i.2) (V j.1 j.2)).op (s i.1 i.2) =
      X.presheaf.map (Opens.infLERight (V i.1 i.2) (V j.1 j.2)).op (s j.1 j.2)
    have hmem : genericPoint X ∈ V i.1 i.2 ⊓ V j.1 j.2 := ⟨hηV i, hηV j⟩
    apply germ_injective_of_isIntegral X (genericPoint X) hmem
    rw [TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply, hgermη i, hgermη j]
  obtain ⟨a, ha, -⟩ := X.sheaf.existsUnique_gluing' (fun i : ↥U => V i.1 i.2) U
    (fun i => homOfLE (hVU i.1 i.2))
    (fun z hzU => Opens.mem_iSup.mpr ⟨⟨z, hzU⟩, hzV z hzU⟩)
    (fun i => s i.1 i.2) hcomp
  refine ⟨a, ?_⟩
  have ha' : X.presheaf.map (homOfLE (hVU (genericPoint X) hη)).op a
      = s (genericPoint X) hη := ha ⟨genericPoint X, hη⟩
  have h := congrArg (X.presheaf.germ (V (genericPoint X) hη) (genericPoint X)
    (hηV ⟨genericPoint X, hη⟩)) ha'
  rw [TopCat.Presheaf.germ_res_apply] at h
  exact h.trans (hgermη ⟨genericPoint X, hη⟩)

/-- On a curve, the canonical morphism `𝒪ₓ ⟶ 𝒪ₓ(0)` is bijective on every open. -/
lemma unitToSheafZero_app_bijective [Order.KrullDimLE 1 X]
    (U : (TopologicalSpace.Opens ↥X)ᵒᵖ) :
    Function.Bijective (unitToSheafZero.app U) := by
  by_cases hU : Nonempty ↥(unop U)
  · have hη : genericPoint X ∈ unop U :=
      ((genericPoint_spec X).mem_open_set_iff (unop U).isOpen).mpr
        (by simpa using Set.nonempty_of_mem hU.some.2)
    have x₀ : (Opens.pointGrothendieckTopology (genericPoint X)).fiber.obj (unop U) := ⟨⟨hη⟩⟩
    constructor
    · intro a b hab
      have h : eval x₀ (unitToSheafZero.app U a).val
          = eval x₀ (unitToSheafZero.app U b).val := congrArg (fun t => eval x₀ t.val) hab
      rw [eval_unitToSheafZero_app, eval_unitToSheafZero_app, mul_one, mul_one] at h
      exact germ_injective_of_isIntegral X (genericPoint X) hη h
    · rintro ⟨t, ht⟩
      have htx₀ : eval x₀ t ∈ Sheaf.carrier (0 : AlgebraicCycle X ℤ) (unop U) := ht x₀
      obtain ⟨a, ha⟩ := exists_germ_eq_of_mem_carrier hη htx₀
      refine ⟨a, Subtype.ext (pi_ext _ fun
        (x : (Opens.pointGrothendieckTopology (genericPoint X)).fiber.obj (unop U)) => ?_)⟩
      change eval x (unitToSheafZero.app U a).val = eval x t
      rw [eval_unitToSheafZero_app, mul_one]
      have hxt : eval x t = eval x₀ t := congrArg (fun w => eval w t) (Subsingleton.elim x x₀)
      rw [hxt]
      exact ha
  · constructor
    · intro a b _
      exact @Subsingleton.elim _ (subsingleton_sections_of_isEmpty hU) a b
    · intro t
      exact ⟨0, @Subsingleton.elim _
        (subsingleton_divisorSubmodule_obj hU (0 : AlgebraicCycle X ℤ)) _ _⟩

/-- On a curve, `𝒪ₓ ⟶ 𝒪ₓ(0)` is an isomorphism of presheaves of modules. -/
noncomputable def unitIsoPresheafZero [Order.KrullDimLE 1 X] :
    PresheafOfModules.unit X.ringCatSheaf.obj ≅ presheaf (X := X) (0 : AlgebraicCycle X ℤ) :=
  PresheafOfModules.isoMk
    (fun U => @asIso _ _ _ _ (unitToSheafZero.app U)
      ((ConcreteCategory.isIso_iff_bijective _).mpr (unitToSheafZero_app_bijective U)))
    (fun _ _ r => unitToSheafZero.naturality r)

/-- **`𝒪ₓ(0)` is the structure sheaf.** On a curve (`Order.KrullDimLE 1 X`), the free
rank-one sheaf of modules `𝒪ₓ` is isomorphic to the divisorial sheaf `𝒪ₓ(0)`. -/
noncomputable def unitIsoSheafZero [Order.KrullDimLE 1 X] :
    structureSheafModule X ≅ sheaf (X := X) (0 : AlgebraicCycle X ℤ) where
  hom := ⟨unitIsoPresheafZero.hom⟩
  inv := ⟨unitIsoPresheafZero.inv⟩
  hom_inv_id := SheafOfModules.hom_ext unitIsoPresheafZero.hom_inv_id
  inv_hom_id := SheafOfModules.hom_ext unitIsoPresheafZero.inv_hom_id

end AlgebraicGeometry.AlgebraicCycle.SheafViaSubmodule
