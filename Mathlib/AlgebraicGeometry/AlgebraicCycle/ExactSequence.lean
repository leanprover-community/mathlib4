/-
Copyright (c) 2026 Raphael Douglas Giles. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Douglas Giles
-/
import Mathlib.AlgebraicGeometry.AlgebraicCycle.SheafViaSubmodule
import Mathlib.AlgebraicGeometry.AlgebraicCycle.LocallyFinsupp
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.Algebra.Category.Grp.EpiMono
import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.Topology.Sheaves.LocallySurjective
import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-!
# The twisted closed subscheme exact sequence

This file is a WIP where we construct the following exact sequence:

`0 ⟶ 𝒪ₓ(D - p) ⟶ 𝒪ₓ(D) ⟶ Q_p(D) ⟶ 0`

Notably, in this formulation, we abstractly characterise the cokernel `Q_p(D)`
(`residueLineSheaf`) as the skyscraper at `p` valued in what is sometimes in the literature called
the "line":

`L_p(D) = {f | ord_p f ≥ -D p} / {f | ord_p f ≥ 1 - D p}` (`residueLine`),

a one-dimensional vector space over the residue field, but with no chosen basis. We then construct
an isomorphism from `Q_p(D)` to `k(P)`, the skyscraper sheaf valued in `κ(p)` at `P`.
Previously, I had not used this basis free presentation, and so had to thread a uniformizer through
a lot of the constructions, which was both ugly and would cause some things only to be true up to
multiplication by units (which is not relevant for Riemann-Roch but makes for bad API long term).
I am still working out the right API for this approach, but I think it is quite a bit better.

## TODO

* Upstream `PresheafOfModules.Submodule.liftOfLE` next to `Submodule.homOfLE`, and the
  skyscraper component lemmas (`eval*_smul`) to `SkyscraperTopos.lean` (stated once for an
  arbitrary module over the stalk, instead of the present copies at `k(X)` and `L_p(D)`).
* Refactor exactness through a `kernelSubmodule` for morphisms of sheaves of modules once
  `SheafOfModules.Submodule` is available.
-/

universe u

open AlgebraicGeometry Scheme CategoryTheory CategoryTheory.Limits
  CategoryTheory.GrothendieckTopology Order Opposite TopologicalSpace
  Function.locallyFinsuppWithin

namespace AlgebraicGeometry.AlgebraicCycle
namespace SheafViaSubmodule

/-! ### Elementwise API for products in `Ab` -/

section PiHelpers

variable {ι : Type u} (f : ι → AddCommGrpCat.{u})

lemma pi_ext {a b : ↑(∏ᶜ f)} (h : ∀ i, (Pi.π f i).hom a = (Pi.π f i).hom b) : a = b :=
  Concrete.limit_ext _ a b fun j => h j.as

lemma pi_lift_π_apply {Z : AddCommGrpCat.{u}} (g : ∀ i, Z ⟶ f i) (i : ι) (z : ↑Z) :
    (Pi.π f i).hom ((Pi.lift g).hom z) = (g i).hom z :=
  ConcreteCategory.congr_hom (limit.lift_π (Fan.mk Z g) ⟨i⟩) z

end PiHelpers

variable {X : Scheme.{u}} [IsIntegral X]

/-! ### Constant sections of the sheaf of rational functions -/

/-- The section of the sheaf of rational functions with constant value `f`. -/
noncomputable def constSection {U : (TopologicalSpace.Opens ↥X)ᵒᵖ} (f : ↑X.functionField) :
    ↑((functionFieldSheaf X).val.obj U) :=
  (Pi.lift fun _ => 𝟙 (AddCommGrpCat.of ↑X.functionField)).hom f

@[simp]
lemma eval_constSection {U : (TopologicalSpace.Opens ↥X)ᵒᵖ}
    (x : (Opens.pointGrothendieckTopology (genericPoint X)).fiber.obj (unop U))
    (f : ↑X.functionField) : eval x (constSection (U := U) f) = f := by
  exact pi_lift_π_apply (fun _ => AddCommGrpCat.of ↑X.functionField)
    (fun _ => 𝟙 (AddCommGrpCat.of ↑X.functionField)) x f

/-! ### Generic skyscraper lemmas -/

variable (p : X)

omit [IsIntegral X] in
/-- Away from `p`, the values of a skyscraper presheaf are zero objects. -/
lemma skyscraperPresheaf_obj_isZero (A : AddCommGrpCat.{u})
    {U : (TopologicalSpace.Opens ↥X)ᵒᵖ} (hp : p ∉ unop U) :
    IsZero (((Opens.pointGrothendieckTopology p).skyscraperPresheaf A).obj U) := by
  have hterm : IsTerminal (((Opens.pointGrothendieckTopology p).skyscraperPresheaf A).obj U) :=
    IsTerminal.ofUniqueHom (fun Z => Pi.lift fun x => absurd x.down.down hp)
      (fun Z m => Pi.hom_ext _ _ fun x => absurd x.down.down hp)
  exact (isZero_zero _).of_iso (hterm.uniqueUpToIso (isZero_zero _).isTerminal)

/-- The canonical comparison from the `RingCat`-valued stalk to the `CommRingCat`-valued
stalk, as a ring homomorphism with the right (syntactic) codomain. -/
noncomputable def stalkCompare :
    ↑(X.ringCatSheaf.presheaf.stalk p) →+* ↑(X.presheaf.stalk p) :=
  RingCat.Hom.hom
    (colimit.post ((OpenNhds.inclusion p).op ⋙ X.presheaf) (forget₂ CommRingCat RingCat))

section Line

variable [IsLocallyNoetherian X] [IsRegularInCodimensionOne X]
variable {p} (hp : coheight p = 1)

/-- The `𝒪_{X,p}`-submodule of `k(X)` of rational functions of order at least `n` at the
codimension-one point `p`: the fractional ideal `𝔪_p^n`. -/
noncomputable def ordSubmodule (n : ℤ) :
    Submodule ↑(X.presheaf.stalk p) ↑X.functionField where
  carrier := {f | f ≠ 0 → n ≤ X.ord f p}
  zero_mem' := fun h => absurd rfl h
  add_mem' := fun {a b} ha hb hne => by
    haveI : IsDiscreteValuationRing (X.presheaf.stalk p) :=
      IsRegularInCodimensionOne.stalk_dvr p hp
    rcases eq_or_ne a 0 with rfl | ha0
    · rw [zero_add] at hne ⊢
      exact hb hne
    rcases eq_or_ne b 0 with rfl | hb0
    · rw [add_zero] at hne ⊢
      exact ha hne
    have h1 := ha ha0
    have h2 := hb hb0
    have h3 := ord_add hp hne
    omega
  smul_mem' := fun c {f} hf hne => by
    haveI : IsDiscreteValuationRing (X.presheaf.stalk p) :=
      IsRegularInCodimensionOne.stalk_dvr p hp
    have hc0 : c ≠ 0 := fun h0 => hne (by rw [h0, zero_smul])
    have hf0 : f ≠ 0 := fun h0 => hne (by rw [h0, smul_zero])
    rw [Algebra.smul_def, X.ord_mul hp (algebraMap_functionField_ne_zero hc0) hf0]
    have h1 := ord_algebraMap_nonneg hp hc0
    have h2 := hf hf0
    omega

lemma mem_ordSubmodule_iff {n : ℤ} {f : ↑X.functionField} :
    f ∈ ordSubmodule hp n ↔ (f ≠ 0 → n ≤ X.ord f p) :=
  Iff.rfl

variable (D : AlgebraicCycle X ℤ)

/-- The canonical value of the cokernel of `𝒪ₓ(D - p) ⟶ 𝒪ₓ(D)`: the line
`𝔪_p^{-D p}/𝔪_p^{1 - D p}`, a one-dimensional `κ(p)`-vector space with no preferred basis. -/
noncomputable def residueLine : Type u :=
  ↥(ordSubmodule hp (-D p)) ⧸
    (Submodule.comap (ordSubmodule hp (-D p)).subtype (ordSubmodule hp (1 - D p)))

noncomputable instance : AddCommGroup (residueLine hp D) :=
  inferInstanceAs (AddCommGroup (↥(ordSubmodule hp (-D p)) ⧸
    (Submodule.comap (ordSubmodule hp (-D p)).subtype (ordSubmodule hp (1 - D p)))))

noncomputable instance : Module ↑(X.presheaf.stalk p) (residueLine hp D) :=
  inferInstanceAs (Module ↑(X.presheaf.stalk p) (↥(ordSubmodule hp (-D p)) ⧸
    (Submodule.comap (ordSubmodule hp (-D p)).subtype (ordSubmodule hp (1 - D p)))))

/-- The class of a rational function of order at least `-D p` in the line `L_p(D)`. -/
noncomputable def residueLine.mk (f : ↥(ordSubmodule hp (-D p))) : residueLine hp D :=
  Submodule.Quotient.mk f

lemma residueLine.mk_surjective : Function.Surjective (residueLine.mk hp D) :=
  Submodule.Quotient.mk_surjective _

lemma residueLine.mk_eq_zero_iff {f : ↥(ordSubmodule hp (-D p))} :
    residueLine.mk hp D f = 0 ↔ f.1 ∈ ordSubmodule hp (1 - D p) :=
  (Submodule.Quotient.mk_eq_zero _).trans Submodule.mem_comap

lemma residueLine.mk_smul (c : ↑(X.presheaf.stalk p)) (f : ↥(ordSubmodule hp (-D p))) :
    residueLine.mk hp D (c • f) = c • residueLine.mk hp D f :=
  Submodule.Quotient.mk_smul _ c f

lemma residueLine.mk_add (f g : ↥(ordSubmodule hp (-D p))) :
    residueLine.mk hp D (f + g) = residueLine.mk hp D f + residueLine.mk hp D g :=
  rfl

/-- The line is a module over the `RingCat`-valued stalk, via the canonical comparison map. -/
noncomputable instance : Module ↑(X.ringCatSheaf.presheaf.stalk p) (residueLine hp D) :=
  Module.compHom _ (stalkCompare p)

/-- `Q_p(D)`: the canonical cokernel of `𝒪ₓ(D - p) ⟶ 𝒪ₓ(D)`, as the skyscraper sheaf of
modules at `p` valued in the line `L_p(D)`. -/
noncomputable def residueLineSheaf : X.Modules :=
  skyscraperSheafOfModules p X.ringCatSheaf (residueLine hp D)

/-- The value of a section of `Q_p(D)` at a witness `p ∈ U`. -/
noncomputable def evalLine {U : (TopologicalSpace.Opens ↥X)ᵒᵖ}
    (x : (Opens.pointGrothendieckTopology p).fiber.obj (unop U))
    (t : ↑((residueLineSheaf hp D).val.obj U)) : residueLine hp D :=
  (Pi.π (fun _ => AddCommGrpCat.of (residueLine hp D)) x).hom t

lemma evalLine_map {U V : (TopologicalSpace.Opens ↥X)ᵒᵖ} (r : U ⟶ V)
    (x : (Opens.pointGrothendieckTopology p).fiber.obj (unop V))
    (t : ↑((residueLineSheaf hp D).val.obj U)) :
    evalLine hp D x ((residueLineSheaf hp D).val.presheaf.map r t) =
      evalLine hp D ((Opens.pointGrothendieckTopology p).fiber.map r.unop x) t :=
  ConcreteCategory.congr_hom
    (Point.skyscraperPresheaf_map_π (Opens.pointGrothendieckTopology p)
      (AddCommGrpCat.of (residueLine hp D)) r x) t

/-- The scalar action of a section `a` of the structure sheaf on `Q_p(D)` is, on values, the
action of the germ of `a` at `p` on the line. -/
lemma evalLine_smul {U : (TopologicalSpace.Opens ↥X)ᵒᵖ}
    (x : (Opens.pointGrothendieckTopology p).fiber.obj (unop U))
    (a : ↑(X.ringCatSheaf.obj.obj U)) (t : ↑((residueLineSheaf hp D).val.obj U)) :
    evalLine hp D x (a • t) =
      X.presheaf.germ (unop U) p x.down.down a • evalLine hp D x t := by
  letI : Module ↑((Opens.pointGrothendieckTopology p).presheafFiber.obj
      X.ringCatSheaf.presheaf) (residueLine hp D) :=
    pointSheafFiberModule p X.ringCatSheaf (residueLine hp D)
  have h1 : evalLine hp D x (a • t) =
      ((Opens.pointGrothendieckTopology p).toPresheafFiber (unop U) x
        X.ringCatSheaf.presheaf).hom a • evalLine hp D x t := by
    refine (ConcreteCategory.congr_hom
      (Point.skyscraperSMul_π (Opens.pointGrothendieckTopology p)
        X.ringCatSheaf.presheaf (ModuleCat.of _ (residueLine hp D)) U a x) t).trans ?_
    exact Point.skyscraperSMulComponent_apply _ _ _ _ _ _ _
  rw [h1]
  have hfibsmul : ∀ (r : ↑((Opens.pointGrothendieckTopology p).presheafFiber.obj
      X.ringCatSheaf.presheaf)) (m : residueLine hp D),
      r • m = (pointPresheafFiberToStalk p X.ringCatSheaf).hom r • m := fun _ _ => rfl
  have hsmul : ∀ (s : ↑(X.ringCatSheaf.presheaf.stalk p)) (m : residueLine hp D),
      s • m = stalkCompare p s • m := fun _ _ => rfl
  have hfib : (pointPresheafFiberToStalk p X.ringCatSheaf).hom
      (((Opens.pointGrothendieckTopology p).toPresheafFiber (unop U) x
        X.ringCatSheaf.presheaf).hom a) =
      (X.ringCatSheaf.presheaf.germ (unop U) p x.down.down).hom a :=
    ConcreteCategory.congr_hom
      (toPresheafFiber_pointPresheafFiberToStalk p X.ringCatSheaf (unop U) x.down.down) a
  have hpost : stalkCompare p
      ((X.ringCatSheaf.presheaf.germ (unop U) p x.down.down).hom a) =
      (X.presheaf.germ (unop U) p x.down.down).hom a := by
    have h := colimit.ι_post ((OpenNhds.inclusion p).op ⋙ X.presheaf)
      (forget₂ CommRingCat RingCat) (op ⟨unop U, x.down.down⟩)
    exact congrArg (fun f => (RingCat.Hom.hom f) a) h
  rw [hfibsmul, hsmul, hfib, hpost]

end Line

/-! ### The morphism to the cokernel -/

section Hom

variable [IsLocallyNoetherian X] [IsRegularInCodimensionOne X]
variable (D : AlgebraicCycle X ℤ) {p : X} (hp : coheight p = 1)

omit [IsLocallyNoetherian X] [IsRegularInCodimensionOne X] in
/-- The generic point lies in every open containing `p`. -/
lemma genericPoint_mem {U : X.Opens} (hpU : p ∈ U) : genericPoint X ∈ U :=
  ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr
    (by simpa using Set.nonempty_of_mem hpU)

/-- The value of a section of `𝒪ₓ(D)` lies in `𝔪_p^{-D p}`: the divisor bound at `p`, from
membership. -/
lemma mem_ordSubmodule_of_mem {U : (TopologicalSpace.Opens ↥X)ᵒᵖ}
    (x : (Opens.pointGrothendieckTopology p).fiber.obj (unop U))
    (s : ↑((presheaf D).obj U)) :
    eval ⟨⟨genericPoint_mem x.down.down⟩⟩ s.1 ∈ ordSubmodule hp (-D p) := fun hne => by
  have h1 := (Sheaf.mem_carrier_iff.mp (s.2 ⟨⟨genericPoint_mem x.down.down⟩⟩) hne).2
    p x.down.down
  omega

/-- The residue of a section of `𝒪ₓ(D)` at a witness `p ∈ U`: the class of its underlying
rational function in the line `L_p(D)`. No choice of uniformizer is involved. -/
noncomputable def toLineFun {U : (TopologicalSpace.Opens ↥X)ᵒᵖ}
    (x : (Opens.pointGrothendieckTopology p).fiber.obj (unop U))
    (s : ↑((presheaf D).obj U)) : residueLine hp D :=
  residueLine.mk hp D
    ⟨eval ⟨⟨genericPoint_mem x.down.down⟩⟩ s.1, mem_ordSubmodule_of_mem D hp x s⟩

lemma toLineFun_add {U : (TopologicalSpace.Opens ↥X)ᵒᵖ}
    (x : (Opens.pointGrothendieckTopology p).fiber.obj (unop U))
    (s t : ↑((presheaf D).obj U)) :
    toLineFun D hp x (s + t) = toLineFun D hp x s + toLineFun D hp x t :=
  Eq.trans (congrArg (residueLine.mk hp D) (Subtype.ext (eval_add _ s.1 t.1)))
    (residueLine.mk_add hp D _ _)

lemma toLineFun_smul {U : (TopologicalSpace.Opens ↥X)ᵒᵖ}
    (x : (Opens.pointGrothendieckTopology p).fiber.obj (unop U))
    (a : ↑(X.ringCatSheaf.obj.obj U)) (s : ↑((presheaf D).obj U)) :
    toLineFun D hp x (a • s) =
      X.presheaf.germ (unop U) p x.down.down a • toLineFun D hp x s := by
  rw [toLineFun, toLineFun, ← residueLine.mk_smul]
  refine congrArg _ (Subtype.ext ?_)
  refine (eval_smul _ a s.1).trans ?_
  have hgerm : algebraMap (X.presheaf.stalk p) X.functionField
      (X.presheaf.germ (unop U) p x.down.down a) =
      X.presheaf.germ (unop U) (genericPoint X) (genericPoint_mem x.down.down) a := by
    haveI : Nonempty ↑(unop U) := ⟨⟨p, x.down.down⟩⟩
    rw [Scheme.algebraMap_germ_eq_germToFunctionField x.down.down]
  rw [← hgerm, SetLike.val_smul, Algebra.smul_def]

/-- `toLineFun` is compatible with restriction: both are computed from the underlying rational
function, which is unchanged by restriction. -/
lemma toLineFun_res {U V : (TopologicalSpace.Opens ↥X)ᵒᵖ} (r : U ⟶ V)
    (x : (Opens.pointGrothendieckTopology p).fiber.obj (unop V))
    (s : ↑((presheaf D).obj U)) :
    toLineFun D hp x ((presheaf D).map r s) =
      toLineFun D hp ((Opens.pointGrothendieckTopology p).fiber.map r.unop x) s :=
  congrArg (residueLine.mk hp D) (Subtype.ext ((eval_map r _ s.1).trans rfl))

/-- The component of the morphism to the cokernel at a witness `p ∈ U`. -/
noncomputable def toLineComponent (U : (TopologicalSpace.Opens ↥X)ᵒᵖ)
    (x : (Opens.pointGrothendieckTopology p).fiber.obj (unop U)) :
    (presheaf D).presheaf.obj U ⟶ AddCommGrpCat.of (residueLine hp D) :=
  AddCommGrpCat.ofHom (AddMonoidHom.mk' (toLineFun D hp x) (toLineFun_add D hp x))

/-- The morphism of abelian presheaves from `𝒪ₓ(D)` to the cokernel skyscraper: `Pi.lift` of
the per-witness components. -/
noncomputable def toLineAb :
    (presheaf D).presheaf ⟶ (residueLineSheaf hp D).val.presheaf where
  app U := Pi.lift fun x => toLineComponent D hp U x
  naturality {U V} r := by
    refine Pi.hom_ext _ _ fun x => ?_
    ext s
    have h1 := pi_lift_π_apply (fun _ => AddCommGrpCat.of (residueLine hp D))
      (toLineComponent D hp V) x (((presheaf D).presheaf.map r) s)
    have h2 := toLineFun_res D hp r x s
    have h3 := ConcreteCategory.congr_hom
      (Point.skyscraperPresheaf_map_π (Opens.pointGrothendieckTopology p)
        (AddCommGrpCat.of (residueLine hp D)) r x)
      ((Pi.lift (toLineComponent D hp U)).hom s)
    have h4 := pi_lift_π_apply (fun _ => AddCommGrpCat.of (residueLine hp D))
      (toLineComponent D hp U)
      (((Opens.pointGrothendieckTopology p).fiber.map r.unop) x) s
    exact (h1.trans (h2.trans h4.symm)).trans h3.symm

/-- The canonical morphism of sheaves of modules `𝒪ₓ(D) ⟶ Q_p(D)`: a section maps to the
class of its underlying rational function. -/
noncomputable def toLineHom : sheaf D ⟶ residueLineSheaf hp D :=
  ⟨PresheafOfModules.homMk (toLineAb D hp) fun U a s => by
    refine pi_ext _ fun x => ?_
    have h1 := pi_lift_π_apply (fun _ => AddCommGrpCat.of (residueLine hp D))
      (toLineComponent D hp U) x (a • s)
    have h2 := toLineFun_smul D hp x a s
    have h3 := evalLine_smul hp D x a ((Pi.lift (toLineComponent D hp U)).hom s)
    have h4 := pi_lift_π_apply (fun _ => AddCommGrpCat.of (residueLine hp D))
      (toLineComponent D hp U) x s
    exact (h1.trans h2).trans (h3.trans (congrArg
      (fun y => X.presheaf.germ (unop U) p x.down.down a • y) h4)).symm⟩

end Hom

/-! ### The kernel of the morphism to the cokernel -/

section Kernel

variable [IsLocallyNoetherian X] [IsRegularInCodimensionOne X]
variable (D : AlgebraicCycle X ℤ) {p : X} (hp : coheight p = 1)

open Classical in
omit [IsRegularInCodimensionOne X] in
/-- Away from `p`, a rational function satisfying the divisor bound for `D` also satisfies it
for `D - single p 1`. Ported from `AlgebraicCycle.Sheaf.mem_carrier_sub_single`. -/
lemma mem_carrier_sub_single {U : X.Opens} (hU : p ∉ U) {f : ↑X.functionField}
    (hf : f ∈ Sheaf.carrier D U) : f ∈ Sheaf.carrier (D - single p 1) U := by
  intro hne
  obtain ⟨h1, h2⟩ := hf hne
  refine ⟨h1, fun z => ?_⟩
  have h3 := h2 z
  simp only [Function.locallyFinsuppWithin.coe_zero, Pi.zero_apply,
    Function.locallyFinsuppWithin.coe_add, Pi.add_apply, restrict_apply] at h3 ⊢
  split_ifs at h3 ⊢ with hz
  · have hzp : z ≠ p := fun h => hU (h ▸ hz)
    simp only [Function.locallyFinsuppWithin.coe_sub, Pi.sub_apply, single_apply,
      if_neg hzp, sub_zero]
    exact h3
  · exact le_refl _

open Classical in
/-- Vanishing of the class in the line is exactly the extra order bound cutting `𝒪ₓ(D - p)`
out of `𝒪ₓ(D)`. -/
lemma toLineFun_eq_zero_iff {U : (TopologicalSpace.Opens ↥X)ᵒᵖ}
    (x : (Opens.pointGrothendieckTopology p).fiber.obj (unop U))
    (s : ↑((presheaf D).obj U)) :
    toLineFun D hp x s = 0 ↔
      eval ⟨⟨genericPoint_mem x.down.down⟩⟩ s.1 ∈
        Sheaf.carrier (D - single p 1) (unop U) := by
  rw [toLineFun, residueLine.mk_eq_zero_iff]
  by_cases hf0 : eval ⟨⟨genericPoint_mem x.down.down⟩⟩ s.1 = 0
  · refine iff_of_true (fun hne => absurd hf0 hne) (by rw [hf0]; exact Sheaf.zero_mem' _ _)
  · rw [mem_ordSubmodule_iff]
    constructor
    · intro h
      have h2 : 1 - D p ≤ X.ord (eval ⟨⟨genericPoint_mem x.down.down⟩⟩ s.1) p := h hf0
      refine (Sheaf.mem_carrier_sub_single_iff x.down.down hf0
        (s.2 ⟨⟨genericPoint_mem x.down.down⟩⟩)).mpr ?_
      omega
    · intro h hne
      have h2 := (Sheaf.mem_carrier_sub_single_iff x.down.down hf0
        (s.2 ⟨⟨genericPoint_mem x.down.down⟩⟩)).mp h
      exact (by omega : 1 - D p ≤ X.ord (eval ⟨⟨genericPoint_mem x.down.down⟩⟩ s.1) p)

open Classical in
/-- A section of `𝒪ₓ(D)` whose classes in the line all vanish satisfies the divisor bound for
`D - single p 1`. -/
lemma mem_sub_of_forall_toLineFun_eq_zero {U : (TopologicalSpace.Opens ↥X)ᵒᵖ}
    (s : ↑((presheaf D).obj U)) (h : ∀ x, toLineFun D hp x s = 0) :
    s.1 ∈ (divisorSubmodule (D - single p 1)).obj U := by
  intro w
  by_cases hpU : p ∈ unop U
  · exact (toLineFun_eq_zero_iff D hp ⟨⟨hpU⟩⟩ s).mp (h ⟨⟨hpU⟩⟩)
  · exact mem_carrier_sub_single D hpU (s.2 w)

/-- Any rational function in `𝔪_p^{-D p}` is a section of `𝒪ₓ(D)` on a small enough
neighbourhood of `p`: shrink so that the only supported point specializing into the
neighbourhood is `p` itself. This replaces the unit-lifting construction of the
uniformizer-based design: representatives of classes in the line are already sections. -/
lemma exists_carrier_of_mem_ordSubmodule (hD : support D ⊆ {x | coheight x = 1})
    {f : ↑X.functionField} (hf : f ∈ ordSubmodule hp (-D p)) :
    ∃ (V : X.Opens) (_ : p ∈ V), f ∈ Sheaf.carrier D V := by
  classical
  rcases eq_or_ne f 0 with rfl | hne
  · exact ⟨⊤, trivial, Sheaf.zero_mem' D ⊤⟩
  obtain ⟨Uh, hUh1, hUh2, hUh3⟩ :=
    Function.locallyFinsupp.exists_nhd_mem_support_implies_specializes (div f) p
  obtain ⟨UD, hUD1, hUD2, hUD3⟩ :=
    Function.locallyFinsupp.exists_nhd_mem_support_implies_specializes D p
  set V : X.Opens := ⟨Uh ∩ UD, hUh1.inter hUD1⟩ with hV_def
  have hpV : p ∈ V := ⟨hUh2, hUD2⟩
  have spec_eq : ∀ (z : X), coheight z = 1 → z ⤳ p → z = p :=
    fun z hz hspec => hspec.eq_of_coheight_eq_one hz hp
  refine ⟨V, hpV, fun _ => ⟨⟨⟨p, hpV⟩⟩, fun z => ?_⟩⟩
  simp only [Function.locallyFinsuppWithin.coe_zero, Pi.zero_apply,
    Function.locallyFinsuppWithin.coe_add, Pi.add_apply, restrict_apply]
  split_ifs with hzV
  · by_cases hzp : z = p
    · subst hzp
      have h1 := hf hne
      simp only [div_eq_ord]
      omega
    · have hdiv_z : (div f) z = 0 := by
        by_cases hzcoh : coheight z = 1
        · by_contra hord
          exact hzp (spec_eq z hzcoh (hUh3 z ⟨hzV.1, hord⟩))
        · simp [div_eq_ord, Scheme.ord_eq_zero_of_coheight_neq_one hzcoh]
      have hD_z : D z = 0 := by
        by_contra hD'
        have hzcoh : coheight z = 1 := hD hD'
        exact hzp (spec_eq z hzcoh (hUD3 z ⟨hzV.2, hD'⟩))
      rw [hdiv_z, hD_z]
      simp
  · simp

end Kernel

/-! ### The canonical short exact sequence -/

section Complex

variable [IsLocallyNoetherian X] [IsRegularInCodimensionOne X]
variable (D : AlgebraicCycle X ℤ) {p : X} (hp : coheight p = 1)

open Classical in
omit [IsIntegral X] [IsLocallyNoetherian X] [IsRegularInCodimensionOne X] in
/-- `D - single p 1 ≤ D`. -/
lemma sub_single_le : D - single p 1 ≤ D :=
  sub_le_self D (single_nonneg.mpr Int.one_nonneg)

omit [IsIntegral X] [IsLocallyNoetherian X] [IsRegularInCodimensionOne X] in
/-- Applying the zero morphism of sheaves of modules gives zero. -/
lemma zero_hom_app_apply {A B : X.Modules} (U : (TopologicalSpace.Opens ↥X)ᵒᵖ)
    (a : ↑(A.val.obj U)) : (((0 : A ⟶ B)).val.app U) a = 0 := by
  rw [show ((0 : A ⟶ B)).val = 0 from rfl, PresheafOfModules.zero_app]
  rfl

/-- The inclusion `𝒪ₓ(D₁) ⟶ 𝒪ₓ(D₂)` as a morphism of sheaves of modules. -/
noncomputable def extendLeSheaf {D₁ D₂ : AlgebraicCycle X ℤ} (hle : D₁ ≤ D₂) :
    sheaf (X := X) D₁ ⟶ sheaf D₂ :=
  ⟨extendLe hle⟩

/-- The inclusion `𝒪ₓ(D₁) ⟶ 𝒪ₓ(D₂)` is a monomorphism of sheaves of modules. -/
instance extendLeSheaf_mono {D₁ D₂ : AlgebraicCycle X ℤ} (hle : D₁ ≤ D₂) :
    Mono (extendLeSheaf hle) := by
  suffices h : ∀ (U : (TopologicalSpace.Opens ↥X)ᵒᵖ),
      Function.Injective ((extendLe hle).app U) by
    suffices Mono ((SheafOfModules.toSheaf X.ringCatSheaf).map (extendLeSheaf hle)) by
      cat_disch
    exact Sheaf.mono_of_injective _ h
  intro U a b hab
  have h1 := congrArg Subtype.val hab
  exact Subtype.ext h1

open Classical in
/-- The canonical complex `0 ⟶ 𝒪ₓ(D - p) ⟶ 𝒪ₓ(D) ⟶ Q_p(D)`. No hypothesis on the support
of `D` and no choice of uniformizer is needed to define it. -/
noncomputable def twistedClosedSubschemeComplex : ShortComplex X.Modules where
  X₁ := sheaf (D - single p 1)
  X₂ := sheaf D
  X₃ := residueLineSheaf hp D
  f := extendLeSheaf (sub_single_le D)
  g := toLineHom D hp
  zero := by
    apply SheafOfModules.Hom.ext
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.hom_ext
    ext s
    refine pi_ext _ fun x => ?_
    have hL := pi_lift_π_apply (fun _ => AddCommGrpCat.of (residueLine hp D))
      (toLineComponent D hp U) x ((extendLe (sub_single_le D)).app U s)
    have hR : (Pi.π (fun _ => AddCommGrpCat.of (residueLine hp D)) x).hom
        (((0 : sheaf (D - single p 1) ⟶ residueLineSheaf hp D).val.app U) s) = 0 :=
      (congrArg _ (zero_hom_app_apply U s)).trans (map_zero _)
    exact (hL.trans ((toLineFun_eq_zero_iff D hp x _).mpr (s.2 _))).trans hR.symm

open Classical in
/-- The sequence `0 ⟶ 𝒪ₓ(D - p) ⟶ 𝒪ₓ(D) ⟶ Q_p(D)` is exact: the inclusion is a kernel of
the quotient map, by factoring test morphisms through `Submodule.liftOfLE`. -/
lemma twistedClosedSubschemeComplex_exact :
    (twistedClosedSubschemeComplex D hp).Exact := by
  haveI : Mono (twistedClosedSubschemeComplex D hp).f := extendLeSheaf_mono _
  apply ShortComplex.exact_of_f_is_kernel
  refine KernelFork.IsLimit.ofι' _ _ fun {A} k hk => ⟨⟨?lift⟩, ?fac⟩
  case lift =>
    refine PresheafOfModules.Submodule.liftOfLE (divisorSubmodule_mono (sub_single_le D))
      k.val fun U a => mem_sub_of_forall_toLineFun_eq_zero D hp _ fun x => ?_
    have h0 := congrArg (fun (ψ : A ⟶ residueLineSheaf hp D) =>
      (Pi.π (fun _ => AddCommGrpCat.of (residueLine hp D)) x).hom ((ψ.val.app U) a)) hk
    have hR : (Pi.π (fun _ => AddCommGrpCat.of (residueLine hp D)) x).hom
        (((0 : A ⟶ residueLineSheaf hp D).val.app U) a) = 0 :=
      (congrArg _ (zero_hom_app_apply U a)).trans (map_zero _)
    exact (pi_lift_π_apply _ _ x _).symm.trans (h0.trans hR)
  case fac =>
    apply SheafOfModules.Hom.ext
    exact PresheafOfModules.Submodule.liftOfLE_comp_homOfLE _ k.val _

open Classical in
/-- The canonical complex `0 ⟶ 𝒪ₓ(D - p) ⟶ 𝒪ₓ(D) ⟶ Q_p(D) ⟶ 0` is short exact, given that
`D` is supported in codimension one and `p` is a closed point. -/
lemma twistedClosedSubschemeComplex_shortExact
    (hD : support D ⊆ {x | coheight x = 1}) (pClosed : ∀ x : X, x ≤ p → x = p) :
    (twistedClosedSubschemeComplex D hp).ShortExact where
  exact := twistedClosedSubschemeComplex_exact D hp
  mono_f := extendLeSheaf_mono _
  epi_g := by
    have h : Sheaf.IsLocallySurjective
        ((SheafOfModules.toSheaf X.ringCatSheaf).map (toLineHom D hp)) := by
      refine (TopCat.Presheaf.isLocallySurjective_iff _).mpr ?_
      intro U t z hzU
      by_cases hzp : z = p
      · -- At `p` itself, a representative of the class of `t` is a section on a small enough
        -- neighbourhood.
        have hpU : p ∈ U := hzp ▸ hzU
        obtain ⟨⟨f, hfM⟩, hy⟩ := residueLine.mk_surjective hp D (evalLine hp D ⟨⟨hpU⟩⟩ t)
        obtain ⟨V₀, hpV₀, hcar⟩ := exists_carrier_of_mem_ordSubmodule D hp hD hfM
        have hpW : p ∈ V₀ ⊓ U := ⟨hpV₀, hpU⟩
        haveI : Nonempty ↑(V₀ ⊓ U) := ⟨⟨p, hpW⟩⟩
        have hmem : constSection (U := op (V₀ ⊓ U)) f ∈
            (divisorSubmodule D).obj (op (V₀ ⊓ U)) :=
          fun w => Sheaf.mem_carrier_of_le D inf_le_left
            (by rw [eval_constSection]; exact hcar)
        refine ⟨V₀ ⊓ U, inf_le_right, ⟨⟨constSection f, hmem⟩, ?_⟩, hzp ▸ hpW⟩
        -- Both sides of the required equality have the same components.
        refine pi_ext _ fun x' => ?_
        have hL := pi_lift_π_apply (fun _ => AddCommGrpCat.of (residueLine hp D))
          (fun x => toLineComponent D hp (op (V₀ ⊓ U)) x) x' ⟨constSection f, hmem⟩
        have hres : toLineFun D hp x'
            (⟨constSection f, hmem⟩ : ↑((presheaf D).obj (op (V₀ ⊓ U)))) =
            evalLine hp D ⟨⟨hpU⟩⟩ t := by
          rw [toLineFun, ← hy]
          exact congrArg _ (Subtype.ext (eval_constSection _ f))
        refine (hL.trans hres).trans ?_
        exact ((evalLine_map hp D (homOfLE (inf_le_right : V₀ ⊓ U ≤ U)).op x' t).trans
          rfl).symm
      · -- Away from `p`, shrink to a neighbourhood avoiding `p`, where the skyscraper has
        -- no nonzero sections.
        have hzc : z ∉ closure ({p} : Set X) := fun hmem =>
          hzp (pClosed z (Scheme.le_iff_specializes.mpr
            (specializes_iff_mem_closure.mpr hmem)))
        refine ⟨U ⊓ ⟨(closure ({p} : Set X))ᶜ, isClosed_closure.isOpen_compl⟩, inf_le_left,
          ⟨0, ?_⟩, ⟨hzU, hzc⟩⟩
        have hpV : p ∉ (U ⊓ ⟨(closure ({p} : Set X))ᶜ,
            isClosed_closure.isOpen_compl⟩ : X.Opens) :=
          fun hpv => hpv.2 (subset_closure rfl)
        exact @Subsingleton.elim _
          (AddCommGrpCat.subsingleton_of_isZero
            (skyscraperPresheaf_obj_isZero p (AddCommGrpCat.of (residueLine hp D)) hpV)) _ _
    exact (SheafOfModules.toSheaf X.ringCatSheaf).epi_of_epi_map
      ((CategoryTheory.Sheaf.isLocallySurjective_iff_epi'
        (φ := (SheafOfModules.toSheaf X.ringCatSheaf).map (toLineHom D hp))).mp h)

open Classical in
omit [IsIntegral X] [IsLocallyNoetherian X] [IsRegularInCodimensionOne X] in
/-- If `D` is supported in codimension one and `D' - D = single p 1` for a codimension-one
`p`, then so is `D'`. -/
lemma support_subset_of_sub_eq_single {D D' : AlgebraicCycle X ℤ}
    (hD : support D ⊆ {x | coheight x = 1}) (hp : coheight p = 1)
    (hD' : D' - D = single p 1) : support D' ⊆ {x | coheight x = 1} := by
  obtain rfl : D' = D + single p 1 := by rw [← hD']; abel
  exact Function.locallyFinsupp.support_add_single_subset hD hp

open Classical in
/-- `0 ⟶ 𝒪ₓ(D') ⟶ 𝒪ₓ(D) ⟶ Q_p(D)` where `D - D' = single p 1`; the cokernel sits on the
larger divisor `D`. Definitionally `twistedClosedSubschemeComplex` at `D`. -/
noncomputable def twistedClosedSubschemeComplex₁ {D D' : AlgebraicCycle X ℤ}
    (hp : coheight p = 1) (hD' : D - D' = single p 1) :
    ShortComplex X.Modules where
  X₁ := sheaf D'
  X₂ := sheaf D
  X₃ := residueLineSheaf hp D
  f := extendLeSheaf (by rw [← sub_nonneg, hD']; exact single_nonneg.mpr Int.one_nonneg)
  g := toLineHom D hp
  zero := by
    obtain rfl : D' = D - single p 1 := by rw [← hD']; abel
    exact (twistedClosedSubschemeComplex D hp).zero

open Classical in
/-- `twistedClosedSubschemeComplex₁` is short exact. -/
lemma twistedClosedSubschemeComplex₁_shortExact {D D' : AlgebraicCycle X ℤ}
    (hD : support D ⊆ {x | coheight x = 1}) (hp : coheight p = 1)
    (hD' : D - D' = single p 1) (pClosed : ∀ x : X, x ≤ p → x = p) :
    (twistedClosedSubschemeComplex₁ (p := p) hp hD').ShortExact := by
  obtain rfl : D' = D - single p 1 := by rw [← hD']; abel
  exact twistedClosedSubschemeComplex_shortExact D hp hD pClosed

open Classical in
/-- `0 ⟶ 𝒪ₓ(D) ⟶ 𝒪ₓ(D') ⟶ Q_p(D')` where `D' - D = single p 1`; the cokernel sits on the
larger divisor `D'`. Definitionally `twistedClosedSubschemeComplex` at `D'`. -/
noncomputable def twistedClosedSubschemeComplex₂ {D D' : AlgebraicCycle X ℤ}
    (hp : coheight p = 1) (hD' : D' - D = single p 1) :
    ShortComplex X.Modules where
  X₁ := sheaf D
  X₂ := sheaf D'
  X₃ := residueLineSheaf hp D'
  f := extendLeSheaf (by rw [← sub_nonneg, hD']; exact single_nonneg.mpr Int.one_nonneg)
  g := toLineHom D' hp
  zero := by
    obtain rfl : D = D' - single p 1 := by rw [← hD']; abel
    exact (twistedClosedSubschemeComplex D' hp).zero

open Classical in
/-- `twistedClosedSubschemeComplex₂` is short exact. -/
lemma twistedClosedSubschemeComplex₂_shortExact {D D' : AlgebraicCycle X ℤ}
    (hD : support D ⊆ {x | coheight x = 1}) (hp : coheight p = 1)
    (hD' : D' - D = single p 1) (pClosed : ∀ x : X, x ≤ p → x = p) :
    (twistedClosedSubschemeComplex₂ (p := p) hp hD').ShortExact := by
  have hsupp := support_subset_of_sub_eq_single (p := p) hD hp hD'
  obtain rfl : D = D' - single p 1 := by rw [← hD']; abel
  exact twistedClosedSubschemeComplex_shortExact D' hp hsupp pClosed

end Complex

/-! ### Trivializing the line: the residue field appears

A choice of uniformizer `ϖ` of `𝒪_{X,p}` identifies the line `L_p(D)` with the residue field:
the class of `f` maps to the residue of the lift of `ϖ ^ D p * f` along `𝒪_{X,p} → k(X)`.
This is where (and only where) the uniformizer-dependence of the classical presentation lives;
different choices of `ϖ` change the identification by a unit of `κ(p)`.
-/

section Trivialization

variable [IsLocallyNoetherian X] [IsRegularInCodimensionOne X]
variable {p : X} (hp : coheight p = 1)

/-- The residue field as a module over the local ring, with `r` acting by multiplication by
its residue. -/
noncomputable instance : Module ↑(X.presheaf.stalk p) ↑(X.residueField p) :=
  letI : Module (IsLocalRing.ResidueField ↑(X.presheaf.stalk p)) ↑(X.residueField p) :=
    inferInstanceAs (Module ↑(X.residueField p) ↑(X.residueField p))
  Module.compHom _ (IsLocalRing.residue (X.presheaf.stalk p))

/-- The preimage in the local ring at a codimension-one point of a rational function of
nonnegative order (which exists by `mem_range_algebraMap_iff_ord_nonneg`). -/
noncomputable def stalkPreimage (h : ↑X.functionField) (hh : h ≠ 0 → 0 ≤ X.ord h p) :
    ↑(X.presheaf.stalk p) :=
  ((mem_range_algebraMap_iff_ord_nonneg hp h).mpr hh).choose

@[simp]
lemma algebraMap_stalkPreimage (h : ↑X.functionField) (hh : h ≠ 0 → 0 ≤ X.ord h p) :
    algebraMap (X.presheaf.stalk p) X.functionField (stalkPreimage hp h hh) = h :=
  ((mem_range_algebraMap_iff_ord_nonneg hp h).mpr hh).choose_spec

/-- The preimage is whatever maps to `h`; all properties of `stalkPreimage` follow from this
and injectivity of `𝒪_{X,p} → k(X)`. -/
lemma stalkPreimage_eq (h : ↑X.functionField) (hh : h ≠ 0 → 0 ≤ X.ord h p)
    {a : ↑(X.presheaf.stalk p)} (ha : algebraMap (X.presheaf.stalk p) X.functionField a = h) :
    stalkPreimage hp h hh = a :=
  FaithfulSMul.algebraMap_injective (X.presheaf.stalk p) X.functionField
    (by rw [algebraMap_stalkPreimage, ha])

omit [IsIntegral X] [IsLocallyNoetherian X] [IsRegularInCodimensionOne X] in
lemma residue_hom_eq_zero_iff {a : ↑(X.presheaf.stalk p)} :
    (X.residue p).hom a = 0 ↔ a ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk p) :=
  IsLocalRing.residue_eq_zero_iff a

variable (D : AlgebraicCycle X ℤ) {ϖ : X.presheaf.stalk p} (hϖ : Irreducible ϖ)

include hp hϖ in
/-- The order bound making `ϖ ^ D p * f` lift to the local ring. -/
lemma ord_zpow_mul_nonneg {f : ↑X.functionField} (hf : f ≠ 0 → -D p ≤ X.ord f p) :
    (algebraMap (X.presheaf.stalk p) X.functionField ϖ) ^ (D p) * f ≠ 0 →
      0 ≤ X.ord ((algebraMap (X.presheaf.stalk p) X.functionField ϖ) ^ (D p) * f) p :=
  fun hne => by
    have hf0 : f ≠ 0 := right_ne_zero_of_mul hne
    rw [X.ord_mul hp (zpow_ne_zero _ (algebraMap_functionField_ne_zero hϖ.ne_zero)) hf0,
      ord_zpow_algebraMap_irreducible hp hϖ]
    have := hf hf0
    omega

/-- The residue at `p` of `ϖ ^ D p * f`, for `f` satisfying the divisor bound at `p`. -/
noncomputable def residueAux (f : ↑X.functionField) (hf : f ≠ 0 → -D p ≤ X.ord f p) :
    ↑(X.residueField p) :=
  (X.residue p).hom (stalkPreimage hp
    ((algebraMap (X.presheaf.stalk p) X.functionField ϖ) ^ (D p) * f)
    (ord_zpow_mul_nonneg hp D hϖ hf))

/-- `residueAux` does not depend on the bound proof (so equal functions give equal values). -/
lemma residueAux_apply_eq {f g : ↑X.functionField} (hfg : f = g)
    (hf : f ≠ 0 → -D p ≤ X.ord f p) (hg : g ≠ 0 → -D p ≤ X.ord g p) :
    residueAux hp D hϖ f hf = residueAux hp D hϖ g hg := by
  subst hfg
  rfl

lemma residueAux_zero (hf : (0 : ↑X.functionField) ≠ 0 → -D p ≤ X.ord 0 p) :
    residueAux hp D hϖ 0 hf = 0 := by
  rw [residueAux, stalkPreimage_eq hp _ _ (a := 0) (by simp), map_zero]

lemma residueAux_add (f g : ↑X.functionField)
    (hf : f ≠ 0 → -D p ≤ X.ord f p) (hg : g ≠ 0 → -D p ≤ X.ord g p)
    (hfg : f + g ≠ 0 → -D p ≤ X.ord (f + g) p) :
    residueAux hp D hϖ (f + g) hfg = residueAux hp D hϖ f hf + residueAux hp D hϖ g hg := by
  rw [residueAux, residueAux, residueAux, ← map_add,
    stalkPreimage_eq hp _ _
      (a := stalkPreimage hp _ (ord_zpow_mul_nonneg hp D hϖ hf) +
        stalkPreimage hp _ (ord_zpow_mul_nonneg hp D hϖ hg))
      (by rw [map_add, algebraMap_stalkPreimage, algebraMap_stalkPreimage]; ring)]

/-- `residueAux` intertwines the `𝒪_{X,p}`-action with multiplication by the residue. -/
lemma residueAux_algebraMap_smul (r : ↑(X.presheaf.stalk p)) (f : ↑X.functionField)
    (hf : f ≠ 0 → -D p ≤ X.ord f p)
    (hrf : algebraMap (X.presheaf.stalk p) X.functionField r * f ≠ 0 →
      -D p ≤ X.ord (algebraMap (X.presheaf.stalk p) X.functionField r * f) p) :
    residueAux hp D hϖ (algebraMap (X.presheaf.stalk p) X.functionField r * f) hrf =
      (X.residue p).hom r * residueAux hp D hϖ f hf := by
  have hpre : stalkPreimage hp _ (ord_zpow_mul_nonneg hp D hϖ hrf) =
      r * stalkPreimage hp _ (ord_zpow_mul_nonneg hp D hϖ hf) := by
    refine stalkPreimage_eq hp _ _ ?_
    rw [map_mul, algebraMap_stalkPreimage]
    ring
  rw [residueAux, residueAux, hpre, map_mul]

lemma residueAux_eq_zero_iff {f : ↑X.functionField} (hf0 : f ≠ 0)
    (hf : f ≠ 0 → -D p ≤ X.ord f p) :
    residueAux hp D hϖ f hf = 0 ↔ 1 ≤ D p + X.ord f p := by
  have hϖK : (algebraMap (X.presheaf.stalk p) X.functionField ϖ) ^ (D p) ≠ 0 :=
    zpow_ne_zero _ (algebraMap_functionField_ne_zero hϖ.ne_zero)
  have ha0 : stalkPreimage hp _ (ord_zpow_mul_nonneg hp D hϖ hf) ≠ 0 := fun h0 =>
    mul_ne_zero hϖK hf0
      (by rw [← algebraMap_stalkPreimage hp _ (ord_zpow_mul_nonneg hp D hϖ hf), h0, map_zero])
  rw [residueAux, residue_hom_eq_zero_iff, mem_maximalIdeal_iff_one_le_ord hp ha0,
    algebraMap_stalkPreimage, X.ord_mul hp hϖK hf0, ord_zpow_algebraMap_irreducible hp hϖ]

/-- `residueAux`, as an `𝒪_{X,p}`-linear map on the fractional ideal `𝔪_p^{-D p}`. -/
noncomputable def residueAuxHom :
    ↥(ordSubmodule hp (-D p)) →ₗ[↑(X.presheaf.stalk p)] ↑(X.residueField p) where
  toFun f := residueAux hp D hϖ f.1 f.2
  map_add' f g := residueAux_add hp D hϖ f.1 g.1 f.2 g.2 (f + g).2
  map_smul' r f := by
    refine ((residueAux_apply_eq hp D hϖ (Algebra.smul_def r f.1) (r • f).2
      ((Algebra.smul_def r f.1) ▸ (r • f).2)).trans
      (residueAux_algebraMap_smul hp D hϖ r f.1 f.2 _)).trans ?_
    rfl

/-- **Trivialization of the line.** A uniformizer `ϖ` of `𝒪_{X,p}` induces an isomorphism
`L_p(D) ≃ κ(p)`, sending the class of `f` to the residue of the lift of `ϖ ^ D p * f`.
Different uniformizers change this isomorphism by a unit of `κ(p)`; the line itself, and the
short exact sequence above, are canonical. -/
noncomputable def residueLineEquiv :
    residueLine hp D ≃ₗ[↑(X.presheaf.stalk p)] ↑(X.residueField p) := by
  refine LinearEquiv.ofBijective
    (Submodule.liftQ _ (residueAuxHom hp D hϖ) fun f hf => ?_) ⟨?_, ?_⟩
  · -- the extra order bound kills the residue
    have h1 : f.1 ∈ ordSubmodule hp (1 - D p) := Submodule.mem_comap.mp hf
    rcases eq_or_ne f.1 0 with h0 | h0
    · exact (residueAux_apply_eq hp D hϖ h0 f.2 (fun hne => absurd rfl hne)).trans
        (residueAux_zero hp D hϖ _)
    · refine (residueAux_eq_zero_iff hp D hϖ h0 f.2).mpr ?_
      have := h1 h0
      omega
  · -- injectivity: a vanishing residue forces the extra order bound
    intro x y hxy
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    rw [Submodule.Quotient.eq]
    have h0 : residueAuxHom hp D hϖ (x - y) = 0 := by
      rw [map_sub, sub_eq_zero]
      exact (Submodule.liftQ_apply _ _ x).symm.trans
        (hxy.trans (Submodule.liftQ_apply _ _ y))
    refine Submodule.mem_comap.mpr ?_
    rcases eq_or_ne (x - y).1 0 with hd0 | hd0
    · exact fun hne => absurd hd0 hne
    · intro _
      have h2 := (residueAux_eq_zero_iff hp D hϖ hd0 (x - y).2).mp h0
      exact (by omega : 1 - D p ≤ X.ord ((x - y).1) p)
  · -- surjectivity: lift a residue class to a unit `a` and use `ϖ ^ (-D p) * a`
    intro y
    rcases eq_or_ne y 0 with rfl | hy
    · exact ⟨0, map_zero _⟩
    haveI : IsDiscreteValuationRing (X.presheaf.stalk p) :=
      IsRegularInCodimensionOne.stalk_dvr p hp
    obtain ⟨a, ha⟩ := IsLocalRing.residue_surjective (R := X.presheaf.stalk p) y
    have haU : IsUnit a := by
      rw [← IsLocalRing.notMem_maximalIdeal, ← IsLocalRing.residue_eq_zero_iff, ha]
      exact hy
    have ha0 : a ≠ 0 := haU.ne_zero
    have hϖK : algebraMap (X.presheaf.stalk p) X.functionField ϖ ≠ 0 :=
      algebraMap_functionField_ne_zero hϖ.ne_zero
    have hKa : algebraMap (X.presheaf.stalk p) X.functionField a ≠ 0 :=
      algebraMap_functionField_ne_zero ha0
    have ha_ord : X.ord (algebraMap (X.presheaf.stalk p) X.functionField a) p = 0 := by
      have h1 : ¬ (1 ≤ X.ord (algebraMap (X.presheaf.stalk p) X.functionField a) p) := by
        rw [← mem_maximalIdeal_iff_one_le_ord hp ha0, IsLocalRing.mem_maximalIdeal,
          mem_nonunits_iff, not_not]
        exact haU
      have h2 := ord_algebraMap_nonneg hp ha0
      omega
    set h : ↑X.functionField :=
      (algebraMap (X.presheaf.stalk p) X.functionField ϖ) ^ (-(D p)) *
        algebraMap (X.presheaf.stalk p) X.functionField a with hh_def
    have hne : h ≠ 0 := mul_ne_zero (zpow_ne_zero _ hϖK) hKa
    have hh_ord : X.ord h p = -(D p) := by
      rw [hh_def, X.ord_mul hp (zpow_ne_zero _ hϖK) hKa,
        ord_zpow_algebraMap_irreducible hp hϖ, ha_ord, add_zero]
    -- `ϖ ^ D p * h = a`, whose residue is `y`.
    have hcollapse : algebraMap (X.presheaf.stalk p) X.functionField a =
        (algebraMap (X.presheaf.stalk p) X.functionField ϖ) ^ (D p) * h := by
      rw [hh_def, ← mul_assoc, ← zpow_add₀ hϖK, add_neg_cancel, zpow_zero, one_mul]
    refine ⟨Submodule.Quotient.mk ⟨h, fun _ => hh_ord.ge⟩, ?_⟩
    rw [Submodule.liftQ_apply]
    exact Eq.trans (congrArg (X.residue p).hom
      (stalkPreimage_eq hp _ _ (a := a) hcollapse)) ha

/-- A uniformizer induces an isomorphism between the
canonical cokernel `Q_p(D)` and the residue-field skyscraper. Euler-characteristic arguments
need only the existence of this isomorphism. -/
noncomputable def residueLineSheafIso :
    residueLineSheaf hp D ≅ skyscraperSheafOfModules p X.ringCatSheaf ↑(X.residueField p) :=
  ((Opens.pointGrothendieckTopology p).skyscraperSheafOfModulesFunctor
    X.ringCatSheaf).mapIso
    (LinearEquiv.toModuleIso
      (AddEquiv.toLinearEquiv (residueLineEquiv hp D hϖ).toAddEquiv fun r m =>
        (residueLineEquiv hp D hϖ).map_smul
          (stalkCompare p ((pointPresheafFiberToStalk p X.ringCatSheaf).hom r)) m))

end Trivialization

end SheafViaSubmodule
end AlgebraicGeometry.AlgebraicCycle
