/-
Copyright (c) 2026 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
module

public import Mathlib.Algebra.RingQuot
public import Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Formula
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
public import Mathlib.AlgebraicGeometry.Sites.BigZariski
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.RingTheory.MvPolynomial.Homogeneous

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u v w

noncomputable section

namespace CategoryTheory

variable {C : Type*} [Category* C] (J : GrothendieckTopology C)
variable {D : Type*} [Category* D]

section ConcreteCategory

variable {FD : D → D → Type*} {CD : D → Type*}
  [∀ X Y, FunLike (FD X Y) (CD X) (CD Y)] [ConcreteCategory D FD]

open Presheaf in
def IsSheafification {F G : Cᵒᵖ ⥤ D} (f : F ⟶ G) : Prop :=
  IsSheaf J G ∧ IsLocallyInjective J f ∧ IsLocallySurjective J f

variable {J}

def IsSheafification.congr_left {F₁ F₂ G : Cᵒᵖ ⥤ D} {f : F₂ ⟶ G} (i : F₁ ⟶ F₂) [IsIso i]
    (hf : IsSheafification J f) : IsSheafification J (i ≫ f) :=
  sorry

def IsSheafification.congr_right {F G₁ G₂ : Cᵒᵖ ⥤ D} {f : F ⟶ G₁} (i : G₁ ⟶ G₂) [IsIso i]
    (hf : IsSheafification J f) : IsSheafification J (f ≫ i) :=
  sorry

def IsSheafification.homEquiv {F G H : Cᵒᵖ ⥤ D} {f : F ⟶ G} (hf : IsSheafification J f)
    (hH : Presheaf.IsSheaf J H) : (F ⟶ H) ≃ (G ⟶ H) where
  toFun := sorry
  invFun g := f ≫ g
  left_inv := sorry
  right_inv := sorry

instance (X : C) [J.Subcanonical] : (J.over X).Subcanonical := sorry
  -- CategoryTheory.Sheaf.over ?

-- not needed
instance (X : C) [HasWeakSheafify J D] : HasWeakSheafify (J.over X) D := sorry

end ConcreteCategory

variable (F G : C ⥤ Type*)

def Functor.typeProd : C ⥤ Type _ where
  obj X := F.obj X × G.obj X
  map f := Prod.map (F.map f) (G.map f)

instance : SProd (Subfunctor F) (Subfunctor G) (Subfunctor (F.typeProd G)) where
  sprod f g :=
  { obj X := f.obj X ×ˢ g.obj X
    map _ _ h := ⟨f.map _ h.1, g.map _ h.2⟩ }

variable {F G} in
def Subfunctor.toFunctorProdIso (f : Subfunctor F) (g : Subfunctor G) :
    (f ×ˢ g).toFunctor ≅ f.toFunctor.typeProd g.toFunctor where
  hom := { app X x := (⟨x.1.1, x.2.1⟩, ⟨x.1.2, x.2.2⟩) }
  inv := { app X x := ⟨(x.1.1, x.2.1), x.1.2, x.2.2⟩ }

def NatTrans.typeProd {F F' : C ⥤ Type u} {G G' : C ⥤ Type v} (f : F ⟶ F') (g : G ⟶ G') :
    F.typeProd G ⟶ F'.typeProd G' where
  app X := Prod.map (f.app X) (g.app X)
  naturality _ _ h := by
    ext x
    exact Prod.ext congr($(f.naturality h) _) congr($(g.naturality h) _)

variable {J}

theorem Presheaf.IsSheaf.typeProd {F G : Cᵒᵖ ⥤ Type u} (hF : IsSheaf J F) (hG : IsSheaf J G) :
    IsSheaf J (F.typeProd G) := by
  sorry

theorem IsSheafification.typeProd {F F' G G' : Cᵒᵖ ⥤ Type u} {f : F ⟶ F'} {g : G ⟶ G'}
    (hf : IsSheafification J f) (hg : IsSheafification J g) :
    IsSheafification J (NatTrans.typeProd f g) := by
  sorry

open Limits

/- Can't be used in the following due to defeq issue: composition of a by-cases definition with
a function is not a by-cases definition using compositions.
CategoryTheory.Limits.mapPairIso/diagramIsoPair/pairComp provide workarounds. -/
def Limits.binaryProductLimitCone (α β : Type u) : LimitCone (pair α β) where
  cone :=
  { pt := α × β
    π := { app | ⟨.left⟩ => (·.fst) | ⟨.right⟩ => (·.snd),
           naturality := by rintro ⟨_ | _⟩ ⟨_ | _⟩ (_ | _) <;> rfl } }
  isLimit := BinaryFan.IsLimit.mk _ (fun f g x ↦ (f x, g x)) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)
    fun f g m hf hg ↦ funext fun _ ↦ Prod.ext congr($hf _) congr($hg _)

def Functor.typeProdLimitCone (F G : C ⥤ Type u) : LimitCone (pair F G) where
  cone := combineCones _ fun X ↦
  { cone :=
    { pt := F.obj X × G.obj X
      π := { app | ⟨.left⟩ => (·.fst) | ⟨.right⟩ => (·.snd)
             naturality := by rintro ⟨_ | _⟩ ⟨_ | _⟩ (_ | _) <;> rfl } }
    isLimit := .postcomposeHomEquiv (diagramIsoPair _) _ <| BinaryFan.IsLimit.mk _
      (fun f g x ↦ (f x, g x)) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)
      fun f g m hf hg ↦ funext fun _ ↦ Prod.ext congr($hf _) congr($hg _) }
  isLimit := combinedIsLimit ..
-- TODO?: Limits.LimitCone.postcomposeHomEquiv
-- see CategoryTheory.Limits.Cones.postcomposeEquivalence

theorem Functor.pt_typeProdLimitCone (F G : C ⥤ Type u) :
    (F.typeProdLimitCone G).cone.pt = F.typeProd G := rfl

def yonedaProd {X Y : C} {c : BinaryFan X Y} (hc : IsLimit c) :
    yoneda.obj c.pt ≅ (yoneda.obj X).typeProd (yoneda.obj Y) :=
  (isLimitOfPreserves yoneda hc).conePointsIsoOfEquivalence
    (Functor.typeProdLimitCone ..).isLimit .refl (pairComp ..).symm
/- Probably we also need to identify the maps
from yoneda.obj (X ⨯ Y) to yoneda.obj X and yoneda.obj Y -/

end CategoryTheory

open scoped SpecOfNotation
instance (R : Type*) [CommRing R] (X : (Over Spec(R))ᵒᵖ) :
    Algebra R (Scheme.Γ.obj <| (Over.forget _).op.obj X) :=
  RingHom.toAlgebra <| ((ΓSpec.adjunction.homEquiv ..).symm X.unop.hom).unop.hom

namespace AlgebraicGeometry.Proj

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A] (𝒜 : ℕ → Submodule R A)
variable [GradedAlgebra 𝒜]

def structureMorphism : Proj 𝒜 ⟶ Spec (.of R) :=
  Proj.toSpecZero 𝒜 ≫ Spec.map (CommRingCat.ofHom (algebraMap ..))
  -- ΓSpec.adjunction.homEquiv _ _ (.op sorry) ?

end AlgebraicGeometry.Proj

namespace AlgebraicGeometry.ProjectiveSpace

variable (n : ℕ)

-- This is currently `WeierstrassCurve.Projective.PointClass`
def PointClass (R : Type*) [Monoid R] :=
  MulAction.orbitRel.Quotient Rˣ (Fin n → R)

variable {n} in
def PointClass.ExistsUnit {R : Type*} [Monoid R] : PointClass n R → Prop :=
  Quotient.lift (fun x ↦ ∃ i, IsUnit (x i)) sorry

variable {n} in
def PointClass.SpanEqTop {R : Type*} [Semiring R] : PointClass n R → Prop :=
  Quotient.lift (fun x ↦ Ideal.span (Set.range x) = ⊤) sorry

def functor : CommRingCat ⥤ Type _ where
  obj R := PointClass n R
  map f := Quotient.map (Pi.map fun _ ↦ f) sorry

def subfunctor : Subfunctor (functor n) where
  obj R := {x | x.ExistsUnit}
  map i := sorry

def presheaf : Schemeᵒᵖ ⥤ Type _ := Scheme.Γ ⋙ functor n

def subpresheaf : Subfunctor (presheaf n) where
  obj R := {x | x.ExistsUnit}
  map i := sorry

variable (R₀ : Type*) [CommRing R₀]

attribute [local instance] MvPolynomial.gradedAlgebra

abbrev scheme : Scheme := Proj (MvPolynomial.homogeneousSubmodule (Fin n) R₀)

def schemeOver : Over Spec(R₀) := .mk (Y := scheme n R₀) (Proj.structureMorphism _)

-- not needed
def subpresheafToYoneda : (subpresheaf n).toFunctor ⟶ yoneda.obj (scheme n ℤ) :=
  sorry

-- not needed
theorem isSheafification_subpresheafToYoneda :
    IsSheafification Scheme.zariskiTopology (subpresheafToYoneda n) := by
  refine ⟨((GrothendieckTopology.yoneda _).obj _).2, ?_, ?_⟩
  · sorry
  · sorry

def presheafOver : (Over Spec(R₀))ᵒᵖ ⥤ Type _ := (Over.forget _).op ⋙ presheaf n

def subpresheafOver : Subfunctor (presheafOver n R₀) where
  obj X := {x | x.SpanEqTop}
  map := sorry

def subpresheafOverToYoneda : (subpresheafOver n R₀).toFunctor ⟶ yoneda.obj (schemeOver n R₀) :=
  sorry
/- Outline: to construct `X ⟶ Spec Γ(X) ⟶ ℙ^{n-1}` for X over Spec R₀, it suffices to construct
`Spec R ⟶ ℙ^{n-1}` for R over R₀. The coordinates of points (x₁, ⋯, xₙ) in `subpresheafOver n R₀`
spans the unit ideal, so Spec R[xᵢ⁻¹] form an open cover of Spec R. For each `i` we define a
morphism from Spec R[xᵢ⁻¹] to the `i`th affine chart ≅ 𝔸^{n-1} inside ℙ^{n-1}, and show they
glue up to form a morphism from Spec R to ℙ^{n-1}. -/

theorem isSheafification_subpresheafToYonedaOver :
    IsSheafification (Scheme.zariskiTopology.over _) (subpresheafOverToYoneda n R₀) := by
  refine ⟨((GrothendieckTopology.yoneda _).obj _).2, ?_, ?_⟩
  · sorry
  · sorry

end AlgebraicGeometry.ProjectiveSpace

namespace WeierstrassCurve.Projective

variable {R : Type u} [CommRing R] (W : WeierstrassCurve.Projective R)

/- `Nonsingular` is currently defined with `≠ 0` conditions instead of `IsUnit`.
When defined using `SpanEqTop PolynomialXYZ`, this implies `SpanEqTop P`;
if defined using `ExistsUnit PolynomialXYZ`, it doesn't imply `ExistsUnit P`. -/
def Nonsingular' (P : Fin 3 → R) : Prop :=
  W.Equation P ∧
  Ideal.span {W.polynomialX.eval P, W.polynomialY.eval P, W.polynomialZ.eval P} = ⊤
  --(IsUnit (W.polynomialX.eval P) ∨ IsUnit (W.polynomialY.eval P) ∨ IsUnit (W.polynomialZ.eval P))

theorem Nonsingular'.span_eq_top {P : Fin 3 → R} (hP : W.Nonsingular' P) :
    Ideal.span (Set.range P) = ⊤ := sorry

open AlgebraicGeometry ProjectiveSpace PointClass

-- TODO: replace `PointClass R` by `ProjectiveSpace.PointClass 3 R` everywhere
def EquationLift : PointClass R → Prop :=
  Quotient.lift W.Equation sorry
/- Note: if (x,y,z) satisfies Equation, then x³ ∈ span {y,z},
so span {x,y,z} = ⊤ ↔ span {y,z} = ⊤. -/

def Nonsingular'Lift : PointClass R → Prop :=
  Quotient.lift W.Nonsingular' sorry

theorem Nonsingular'Lift.spanEqTop {P : PointClass R} (hP : W.Nonsingular'Lift P) :
    SpanEqTop P := by rcases P; exact hP.span_eq_top

def point : Set (PointClass R) := {x | SpanEqTop x ∧ W.EquationLift x}

def nonsingularPoint : Set (PointClass R) := {x | W.Nonsingular'Lift x}

open ProjectiveSpace

/-- The presheaf $W_{pre}$. -/
def subpresheaf : Subfunctor (presheafOver 3 R) where
  obj X := (W.baseChange _).toProjective.point
  map := sorry

/-- The presheaf $W⁰_{pre}$. -/
def smoothSubpresheaf : Subfunctor (presheafOver 3 R) where
  obj X := (W.baseChange _).toProjective.nonsingularPoint
  map := sorry

theorem smoothSubpresheaf_le : W.smoothSubpresheaf ≤ W.subpresheaf := sorry

abbrev CoordinateRing : Type u := MvPolynomial (Fin 3) R ⧸ Ideal.span {W.polynomial}

/-- The projective scheme associated to a Weierstrass curve. -/
def scheme : Over Spec(R) := have := W; sorry
  -- to be defined as Proj W.CoordinateRing, pending #27307

def smoothOpens : W.scheme.1.Opens := sorry
-- union of three basic opens associated to the three derivatives

/-- The smooth locus in the projective scheme associated to a Weierstrass curve. -/
def smoothLocus : Over Spec(R) := .mk (W.smoothOpens.ι ≫ W.scheme.hom)

def subpresheafToYoneda : W.subpresheaf.toFunctor ⟶ yoneda.obj W.scheme := sorry

def smoothSubpresheafToYoneda : W.smoothSubpresheaf.toFunctor ⟶ yoneda.obj W.smoothLocus := sorry

abbrev smoothInclusion : W.smoothLocus ⟶ W.scheme := Over.homMk _

theorem subpresheafToYoneda_comm :
    Subfunctor.homOfLe W.smoothSubpresheaf_le ≫ W.subpresheafToYoneda =
    W.smoothSubpresheafToYoneda ≫ yoneda.map W.smoothInclusion := by
  sorry

open scoped MonoidalCategory

def prodToYoneda :
    (W.smoothSubpresheaf ×ˢ W.subpresheaf).toFunctor ⟶ yoneda.obj (W.smoothLocus ⊗ W.scheme) :=
  (Subfunctor.toFunctorProdIso ..).hom ≫
  W.smoothSubpresheafToYoneda.typeProd W.subpresheafToYoneda ≫
  (yonedaProd <| CartesianMonoidalCategory.tensorProductIsBinaryProduct ..).inv

theorem isSheafification_subpresheafToYoneda :
    IsSheafification (Scheme.zariskiTopology.over _) (subpresheafToYoneda W) := by
  sorry

theorem isSheafification_smoothSubpresheafToYoneda :
    IsSheafification (Scheme.zariskiTopology.over _) (smoothSubpresheafToYoneda W) := by
  sorry

theorem isSheafification_prodToYoneda :
    IsSheafification (Scheme.zariskiTopology.over _) (prodToYoneda W) :=
  ((W.isSheafification_smoothSubpresheafToYoneda.typeProd
    W.isSheafification_subpresheafToYoneda).congr_right _).congr_left _

def add₁ (P : PointClass R × PointClass R) : PointClass R :=
  Quotient.map₂ W.addXYZ sorry P.1 P.2

-- use corrected version of X^{(2)}, Y^{(2)} and Z^{(2)} in Bosma–Lenstra
def addXYZ' (P Q : Fin 3 → R) : Fin 3 → R := have := W; sorry

-- probably needs `W.Equation P`
theorem addXYZ'_self (P : Fin 3 → R) : W.addXYZ' P P = W.dblXYZ P := by
  sorry

def add₂ (P : PointClass R × PointClass R) : PointClass R :=
  Quotient.map₂ W.addXYZ' sorry P.1 P.2

-- The subset of pairs of point classes where `add₁` defines a point of the projective space
def U₁ : Set (PointClass R × PointClass R) := W.add₁ ⁻¹' {x | SpanEqTop x}

-- The subset of pairs of point classes where `add₂` defines a point of the projective space
def U₂ : Set (PointClass R × PointClass R) := W.add₂ ⁻¹' {x | SpanEqTop x}

/- The pairs on the Weierstrass curve where either `add₁` or `add₂` defines a point of
the projective space -/
def U₁₂ : Set (PointClass R × PointClass R) := (W.U₁ ∪ W.U₂) ∩ W.point ×ˢ W.point

def U₁₂ToPoint : W.U₁₂ → W.point := sorry
-- Use add₁ on W.U₁ and add₂ on W.U₂, show they agree on the intersection
-- CategoryTheory.Subfunctor.fromPreimage ?

/-- The sum of two nonsingular points is nonsingular.
Here we have to assume R is a local ring if we use the `ExistsUnit` condition.
But with the `SpanEqTop` condition it holds for all R. -/
theorem U₁₂ToPoint_mem_nonsingularPoint (P : W.U₁₂)
    (hP₁ : P.1.1 ∈ W.nonsingularPoint) (hP₂ : P.1.2 ∈ W.nonsingularPoint) :
    (W.U₁₂ToPoint P).1 ∈ W.nonsingularPoint := by
  sorry

def U₁₂subpresheaf : Subfunctor ((presheafOver 3 R).typeProd (presheafOver 3 R)) where
  obj _ := (W.baseChange _).toProjective.U₁₂
  map := sorry

def U₁₂ToSubpresheaf : W.U₁₂subpresheaf.toFunctor ⟶ W.subpresheaf.toFunctor where
  app X := U₁₂ToPoint _
  naturality := sorry

def sheafifyU₁₂ : Subfunctor ((presheafOver 3 R).typeProd (presheafOver 3 R)) :=
  W.U₁₂subpresheaf.sheafify (Scheme.zariskiTopology.over _)

def sheafifyU₁₂ToYoneda : W.sheafifyU₁₂.toFunctor ⟶ yoneda.obj W.scheme :=
  Subfunctor.sheafifyLift _ (W.U₁₂ToSubpresheaf ≫ W.subpresheafToYoneda) <|
    (isSheaf_iff_isSheaf_of_type ..).mp ((GrothendieckTopology.yoneda _).obj _).2

def prodToSheafifyU₁₂ : W.smoothSubpresheaf ×ˢ W.subpresheaf ≤ W.sheafifyU₁₂ := by
  sorry
/- Outline: for each pair (P, Q) in LHS(X), we can show (by considering quotients by maximal ideals)
that Y^{(1)}, Z^{(1)}, Y^{(2)}, Z^{(2)} evaluated at (P, Q) span the unit ideal of Γ(X),
so the corresponding basic opens form a cover of X in the Zariski topology.
(P, Q) restricted to each of these basic opens is obviously in U₁₂,
which shows that (P, Q) is in sheafifyU₁₂. -/

def vadd : W.smoothLocus ⊗ W.scheme ⟶ W.scheme :=
  Yoneda.fullyFaithful.preimage <| W.isSheafification_prodToYoneda.homEquiv
    ((GrothendieckTopology.yoneda _).obj _).2 <|
    Subfunctor.homOfLe W.prodToSheafifyU₁₂ ≫ W.sheafifyU₁₂ToYoneda

def add : W.smoothLocus ⊗ W.smoothLocus ⟶ W.smoothLocus := sorry
/- Outline: show the composition of LHS ⟶ W.smoothLocus ⊗ W.scheme and `vadd`
factors through W.smoothLocus using `U₁₂ToPoint_mem_nonsingularPoint` on the Yoneda level. -/

theorem add_comp_smoothInclusion :
    W.add ≫ W.smoothInclusion = (_ ◁ W.smoothInclusion) ≫ W.vadd := by
  sorry

theorem add_vadd : (W.add ▷ _) ≫ W.vadd = (α_ _ _ _).hom ≫ (_ ◁ W.vadd) ≫ W.vadd := by
  sorry

open MonoidalCategory in
theorem add_assoc : (W.add ▷ _) ≫ W.add = (α_ _ _ _).hom ≫ (_ ◁ W.add) ≫ W.add :=
  (cancel_mono W.smoothInclusion).mp <| by
    simp_rw [Category.assoc, add_comp_smoothInclusion, ← whisker_exchange_assoc, add_vadd,
      associator_naturality_right_assoc, ← whiskerLeft_comp_assoc, add_comp_smoothInclusion]

instance : GrpObj W.smoothLocus where
  one := show Over.mk (𝟙 _) ⟶ _ from sorry
  mul := W.add
  inv := sorry
  one_mul := sorry
  mul_one := sorry
  mul_assoc := W.add_assoc
  left_inv := sorry
  right_inv := sorry

/-- The group scheme structure on a Weierstrass curve. -/
def groupScheme : Grp (Over Spec(R)) where
  X := W.smoothLocus

end WeierstrassCurve.Projective
