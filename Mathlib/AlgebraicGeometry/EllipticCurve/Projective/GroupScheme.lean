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
public import Mathlib.Tactic.DepRewrite

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

-- probably not needed
-- A locally surjective morphism of presheaves is an "epimorphism with respect to sheaf targets".
theorem Presheaf.IsLocallySurjective.comp_injective {F G H : Cᵒᵖ ⥤ D} {f : F ⟶ G}
    (hf : IsLocallySurjective J f) (hH : Presheaf.IsSheaf J H) :
    (fun g : G ⟶ H ↦ f ≫ g).Injective := by
  sorry

namespace IsSheafification

variable {J}

open Presheaf

instance (F : Cᵒᵖ ⥤ Type*) (f₁ f₂ : Subfunctor F) (le : f₁ ≤ f₂) :
    IsLocallyInjective J (Subfunctor.homOfLe le) :=
  isLocallyInjective_of_injective _ _ fun _ _ _ eq ↦ Subtype.ext congr($eq)

theorem comp_left {F₁ F₂ G : Cᵒᵖ ⥤ D} {f : F₂ ⟶ G} (i : F₁ ⟶ F₂) [IsLocallyInjective J i]
    [IsLocallySurjective J i] (hf : IsSheafification J f) : IsSheafification J (i ≫ f) :=
  have := hf.2.1; have := hf.2.2; ⟨hf.1, inferInstance, inferInstance⟩

theorem congr_left {F₁ F₂ G : Cᵒᵖ ⥤ D} {f : F₂ ⟶ G} (i : F₁ ⟶ F₂) [IsIso i]
    (hf : IsSheafification J f) : IsSheafification J (i ≫ f) :=
  sorry

theorem congr_right {F G₁ G₂ : Cᵒᵖ ⥤ D} {f : F ⟶ G₁} (i : G₁ ⟶ G₂) [IsIso i]
    (hf : IsSheafification J f) : IsSheafification J (f ≫ i) :=
  sorry

def homEquiv {F G H : Cᵒᵖ ⥤ D} {f : F ⟶ G} (hf : IsSheafification J f)
    (hH : Presheaf.IsSheaf J H) : (F ⟶ H) ≃ (G ⟶ H) where
  toFun := sorry
  invFun g := f ≫ g
  left_inv := sorry
  right_inv := sorry

end IsSheafification

instance (X : C) [J.Subcanonical] : (J.over X).Subcanonical := sorry
  -- CategoryTheory.Sheaf.over ?

-- not needed
instance (X : C) [HasWeakSheafify J D] : HasWeakSheafify (J.over X) D := sorry

end ConcreteCategory

variable (F G : C ⥤ Type u)

open scoped MonoidalCategory
/- Using Cartesian monoidal category structure on `C ⥤ Type*` from
`Functor.cartesianMonoidalCategory` and `typesCartesianMonoidalCategory`. -/

instance : SProd (Subfunctor F) (Subfunctor G) (Subfunctor (F ⊗ G)) where
  sprod f g :=
  { obj X := f.obj X ×ˢ g.obj X
    map _ _ h := ⟨f.map _ h.1, g.map _ h.2⟩ }

variable {F G}

lemma Subfunctor.prod_mono {f₁ f₂ : Subfunctor F} {g₁ g₂ : Subfunctor G}
    (hf : f₁ ≤ f₂) (hg : g₁ ≤ g₂) : f₁ ×ˢ g₁ ≤ f₂ ×ˢ g₂ :=
  fun _ _ h ↦ ⟨hf _ h.1, hg _ h.2⟩

def Subfunctor.toFunctorProdIso (f : Subfunctor F) (g : Subfunctor G) :
    (f ×ˢ g).toFunctor ≅ f.toFunctor ⊗ g.toFunctor where
  hom := { app X x := (⟨x.1.1, x.2.1⟩, ⟨x.1.2, x.2.2⟩) }
  inv := { app X x := ⟨(x.1.1, x.2.1), x.1.2, x.2.2⟩ }

variable {J}

theorem Presheaf.IsSheaf.typeProd {F G : Cᵒᵖ ⥤ Type u} (hF : IsSheaf J F) (hG : IsSheaf J G) :
    IsSheaf J (F ⊗ G) := by
  sorry

theorem IsSheafification.typeProd {F F' G G' : Cᵒᵖ ⥤ Type u} {f : F ⟶ F'} {g : G ⟶ G'}
    (hf : IsSheafification J f) (hg : IsSheafification J g) :
    IsSheafification J (f ⊗ₘ g) := by
  sorry

instance [CartesianMonoidalCategory C] : (yoneda (C := C)).Monoidal := .ofChosenFiniteProducts _

end CategoryTheory

open scoped SpecOfNotation

namespace AlgebraicGeometry

variable {R : Type*} [CommRing R]

instance (X : (Over Spec(R))ᵒᵖ) : Algebra R (Scheme.Γ.obj <| (Over.forget _).op.obj X) :=
  ((ΓSpec.adjunction.homEquiv ..).symm X.unop.hom).unop.hom.toAlgebra

theorem Scheme.Γ_overForget_comp_algebraMap {X Y : (Over Spec(R))ᵒᵖ} (f : X ⟶ Y) :
    (Scheme.Γ.map <| (Over.forget _).op.map f).hom.comp (algebraMap R _) = algebraMap R _ := by
  sorry

end AlgebraicGeometry

namespace AlgebraicGeometry.Proj

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A] (𝒜 : ℕ → Submodule R A)
variable [GradedAlgebra 𝒜]

def structureMorphism : Proj 𝒜 ⟶ Spec (.of R) :=
  Proj.toSpecZero 𝒜 ≫ Spec.map (CommRingCat.ofHom (algebraMap ..))
  -- ΓSpec.adjunction.homEquiv _ _ (.op sorry) ?

end AlgebraicGeometry.Proj

namespace AlgebraicGeometry.ProjectiveSpace

variable (n m : Type*)

-- This is currently `WeierstrassCurve.Projective.PointClass`
abbrev PointClass (R : Type*) [Monoid R] :=
  MulAction.orbitRel.Quotient Rˣ (n → R)

variable {n m}

namespace PointClass

section Monoid

variable {R S : Type*} [Monoid R] [Monoid S] (f : R →* S)

abbrev map : PointClass n R → PointClass n S :=
  Quotient.map (f ∘ ·) fun _ _ ⟨u, h⟩ ↦
    ⟨u.map f, funext fun _ ↦ (map_mul f ..).symm.trans congr(f ($h _))⟩

abbrev map₂ : PointClass n R × PointClass m R → PointClass n S × PointClass m S :=
  Prod.map (map f) (map f)

-- map₃ ...

def ExistsUnit : PointClass n R → Prop :=
  Quotient.lift (fun x ↦ ∃ i, IsUnit (x i)) sorry

@[simp] lemma existsUnit_mk_iff {P : n → R} : ExistsUnit ⟦P⟧ ↔ ∃ i, IsUnit (P i) := .rfl

lemma ExistsUnit.map {P : PointClass n R} (hP : ExistsUnit P) : ExistsUnit (P.map f) := by
  rcases P; have ⟨i, hi⟩ := hP; exact ⟨i, hi.map f⟩

end Monoid

section Semiring

variable {R S : Type*} [Semiring R] [Semiring S] (f : R →+* S)

def SpanEqTop : PointClass n R → Prop :=
  Quotient.lift (fun x ↦ Ideal.span (Set.range x) = ⊤) sorry

@[simp]
lemma spanEqTop_mk_iff {P : n → R} : SpanEqTop ⟦P⟧ ↔ Ideal.span (Set.range P) = ⊤ := .rfl

lemma SpanEqTop.map {P : PointClass n R} (hP : SpanEqTop P) :
    SpanEqTop (P.map f.toMonoidHom) := by
  obtain ⟨P, rfl⟩ := Quotient.mk_surjective P
  rw [spanEqTop_mk_iff] at hP
  apply_fun Ideal.map f at hP
  rwa [Ideal.map_top, Ideal.map_span, ← Set.range_comp] at hP

lemma ExistsUnit.spanEqTop {P : PointClass n R} (hP : ExistsUnit P) : SpanEqTop P := by
  rcases P
  have ⟨i, hi⟩ := hP
  exact Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨i, rfl⟩) hi

end Semiring

theorem orbitRel_iff_of_span_eq_one {R} [CommSemiring R] {P Q : n → R}
    (hP : Ideal.span (Set.range P) = ⊤) (hQ : Ideal.span (Set.range Q) = ⊤) :
    MulAction.orbitRel Rˣ _ P Q ↔ ∀ i j, P i * Q j = P j * Q i where
  mp := by rintro ⟨u, rfl⟩; simp [Units.smul_def, mul_right_comm]
  mpr h := by
    have ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp ((Ideal.eq_top_iff_one _).mp hQ)
    let u := c.sum fun i a ↦ a • P i
    have h i : u * Q i = P i := by
      rw [← one_mul (P i), ← hc, c.sum_mul]
      dsimp; rw [c.sum_mul]
      simp_rw [mul_assoc, h, mul_comm]
    refine ⟨(Ideal.span_singleton_eq_top (x := u).mp <|
      top_unique <| .trans hP.ge <| Ideal.span_le.mpr ?_).unit, funext h⟩
    rintro _ ⟨i, rfl⟩
    rw [← h, mul_comm]
    exact Submodule.smul_mem _ _ (Ideal.subset_span rfl)

end PointClass

variable (n)

def functor : CommRingCat ⥤ Type _ where
  obj R := PointClass n R
  map f P := P.map f.hom
  map_id _ := funext <| by rintro ⟨⟩; rfl
  map_comp _ _ := funext <| by rintro ⟨⟩; rfl

def subfunctor : Subfunctor (functor n) where
  obj _ := {P | P.ExistsUnit}
  map _ _ := (·.map _)

def presheaf : Schemeᵒᵖ ⥤ Type _ := Scheme.Γ ⋙ functor n

def subpresheaf : Subfunctor (presheaf n) where
  obj _ := {P | P.ExistsUnit}
  map _ _ := (·.map _)

attribute [local instance] MvPolynomial.gradedAlgebra

section

variable (R₀ : Type*) [CommRing R₀]

abbrev scheme : Scheme := Proj (MvPolynomial.homogeneousSubmodule n R₀)

def presheafOver : (Over Spec(R₀))ᵒᵖ ⥤ Type _ := (Over.forget _).op ⋙ presheaf n

def subpresheafOver : Subfunctor (presheafOver n R₀) where
  obj _ := {P | P.ExistsUnit}
  map _ _ := (·.map _)

end

variable (n : ℕ) (R₀ : Type*) [CommRing R₀]

def schemeOver : Over Spec(R₀) := .mk (Y := scheme (Fin n) R₀) (Proj.structureMorphism _)

-- not needed
def subpresheafToYoneda : (subpresheaf (Fin n)).toFunctor ⟶ yoneda.obj (scheme (Fin n) ℤ) :=
  sorry

-- not needed
theorem isSheafification_subpresheafToYoneda :
    IsSheafification Scheme.zariskiTopology (subpresheafToYoneda n) := by
  refine ⟨((GrothendieckTopology.yoneda _).obj _).2, ?_, ?_⟩
  · sorry
  · sorry

def subpresheafOverToYoneda :
    (subpresheafOver (Fin n) R₀).toFunctor ⟶ yoneda.obj (schemeOver n R₀) :=
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

/- Can replace the `Nonsingular` definition, which currently uses `≠ 0` conditions which are
good only in a field. Note that `SpanDerivEqTop` implies `SpanEqTop`, since the derivatives are
homogeneous of degree 2 in the coordinates x,y,z, so certainly in the ideal generated by x,y,z.
If this is defined to say one of the derivative is a unit, it doesn't imply one of x,y,z is a unit.
-/
def SpanDerivEqTop (P : Fin 3 → R) : Prop :=
  Ideal.span {W.polynomialX.eval P, W.polynomialY.eval P, W.polynomialZ.eval P} = ⊤

open AlgebraicGeometry ProjectiveSpace PointClass

-- TODO: replace `PointClass R` by `ProjectiveSpace.PointClass 3 R` everywhere
def EquationLift : PointClass R → Prop :=
  Quotient.lift W.Equation sorry
/- Note: if (x,y,z) satisfies Equation, then x³ ∈ span {y,z},
so span {x,y,z} = ⊤ ↔ span {y,z} = ⊤. -/

def SpanDerivEqTopLift : PointClass R → Prop :=
  Quotient.lift W.SpanDerivEqTop sorry

def point : Set (PointClass R) := {P | ExistsUnit P ∧ W.EquationLift P}

def nonsingularPoint : Set (PointClass R) := W.point ∩ {P | W.SpanDerivEqTopLift P}

open ProjectiveSpace

-- The presheaf of `PointClass`es.
notation "PC" => presheafOver (Fin 3)

/-- The presheaf $W_{pre}$. -/
def subpresheaf : Subfunctor (PC R) where
  obj X := point (W.baseChange _)
  map := sorry

/-- The presheaf $W⁰_{pre}$. -/
def smoothSubpresheaf : Subfunctor (PC R) where
  obj X := nonsingularPoint (W.baseChange _)
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

notation "yo" => yoneda.obj

def subpresheafToYoneda : W.subpresheaf.toFunctor ⟶ yo W.scheme := sorry

def smoothSubpresheafToYoneda : W.smoothSubpresheaf.toFunctor ⟶ yo W.smoothLocus := sorry

abbrev smoothInclusion : W.smoothLocus ⟶ W.scheme := Over.homMk _

theorem subpresheafToYoneda_comm :
    Subfunctor.homOfLe W.smoothSubpresheaf_le ≫ W.subpresheafToYoneda =
    W.smoothSubpresheafToYoneda ≫ yoneda.map W.smoothInclusion := by
  sorry

open scoped MonoidalCategory

theorem isSheafification_subpresheafToYoneda :
    IsSheafification (Scheme.zariskiTopology.over _) (subpresheafToYoneda W) := by
  sorry

theorem isSheafification_smoothSubpresheafToYoneda :
    IsSheafification (Scheme.zariskiTopology.over _) (smoothSubpresheafToYoneda W) := by
  sorry

variable {S : Type*} [CommRing S] (f : R →+* S)

-- Maybe rename addXYZ to addXYZ₁
def addXYZ₁ := @addXYZ

def add₁ (P : PointClass R × PointClass R) : PointClass R :=
  Quotient.map₂ W.addXYZ₁ sorry P.1 P.2

-- use corrected version of X^{(2)}, Y^{(2)} and Z^{(2)} in Bosma–Lenstra
def addXYZ₂ (P Q : Fin 3 → R) : Fin 3 → R := have := W; sorry

-- probably needs `W.Equation P`
theorem addXYZ₂_self (P : Fin 3 → R) : W.addXYZ₂ P P = W.dblXYZ P := by
  sorry

theorem addXYZ₁_mul_addXYZ₂ (P Q : Fin 3 → R) (hP : W.Equation P) (hQ : W.Equation Q) (i j) :
    W.addXYZ P Q i * W.addXYZ₂ P Q j = W.addXYZ₁ P Q j * W.addXYZ₂ P Q i := by
  sorry
/- trivial on the diagonal; verify for (i,j) = (0,2) or (1,2), then (0,2) can be deduced from
the universal case since W.addXYZ 2 and W.addXYZ' 2 are nonzero in CoordinateRing. -/

-- Is this true? Or only up to a scalar multiple?
theorem addXYZ₁_addXYZ₁ (P Q R : Fin 3 → R) :
    W.addXYZ (W.addXYZ P Q) R = W.addXYZ P (W.addXYZ Q R) := by
  sorry

def add₂ (P : PointClass R × PointClass R) : PointClass R :=
  Quotient.map₂ W.addXYZ₂ sorry P.1 P.2

theorem map_add₁ (P) :
    PointClass.map f (W.add₁ P) = add₁ (W.map f) (PointClass.map₂ f P) := by
  sorry

theorem map_add₂ (P) :
    PointClass.map f (W.add₂ P) = add₂ (W.map f) (PointClass.map₂ f P) := by
  sorry

-- The subset of pairs of point classes where `add₁` defines a point of the projective space
def U₁ : Set (PointClass R × PointClass R) := W.add₁ ⁻¹' {P | ExistsUnit P}

-- The subset of pairs of point classes where `add₂` defines a point of the projective space
def U₂ : Set (PointClass R × PointClass R) := W.add₂ ⁻¹' {P | ExistsUnit P}

theorem add₁_eq_add₂ {P} (h₁ : P ∈ W.U₁) (h₂ : P ∈ W.U₂) (h : P ∈ W.point ×ˢ W.point) :
    W.add₁ P = W.add₂ P := by
  obtain ⟨⟨P⟩, ⟨Q⟩⟩ := P
  dsimp only [← Quotient.mk.eq_1] at *
  dsimp [add₁, add₂]
  dsimp [U₁, U₂] at h₁ h₂
  rw [Quotient.eq, orbitRel_iff_of_span_eq_one h₁.spanEqTop h₂.spanEqTop]
  exact W.addXYZ₁_mul_addXYZ₂ P Q h.1.2 h.2.2

theorem add₁_mem_point {P} (h₁ : P ∈ W.U₁) (h : P ∈ W.point ×ˢ W.point) : W.add₁ P ∈ W.point :=
  ⟨h₁, sorry⟩

theorem add₂_mem_point {P} (h₂ : P ∈ W.U₂) (h : P ∈ W.point ×ˢ W.point) : W.add₂ P ∈ W.point :=
  ⟨h₂, sorry⟩

def add₁₂ (P : PointClass R × PointClass R) : PointClass R := by
  classical exact if P ∈ W.U₁ then W.add₁ P else W.add₂ P

/- The pairs on the Weierstrass curve where either `add₁` or `add₂` defines a point of
the projective space -/
def U₁₂ : Set (PointClass R × PointClass R) := (W.U₁ ∪ W.U₂) ∩ W.nonsingularPoint ×ˢ W.point

theorem add₁₂_mem_point {P} (hP : P ∈ W.U₁₂) : W.add₁₂ P ∈ W.point := by
  have := And.intro hP.2.1.1 hP.2.2
  rw [add₁₂]; split_ifs with h
  exacts [W.add₁_mem_point h this, W.add₂_mem_point (hP.1.resolve_left h) this]

theorem add₁₂_eq_add₁ {P} (h : P ∈ W.U₁) : W.add₁₂ P = W.add₁ P := if_pos h

theorem add₁₂_eq_add₂ {P} (h : P ∈ W.U₂) (h' : P ∈ W.point ×ˢ W.point) : W.add₁₂ P = W.add₂ P := by
  by_cases h₁ : P ∈ W.U₁
  · rw [W.add₁₂_eq_add₁ h₁, W.add₁_eq_add₂ h₁ h h']
  · rw [add₁₂, if_neg h₁]

theorem map_mem_point {P} (hP : P ∈ W.point) :
    PointClass.map f P ∈ (W.map f).toProjective.point := by
  sorry

theorem map_mem_nonsingularPoint {P} (hP : P ∈ W.nonsingularPoint) :
    PointClass.map f P ∈ (W.map f).toProjective.nonsingularPoint := by
  sorry

theorem map_mem_U₁ {P} (hP : P ∈ W.U₁) : PointClass.map₂ f P ∈ (W.map f).toProjective.U₁ := by
  sorry

theorem map_mem_U₂ {P} (hP : P ∈ W.U₂) : PointClass.map₂ f P ∈ (W.map f).toProjective.U₂ := by
  sorry

theorem map_mem_U₁₂ {P} (hP : P ∈ W.U₁₂) : PointClass.map₂ f P ∈ (W.map f).toProjective.U₁₂ :=
  ⟨hP.1.imp (W.map_mem_U₁ f) (W.map_mem_U₂ f),
    W.map_mem_nonsingularPoint f hP.2.1, W.map_mem_point f hP.2.2⟩

theorem map_add₁₂ {P} (h : P ∈ W.U₁₂) :
    PointClass.map f (W.add₁₂ P) = (W.map f).toProjective.add₁₂ (PointClass.map₂ f P) := by
  obtain h₁ | h₂ := h.1
  · rw [W.add₁₂_eq_add₁ h₁, add₁₂_eq_add₁ _ (W.map_mem_U₁ f h₁), map_add₁]
  · rw [W.add₁₂_eq_add₂ h₂ ⟨h.2.1.1, h.2.2⟩, add₁₂_eq_add₂ _ (W.map_mem_U₂ f h₂), map_add₂]
    exact ⟨W.map_mem_point f h.2.1.1, W.map_mem_point f h.2.2⟩

theorem add₁₂_mem_nonsingularPoint {P} (h : P ∈ W.U₁ ∪ W.U₂)
    (h' : P ∈ W.nonsingularPoint ×ˢ W.nonsingularPoint) :
    W.add₁₂ P ∈ W.nonsingularPoint := by
  sorry

def prodSubpresheaf : Subfunctor (PC R ⊗ PC R) where
  obj _ := (W.baseChange _).toProjective.U₁₂
  map f x hx := by
    rw [baseChange, ← Scheme.Γ_overForget_comp_algebraMap f, ← map_map, Set.mem_preimage]
    exact map_mem_U₁₂ _ _ hx

def prodToSubpresheaf : W.prodSubpresheaf.toFunctor ⟶ W.subpresheaf.toFunctor where
  app X P := ⟨_, add₁₂_mem_point _ P.2⟩
  naturality X Y f := by
    ext P; apply Subtype.ext
    dsimp only [types_comp_apply, Subfunctor.toFunctor_map_coe]
    rw [baseChange, ← Scheme.Γ_overForget_comp_algebraMap f, ← map_map]
    exact (map_add₁₂ _ _ P.2).symm

theorem prodSubpresheaf_le : W.prodSubpresheaf ≤ W.smoothSubpresheaf ×ˢ W.subpresheaf :=
  fun _ _ ↦ (·.2)

def prodToYoneda : W.prodSubpresheaf.toFunctor ⟶ yo W.smoothLocus ⊗ yo W.scheme :=
  Subfunctor.homOfLe W.prodSubpresheaf_le ≫ (Subfunctor.toFunctorProdIso ..).hom ≫
  (W.smoothSubpresheafToYoneda ⊗ₘ W.subpresheafToYoneda)

def prodSmoothSubpresheaf : Subfunctor (PC R ⊗ PC R) :=
  W.prodSubpresheaf ⊓ (W.smoothSubpresheaf ×ˢ W.smoothSubpresheaf)

def prodSmoothToYoneda : W.prodSmoothSubpresheaf.toFunctor ⟶ yo W.smoothLocus ⊗ yo W.smoothLocus :=
  Subfunctor.homOfLe inf_le_right ≫ (Subfunctor.toFunctorProdIso ..).hom ≫
  (W.smoothSubpresheafToYoneda ⊗ₘ W.smoothSubpresheafToYoneda)

def prodToSmoothSubpresheaf :
    W.prodSmoothSubpresheaf.toFunctor ⟶ W.smoothSubpresheaf.toFunctor where
  app X P := ⟨_, add₁₂_mem_nonsingularPoint _ P.2.1.1 P.2.2⟩
  naturality X Y f := by
    ext P; apply Subtype.ext
    exact congr($(W.prodToSubpresheaf.naturality f) ⟨P, P.2.1⟩)

instance : Presheaf.IsLocallySurjective (Scheme.zariskiTopology.over _)
    (Subfunctor.homOfLe W.prodSubpresheaf_le) := by
  sorry
/- Outline: for each pair (P, Q) in W⁰ × W, we can show (by considering quotients by maximal ideals)
that Y^{(1)}, Z^{(1)}, Y^{(2)}, Z^{(2)} evaluated at (P, Q) span the unit ideal of Γ(X),
so the corresponding basic opens form a cover of X in the Zariski topology,
and (P, Q) restricted to each of these basic opens is obviously in U₁₂. -/

instance : Presheaf.IsLocallySurjective (Scheme.zariskiTopology.over _)
    (Subfunctor.homOfLe (inf_le_right : W.prodSmoothSubpresheaf ≤ _)) := by
  sorry

theorem isSheafification_prodToYoneda :
    IsSheafification (Scheme.zariskiTopology.over _) W.prodToYoneda :=
  ((W.isSheafification_smoothSubpresheafToYoneda.typeProd
    W.isSheafification_subpresheafToYoneda).congr_left _).comp_left _

theorem isSheafification_prodSmoothToYoneda :
    IsSheafification (Scheme.zariskiTopology.over _) W.prodSmoothToYoneda :=
  ((W.isSheafification_smoothSubpresheafToYoneda.typeProd
    W.isSheafification_smoothSubpresheafToYoneda).congr_left _).comp_left _

def yonedaVAdd : yo W.smoothLocus ⊗ yo W.scheme ⟶ yo W.scheme :=
  W.isSheafification_prodToYoneda.homEquiv ((GrothendieckTopology.yoneda _).obj _).2 <|
    W.prodToSubpresheaf ≫ W.subpresheafToYoneda

def vadd : W.smoothLocus ⊗ W.scheme ⟶ W.scheme :=
  Yoneda.fullyFaithful.preimage <| (Functor.Monoidal.μIso ..).inv ≫ W.yonedaVAdd

def yonedaAdd : yo W.smoothLocus ⊗ yo W.smoothLocus ⟶ yo W.smoothLocus :=
  W.isSheafification_prodSmoothToYoneda.homEquiv ((GrothendieckTopology.yoneda _).obj _).2 <|
    W.prodToSmoothSubpresheaf ≫ W.smoothSubpresheafToYoneda

/- Outline: show the composition of LHS ⟶ W.smoothLocus ⊗ W.scheme and `vadd`
factors through W.smoothLocus using `U₁₂ToPoint_mem_nonsingularPoint` on the Yoneda level. -/

def add : W.smoothLocus ⊗ W.smoothLocus ⟶ W.smoothLocus :=
  Yoneda.fullyFaithful.preimage <| (Functor.Monoidal.μIso ..).inv ≫ W.yonedaAdd

theorem add_comp_smoothInclusion :
    W.add ≫ W.smoothInclusion = (_ ◁ W.smoothInclusion) ≫ W.vadd := by
  sorry

/-- The locus in W⁰ × W⁰ × W such that addition in both order, including intermediate results,
lands in U₁₂. -/
def prodProdSubsheaf : Subfunctor ((PC R ⊗ PC R) ⊗ PC R) :=
  (W.smoothSubpresheaf ×ˢ W.smoothSubpresheaf) ×ˢ W.subpresheaf ⊓
  ((W.prodSubpresheaf ×ˢ (⊤ : Subfunctor (PC R))) ⊓
    (W.prodSubpresheaf.preimage ((W.prodToSmoothSubpresheaf ≫ W.smoothSubpresheaf.ι) ▷ _)).image
      (W.prodSmoothSubpresheaf.ι ▷ _)) ⊓
  (((⊤ : Subfunctor (PC R)) ×ˢ W.prodSubpresheaf).preimage (α_ _ _ _).hom ⊓
    (W.prodSubpresheaf.preimage (_ ◁ (W.prodToSubpresheaf ≫ W.subpresheaf.ι))).image
      ((_ ◁ W.prodSubpresheaf.ι) ≫ (α_ _ _ _).inv))

theorem mem_obj_prodProdSubsheaf_iff {X} {P : ((PC R ⊗ PC R) ⊗ PC R).obj X} :
    P ∈ W.prodProdSubsheaf.obj X ↔ P.1.1 ∈ nonsingularPoint (W.baseChange _) ∧
      P.1.2 ∈ nonsingularPoint (W.baseChange _) ∧ P.2 ∈ point (W.baseChange _) ∧
      P.1 ∈ U₁₂ (W.baseChange _) ∧ (P.1.2, P.2) ∈ U₁₂ (W.baseChange _) ∧
      (add₁₂ (W.baseChange _) P.1, P.2) ∈ U₁₂ (W.baseChange _) ∧
      (P.1.1, add₁₂ (W.baseChange _) (P.1.2, P.2)) ∈ U₁₂ (W.baseChange _) where
  mp := by
    refine fun ⟨⟨h₀, h₁⟩, h₂⟩ ↦ ⟨h₀.1.1, h₀.1.2, h₀.2, h₁.1.1, h₂.1.2, ?_, ?_⟩
    · obtain ⟨P, hP, rfl⟩ := h₁.2; exact hP
    · obtain ⟨P, hP, rfl⟩ := h₂.2; exact hP
  mpr := fun ⟨h1, h2, h3, h12, h23, h₁, h₂⟩ ↦ ⟨⟨⟨⟨h1, h2⟩, h3⟩, ⟨h12, ⟨⟩⟩, (⟨P.1, h12, _⟩, P.2), _⟩, _, _⟩



def prodProdToYoneda :
    W.prodProdSubsheaf.toFunctor ⟶ (yo W.smoothLocus ⊗ yo W.smoothLocus) ⊗ yo W.scheme :=
  Subfunctor.homOfLe inf_le_left ≫
  (Subfunctor.toFunctorProdIso ..).hom ≫ (Subfunctor.toFunctorProdIso ..).hom ▷ _ ≫
  ((W.smoothSubpresheafToYoneda ⊗ₘ W.smoothSubpresheafToYoneda) ⊗ₘ W.subpresheafToYoneda)

theorem isSheafification_prodProdToYoneda :
    IsSheafification (Scheme.zariskiTopology.over _) W.prodProdToYoneda := by
  sorry

theorem yoneda_add_vadd :


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
