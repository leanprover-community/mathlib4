/-
Copyright (c) 2026 Raphael Douglas Giles. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Douglas Giles
-/
import Mathlib.AlgebraicGeometry.AlgebraicCycle.StructureSheafVanishing

/-!
# The sheaf of principal parts and the flasque resolution of `𝒪ₓ(D)`

For a Noetherian integral scheme `X` which is regular in codimension one and a Weil divisor
`D`, we construct the sheaf of **principal parts** `Q(D)`: its sections over `U` are the
finitely supported families `(f_q)` indexed by the codimension-one points `q ∈ U`, with
`f_q ∈ k(X) ⧸ 𝔪_q^{-D q}` (the quotient of the function field by the fractional ideal
`ordSubmodule hq (-D q)` of rational functions of order at least `-D q` at `q`).

This realizes the canonical two-step flasque resolution

`0 ⟶ 𝒪ₓ(D) ⟶ 𝒦 ⟶ Q(D) ⟶ 0`

where `𝒦 = functionFieldSheaf X` is the (flasque) skyscraper of rational functions at the
generic point and `𝒪ₓ(D)` is the divisorial sheaf of `SheafViaSubmodule`. The morphism
`𝒦 ⟶ Q(D)` sends a rational function to its family of classes; its kernel is `𝒪ₓ(D)` by the
very definition of the divisor bound, and it is an epimorphism because a class at `q` is
represented by an actual rational function on a small enough neighbourhood of `q`.

Since `𝒦` and `Q(D)` are flasque, the long exact sequence shows `Hⁿ(X, 𝒪ₓ(D)) = 0` for
`n ≥ 2`; at `D = 0` this discharges the vanishing hypothesis `hb₀` of
`riemann_roch_of_structureSheaf` (with `N = 1`), leaving only the finiteness of `H⁰(X, 𝒪ₓ)`
and `H¹(X, 𝒪ₓ)`.

## Design

The sections of the ambient sheaf of *all* families (no support condition) form a plain
dependent product `Π q, k(X) ⧸ 𝔪_q^{-D q}`, so all elementwise reasoning is `funext` and
definitional — no categorical product API is needed. `Q(D)` is then carved out as a
`PresheafOfModules.Submodule` by the finite-support predicate, exactly parallel to the way
`𝒪ₓ(D)` is carved out of `𝒦` in `SheafViaSubmodule`. Noetherianity enters only through
quasi-compactness of opens, which makes local finiteness of supports equal to finiteness
(for the sheaf property of `Q(D)`, and for the finiteness of the family of principal parts
of a single rational function).
-/

universe u

open AlgebraicGeometry Scheme CategoryTheory CategoryTheory.Limits
  CategoryTheory.GrothendieckTopology Order Opposite TopologicalSpace

set_option backward.isDefEq.respectTransparency false

/-- A morphism into `M` whose values lie pointwise in a submodule `N` factors through `N.ι`;
see `PresheafOfModules.Submodule.lift_comp_ι`.
TODO: upstream next to `PresheafOfModules.Submodule.liftOfLE`. -/
noncomputable def PresheafOfModules.Submodule.lift {C : Type*} [Category C]
    {R : Cᵒᵖ ⥤ RingCat.{u}} {M : PresheafOfModules.{u} R} (N : M.Submodule)
    {A : PresheafOfModules.{u} R} (k : A ⟶ M)
    (hk : ∀ (U : Cᵒᵖ) (a : ↑(A.obj U)), k.app U a ∈ N.obj U) :
    A ⟶ N.toPresheafOfModules :=
  PresheafOfModules.homMk
    { app := fun U => AddCommGrpCat.ofHom
        (AddMonoidHom.mk' (fun a => (⟨k.app U a, hk U a⟩ : ↑(N.obj U)))
          (fun a b => Subtype.ext (map_add (k.app U).hom a b)))
      naturality := fun {U V} r => by
        ext a
        apply Subtype.ext
        change (k.app V) ((A.map r) a) = (M.map r) ((k.app U) a)
        exact PresheafOfModules.naturality_apply k r a }
    (fun U r m => Subtype.ext (map_smul (k.app U).hom r m))

lemma PresheafOfModules.Submodule.lift_comp_ι {C : Type*} [Category C]
    {R : Cᵒᵖ ⥤ RingCat.{u}} {M : PresheafOfModules.{u} R} (N : M.Submodule)
    {A : PresheafOfModules.{u} R} (k : A ⟶ M)
    (hk : ∀ (U : Cᵒᵖ) (a : ↑(A.obj U)), k.app U a ∈ N.obj U) :
    N.lift k hk ≫ N.ι = k := by
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  ext a
  rfl

namespace AlgebraicGeometry.AlgebraicCycle
namespace SheafViaSubmodule

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsRegularInCodimensionOne X]
variable (D : AlgebraicCycle X ℤ)

namespace PrincipalParts

/-! ### The spaces of principal parts at codimension-one points -/

/-- The space of principal parts at a codimension-one point `q`, twisted by `D`: the quotient
of the function field by the fractional ideal `𝔪_q^{-D q}` of rational functions of order at
least `-D q` at `q`. -/
def Component {q : X} (hq : coheight q = 1) : Type u :=
  ↑X.functionField ⧸ ordSubmodule hq (-D q)

noncomputable instance {q : X} (hq : coheight q = 1) : AddCommGroup (Component D hq) :=
  inferInstanceAs (AddCommGroup (↑X.functionField ⧸ ordSubmodule hq (-D q)))

noncomputable instance {q : X} (hq : coheight q = 1) :
    Module ↑(X.presheaf.stalk q) (Component D hq) :=
  inferInstanceAs (Module ↑(X.presheaf.stalk q) (↑X.functionField ⧸ ordSubmodule hq (-D q)))

/-- The class of a rational function in the space of principal parts at `q`. -/
noncomputable def Component.mk {q : X} (hq : coheight q = 1) (f : ↑X.functionField) :
    Component D hq :=
  Submodule.Quotient.mk f

lemma Component.mk_surjective {q : X} (hq : coheight q = 1) :
    Function.Surjective (Component.mk D hq) :=
  Submodule.Quotient.mk_surjective _

lemma Component.mk_eq_zero_iff {q : X} (hq : coheight q = 1) {f : ↑X.functionField} :
    Component.mk D hq f = 0 ↔ f ∈ ordSubmodule hq (-D q) :=
  Submodule.Quotient.mk_eq_zero _

lemma Component.mk_add {q : X} (hq : coheight q = 1) (f g : ↑X.functionField) :
    Component.mk D hq (f + g) = Component.mk D hq f + Component.mk D hq g :=
  rfl

lemma Component.mk_smul {q : X} (hq : coheight q = 1) (c : ↑(X.presheaf.stalk q))
    (f : ↑X.functionField) :
    Component.mk D hq (c • f) = c • Component.mk D hq f :=
  Submodule.Quotient.mk_smul _ c f

/-! ### The ambient presheaf of all families of principal parts -/

/-- The codimension-one points of an open `U`, indexing the components of the sheaf of
principal parts. -/
def Index (U : X.Opens) : Type u := {q : X // coheight q = 1 ∧ q ∈ U}

/-- The ambient abelian presheaf of (unconstrained) families of principal parts; restriction
is (definitionally) restriction of families. -/
noncomputable def ambientAb : (Opens ↥X)ᵒᵖ ⥤ Ab where
  obj U := AddCommGrpCat.of (∀ i : Index (unop U), Component D i.2.1)
  map {U V} r := AddCommGrpCat.ofHom
    { toFun f := fun i => f ⟨i.1, i.2.1, leOfHom r.unop i.2.2⟩
      map_zero' := rfl
      map_add' _ _ := rfl }

@[simp]
lemma ambientAb_map_apply {U V : (Opens ↥X)ᵒᵖ} (r : U ⟶ V) (f : ↑((ambientAb D).obj U))
    (i : Index (unop V)) :
    ((ambientAb D).map r) f i = f ⟨i.1, i.2.1, leOfHom r.unop i.2.2⟩ :=
  rfl

/-- The module structure on families of principal parts over the sections of the structure
sheaf: a section acts on the component at `q` through its germ at `q`. -/
noncomputable instance sectionsModule (U : (Opens ↥X)ᵒᵖ) :
    Module ↑(X.ringCatSheaf.obj.obj U) ↑((ambientAb D).obj U) where
  smul a f := fun i => X.presheaf.germ (unop U) i.1 i.2.2 a • f i
  one_smul f := funext fun i =>
    (congrArg (· • f i) (map_one (X.presheaf.germ (unop U) i.1 i.2.2).hom)).trans
      (one_smul _ (f i))
  mul_smul a b f := funext fun i =>
    (congrArg (· • f i) (map_mul (X.presheaf.germ (unop U) i.1 i.2.2).hom a b)).trans
      (mul_smul _ _ (f i))
  smul_zero a := funext fun i =>
    smul_zero (A := Component D i.2.1) (X.presheaf.germ (unop U) i.1 i.2.2 a)
  smul_add a f g := funext fun i =>
    smul_add (X.presheaf.germ (unop U) i.1 i.2.2 a) (f i) (g i)
  add_smul a b f := funext fun i =>
    (congrArg (· • f i) (map_add (X.presheaf.germ (unop U) i.1 i.2.2).hom a b)).trans
      (add_smul _ _ (f i))
  zero_smul f := funext fun i =>
    (congrArg (· • f i) (map_zero (X.presheaf.germ (unop U) i.1 i.2.2).hom)).trans
      (zero_smul _ (f i))

lemma smul_apply {U : (Opens ↥X)ᵒᵖ} (a : ↑(X.ringCatSheaf.obj.obj U))
    (f : ↑((ambientAb D).obj U)) (i : Index (unop U)) :
    (a • f) i = X.presheaf.germ (unop U) i.1 i.2.2 a • f i :=
  rfl

/-- The scalar action on families of principal parts is semilinear with respect to
restriction, since germs are unchanged by restriction. -/
lemma ambientAb_map_smul ⦃U V : (Opens ↥X)ᵒᵖ⦄ (r : U ⟶ V) (a : ↑(X.ringCatSheaf.obj.obj U))
    (f : ↑((ambientAb D).obj U)) :
    (ambientAb D).map r (a • f) = X.ringCatSheaf.obj.map r a • (ambientAb D).map r f :=
  funext fun i =>
    (congrArg (· • f ⟨i.1, i.2.1, leOfHom r.unop i.2.2⟩)
      (X.presheaf.germ_res_apply' r i.1 i.2.2 a)).symm

/-- The ambient presheaf of modules of (unconstrained) families of principal parts. -/
noncomputable def ambient : PresheafOfModules.{u} X.ringCatSheaf.obj :=
  PresheafOfModules.ofPresheaf (ambientAb D) (ambientAb_map_smul D)

/-! ### Supports of families -/

/-- The support of a family of principal parts, as a set of points of `X`. -/
def suppSet {U : (Opens ↥X)ᵒᵖ} (f : ↑((ambientAb D).obj U)) : Set X :=
  {q : X | ∃ h : coheight q = 1 ∧ q ∈ unop U, f ⟨q, h⟩ ≠ 0}

lemma suppSet_subset_coheight {U : (Opens ↥X)ᵒᵖ} (f : ↑((ambientAb D).obj U)) :
    suppSet D f ⊆ {q : X | coheight q = 1} :=
  fun _ ⟨h, _⟩ => h.1

lemma suppSet_zero (U : (Opens ↥X)ᵒᵖ) : suppSet D (0 : ↑((ambientAb D).obj U)) = ∅ :=
  Set.eq_empty_iff_forall_notMem.mpr fun _ ⟨_, hne⟩ => hne rfl

lemma suppSet_add_subset {U : (Opens ↥X)ᵒᵖ} (f g : ↑((ambientAb D).obj U)) :
    suppSet D (f + g) ⊆ suppSet D f ∪ suppSet D g := by
  intro q hq
  obtain ⟨h, hne⟩ := hq
  by_cases hf : f ⟨q, h⟩ = 0
  · exact Or.inr ⟨h, fun hg => hne (by
      show f ⟨q, h⟩ + g ⟨q, h⟩ = 0
      rw [hf, hg, add_zero])⟩
  · exact Or.inl ⟨h, hf⟩

lemma suppSet_smul_subset {U : (Opens ↥X)ᵒᵖ} (a : ↑(X.ringCatSheaf.obj.obj U))
    (f : ↑((ambientAb D).obj U)) :
    suppSet D (a • f) ⊆ suppSet D f := by
  intro q hq
  obtain ⟨h, hne⟩ := hq
  refine ⟨h, fun hf => hne ?_⟩
  rw [smul_apply, hf, smul_zero]

/-! ### The ambient presheaf is a flasque sheaf -/

/-- The ambient presheaf of all families is a sheaf: gluing is pointwise. -/
lemma ambient_isSheaf : TopCat.Presheaf.IsSheaf (ambientAb D) := by
  rw [TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing]
  intro ι U sf hsf
  classical
  -- Compatibility gives pointwise agreement of the sections at common points.
  have key : ∀ (i j : ι) (q : X) (hq : coheight q = 1) (hi : q ∈ U i) (hj : q ∈ U j),
      sf i ⟨q, hq, hi⟩ = sf j ⟨q, hq, hj⟩ := fun i j q hq hi hj =>
    congrFun (hsf i j) (⟨q, hq, hi, hj⟩ : Index (U i ⊓ U j))
  choose jdx hjdx using fun i : Index (iSup U) => Opens.mem_iSup.mp i.2.2
  refine ⟨fun i => sf (jdx i) ⟨i.1, i.2.1, hjdx i⟩,
    fun j => funext fun i => ?_, fun t ht => funext fun i => ?_⟩
  · exact key (jdx ⟨i.1, i.2.1, (Opens.leSupr U j).le i.2.2⟩) j i.1 i.2.1 (hjdx _) i.2.2
  · exact congrFun (ht (jdx i)) ⟨i.1, i.2.1, hjdx i⟩

/-- The ambient presheaf of all families is flasque: families extend by zero. -/
instance ambientAb_isFlasque : TopCat.Presheaf.IsFlasque (ambientAb D) where
  epi {U V} r := by
    rw [AddCommGrpCat.epi_iff_surjective]
    intro f
    classical
    exact ⟨fun j => if h : j.1 ∈ unop V then f ⟨j.1, j.2.1, h⟩ else 0,
      funext fun j => dif_pos j.2.2⟩

/-! ### The sheaf of principal parts as a finitely-supported submodule -/

/-- The finite-support predicate carves the sheaf of principal parts out of the ambient
presheaf of all families, as a `PresheafOfModules.Submodule`. -/
noncomputable def submodule : PresheafOfModules.Submodule (ambient D) where
  obj U :=
    { carrier := {f : ↑((ambientAb D).obj U) | (suppSet D f).Finite}
      add_mem' := fun hf hg => ((hf.union hg).subset (suppSet_add_subset D _ _))
      zero_mem' := by
        change (suppSet D (0 : ↑((ambientAb D).obj U))).Finite
        rw [suppSet_zero]
        exact Set.finite_empty
      smul_mem' := fun a f hf => hf.subset (suppSet_smul_subset D a f) }
  map {U V} r := fun f hf => Submodule.mem_comap.mpr <|
    hf.subset fun q hq => by
      obtain ⟨h, hne⟩ := hq
      exact ⟨⟨h.1, leOfHom r.unop h.2⟩, fun h0 => hne h0⟩

/-- The presheaf of modules of principal parts: finitely supported families. -/
noncomputable def partsPresheaf : PresheafOfModules.{u} X.ringCatSheaf.obj :=
  (submodule D).toPresheafOfModules

/-- The sheaf of principal parts is a sheaf: it glues in the ambient sheaf of all families,
and the glued family is finitely supported because opens of a Noetherian scheme are
quasi-compact, so a finite subcover controls the support. -/
lemma partsPresheaf_isSheaf [IsNoetherian X] :
    TopCat.Presheaf.IsSheaf (partsPresheaf D).presheaf := by
  rw [TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing]
  intro ι U sf hsf
  classical
  have hamb := (TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing _).mp (ambient_isSheaf D)
  obtain ⟨s, hs, huniq⟩ := hamb U (fun i => (sf i).1)
    (fun i j => congrArg Subtype.val (hsf i j))
  -- A finite subcover controls the support of the glued family.
  have hcpt : IsCompact ((iSup U : Opens ↥X) : Set ↥X) := NoetherianSpace.isCompact _
  obtain ⟨T, hT⟩ := hcpt.elim_finite_subcover (fun i => ((U i : Opens ↥X) : Set ↥X))
    (fun i => (U i).isOpen) (by simpa using fun q hq => Opens.mem_iSup.mp hq)
  have hmem : s ∈ (submodule D).obj (op (iSup U)) := by
    refine Set.Finite.subset (Set.Finite.biUnion T.finite_toSet
      (fun i _ => (sf i).2)) ?_
    rintro q ⟨h, hne⟩
    obtain ⟨i, hiT, hqi⟩ := Set.mem_iUnion₂.mp (hT h.2)
    exact Set.mem_biUnion hiT
      ⟨⟨h.1, hqi⟩, fun h0 => hne ((congrFun (hs i) ⟨q, h.1, hqi⟩).trans h0)⟩
  refine ⟨⟨s, hmem⟩, fun i => Subtype.ext (hs i), fun t ht => Subtype.ext ?_⟩
  exact huniq t.1 fun i => congrArg Subtype.val (ht i)

/-- The sheaf of principal parts, as a sheaf of modules. -/
noncomputable def partsSheaf [IsNoetherian X] : X.Modules where
  val := partsPresheaf D
  isSheaf := partsPresheaf_isSheaf D

/-- The sheaf of principal parts is flasque: finitely supported families extend by zero. -/
instance partsPresheaf_isFlasque : TopCat.Presheaf.IsFlasque (partsPresheaf D).presheaf where
  epi {U V} r := by
    rw [AddCommGrpCat.epi_iff_surjective]
    rintro ⟨f, hf⟩
    classical
    refine ⟨⟨fun j => if h : j.1 ∈ unop V then f ⟨j.1, j.2.1, h⟩ else 0, ?_⟩,
      Subtype.ext (funext fun j => dif_pos j.2.2)⟩
    refine hf.subset ?_
    rintro q ⟨h, hne⟩
    by_cases hq : q ∈ unop V
    · exact ⟨⟨h.1, hq⟩, fun h0 => hne ((dif_pos hq).trans h0)⟩
    · exact absurd (dif_neg hq) hne

instance [IsNoetherian X] :
    TopCat.Sheaf.IsFlasque ((SheafOfModules.toSheaf X.ringCatSheaf).obj (partsSheaf D)) :=
  inferInstanceAs (TopCat.Presheaf.IsFlasque (partsPresheaf D).presheaf)

/-! ### Bridging the divisor bound and the components -/

/-- A rational function satisfying the divisor bound on `U` has principal part of order at
least `-D q` at every codimension-one `q ∈ U`. -/
lemma mem_ordSubmodule_of_mem_carrier {U : X.Opens} {f : ↑X.functionField}
    (hf : f ∈ Sheaf.carrier D U) {q : X} (hq : coheight q = 1) (hqU : q ∈ U) :
    f ∈ ordSubmodule hq (-D q) := fun hne => by
  have h := (Sheaf.mem_carrier_iff.mp hf hne).2 q hqU
  omega

/-- Conversely, for `D` supported in codimension one, order bounds at the codimension-one
points of a nonempty `U` give the divisor bound on `U` (the bound at other points is
automatic since `ord` vanishes there). -/
lemma mem_carrier_of_forall_ordSubmodule (hD : D.support ⊆ {x | coheight x = 1})
    {U : X.Opens} (hU : Nonempty U) {f : ↑X.functionField}
    (h : ∀ (q : X) (hq : coheight q = 1), q ∈ U → f ∈ ordSubmodule hq (-D q)) :
    f ∈ Sheaf.carrier D U :=
  Sheaf.mem_carrier_iff.mpr fun hne => ⟨hU, fun z hz => by
    by_cases hz1 : coheight z = 1
    · have h1 := h z hz1 hz hne
      omega
    · have h1 : X.ord f z = 0 := Scheme.ord_eq_zero_of_coheight_neq_one hz1 f
      have h2 : D z = 0 := by
        by_contra h0
        exact hz1 (hD (Function.mem_support.mpr h0))
      omega⟩

/-! ### The quotient morphism `𝒦 ⟶ Q(D)` -/

/-- The family of principal parts of a section of the sheaf of rational functions. -/
noncomputable def toPartsFun {U : (Opens ↥X)ᵒᵖ} (s : ↑((functionFieldSheaf X).val.obj U)) :
    ↑((ambientAb D).obj U) :=
  fun i => Component.mk D i.2.1 (eval ⟨⟨genericPoint_mem i.2.2⟩⟩ s)

/-- The family of principal parts of a rational function is finitely supported: its support
is contained in the (quasi-compact) open intersected with the support of `div f + D`. -/
lemma finite_suppSet_toPartsFun [IsNoetherian X] {U : (Opens ↥X)ᵒᵖ}
    (s : ↑((functionFieldSheaf X).val.obj U)) :
    (suppSet D (toPartsFun D s)).Finite := by
  classical
  rcases isEmpty_or_nonempty (Index (unop U)) with hU | hne₀
  · refine Set.Finite.subset Set.finite_empty ?_
    rintro q ⟨h, -⟩
    exact (hU.false (⟨q, h⟩ : Index (unop U))).elim
  · obtain ⟨i₀⟩ := hne₀
    set f : ↑X.functionField := eval ⟨⟨genericPoint_mem i₀.2.2⟩⟩ s with hf_def
    refine Set.Finite.subset
      (LocallyFiniteSupport.finite_inter_support_of_isCompact
        (div f + D).locallyFiniteSupport
        (NoetherianSpace.isCompact ((unop U : Opens ↥X) : Set ↥X))) ?_
    rintro q ⟨h, hne⟩
    have hne' : ¬ (Component.mk D h.1 f = 0) := hne
    rw [Component.mk_eq_zero_iff, mem_ordSubmodule_iff] at hne'
    push_neg at hne'
    obtain ⟨hf0, hlt⟩ := hne'
    refine ⟨h.2, Function.mem_support.mpr ?_⟩
    simp only [Function.locallyFinsuppWithin.coe_add, Pi.add_apply, div_eq_ord]
    omega

/-- The morphism of abelian presheaves sending a rational function to its family of
principal parts. -/
noncomputable def toPartsAb [IsNoetherian X] :
    (functionFieldSheaf X).val.presheaf ⟶ (partsPresheaf D).presheaf where
  app U := AddCommGrpCat.ofHom (AddMonoidHom.mk'
    (fun s => ⟨toPartsFun D s, finite_suppSet_toPartsFun D s⟩)
    (fun s t => Subtype.ext (funext fun i =>
      congrArg (Component.mk D i.2.1) (eval_add ⟨⟨genericPoint_mem i.2.2⟩⟩ s t))))
  naturality {U V} r := by
    ext s
    refine Subtype.ext (funext fun i => ?_)
    exact congrArg (Component.mk D i.2.1)
      (eval_presheaf_map r ⟨⟨genericPoint_mem i.2.2⟩⟩ s)

/-- `toPartsAb` is semilinear: the principal part of `a • s` at `q` is the germ of `a` at `q`
acting on the principal part of `s`, because both are computed by multiplication by the image
of `a` in the function field. -/
lemma toPartsAb_smul [IsNoetherian X] (U : (Opens ↥X)ᵒᵖ) (a : ↑(X.ringCatSheaf.obj.obj U))
    (s : ↑((functionFieldSheaf X).val.obj U)) :
    (toPartsAb D).app U (a • s) = a • (toPartsAb D).app U s := by
  refine Subtype.ext (funext fun i => ?_)
  have hgerm : algebraMap ↑(X.presheaf.stalk i.1) ↑X.functionField
      (X.presheaf.germ (unop U) i.1 i.2.2 a) =
      X.presheaf.germ (unop U) (genericPoint X) (genericPoint_mem i.2.2) a := by
    haveI : Nonempty ↑(unop U) := ⟨⟨i.1, i.2.2⟩⟩
    rw [Scheme.algebraMap_germ_eq_germToFunctionField i.2.2]
  show Component.mk D i.2.1 (eval ⟨⟨genericPoint_mem i.2.2⟩⟩ (a • s)) =
    X.presheaf.germ (unop U) i.1 i.2.2 a •
      Component.mk D i.2.1 (eval ⟨⟨genericPoint_mem i.2.2⟩⟩ s)
  rw [eval_smul, ← hgerm, ← Algebra.smul_def, Component.mk_smul]

/-- The quotient morphism from the sheaf of rational functions to the sheaf of principal
parts, as a morphism of sheaves of modules. -/
noncomputable def toPartsHom [IsNoetherian X] : functionFieldSheaf X ⟶ partsSheaf D :=
  ⟨PresheafOfModules.homMk (toPartsAb D) (toPartsAb_smul D)⟩

/-! ### The short exact sequence `0 ⟶ 𝒪ₓ(D) ⟶ 𝒦 ⟶ Q(D) ⟶ 0` -/

/-- The inclusion of the divisorial sheaf in the sheaf of rational functions. -/
noncomputable def iotaSheaf : sheaf D ⟶ functionFieldSheaf X :=
  ⟨(divisorSubmodule D).ι⟩

instance iotaSheaf_mono : Mono (iotaSheaf D) := by
  suffices h : ∀ (U : (Opens ↥X)ᵒᵖ),
      Function.Injective (((divisorSubmodule D).ι).app U) by
    suffices Mono ((SheafOfModules.toSheaf X.ringCatSheaf).map (iotaSheaf D)) by
      cat_disch
    exact Sheaf.mono_of_injective _ h
  intro U a b hab
  exact Subtype.ext hab

/-- The complex `0 ⟶ 𝒪ₓ(D) ⟶ 𝒦 ⟶ Q(D)`: the divisor bound at each codimension-one point
says exactly that all principal parts vanish. -/
noncomputable def partsComplex [IsNoetherian X] : ShortComplex X.Modules where
  X₁ := sheaf D
  X₂ := functionFieldSheaf X
  X₃ := partsSheaf D
  f := iotaSheaf D
  g := toPartsHom D
  zero := by
    apply SheafOfModules.Hom.ext
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.hom_ext
    ext s
    have hR := zero_hom_app_apply (A := sheaf D) (B := partsSheaf D) U s
    rw [hR]
    refine Subtype.ext (funext fun i => ?_)
    show Component.mk D i.2.1 (eval ⟨⟨genericPoint_mem i.2.2⟩⟩ s.1) = 0
    exact (Component.mk_eq_zero_iff D i.2.1).mpr
      (mem_ordSubmodule_of_mem_carrier D (s.2 ⟨⟨genericPoint_mem i.2.2⟩⟩) i.2.1 i.2.2)

/-- Exactness of the principal-parts complex: a rational function all of whose principal
parts vanish satisfies the divisor bound, so any test morphism killing the principal parts
factors through the divisorial sheaf. -/
lemma partsComplex_exact [IsNoetherian X] (hD : D.support ⊆ {x | coheight x = 1}) :
    (partsComplex D).Exact := by
  haveI : Mono (partsComplex D).f := inferInstanceAs (Mono (iotaSheaf D))
  apply ShortComplex.exact_of_f_is_kernel
  refine KernelFork.IsLimit.ofι' _ _ fun {A} k hk => ⟨⟨?lift⟩, ?fac⟩
  case lift =>
    refine PresheafOfModules.Submodule.lift (divisorSubmodule D) k.val fun U a => ?_
    intro x
    haveI hU : Nonempty ↑(unop U) := ⟨⟨genericPoint X, x.down.down⟩⟩
    refine mem_carrier_of_forall_ordSubmodule D hD hU fun q hq hqU => ?_
    have h0 := congrArg
      (fun (ψ : A ⟶ partsSheaf D) => ((ψ.val.app U) a).1 ⟨q, hq, hqU⟩) hk
    have hR : (((0 : A ⟶ partsSheaf D).val.app U) a) = 0 := zero_hom_app_apply U a
    have hz : Component.mk D hq
        (eval ⟨⟨genericPoint_mem hqU⟩⟩ ((k.val.app U) a)) = 0 := by
      refine h0.trans ?_
      rw [hR]
      rfl
    exact (Component.mk_eq_zero_iff D hq).mp hz
  case fac =>
    apply SheafOfModules.Hom.ext
    exact PresheafOfModules.Submodule.lift_comp_ι (divisorSubmodule D) k.val _

/-- Codimension-one points are closed, given that nothing specializes properly into them. -/
lemma isClosed_singleton_of_forall_le
    (hcl : ∀ p : X, coheight p = 1 → ∀ y, y ≤ p → y = p)
    {p : X} (hp : coheight p = 1) : IsClosed ({p} : Set X) :=
  isClosed_of_closure_subset fun w hw =>
    hcl p hp w (Scheme.le_iff_specializes.mpr (specializes_iff_mem_closure.mpr hw))

/-- The heart of the surjectivity of `𝒦 ⟶ Q(D)`: given a finitely supported family `t` of
principal parts over `U`, a point `z ∈ U`, and a rational function `g` representing the
component of `t` at `z` (vacuously, if `z` is not a codimension-one point), the constant
section `g` maps to `t` on the neighbourhood of `z` obtained by deleting the (finitely many,
closed) other support points of `t` and poles of `g`. -/
lemma exists_eq_restriction [IsNoetherian X] (hD : D.support ⊆ {x | coheight x = 1})
    (hcl : ∀ p : X, coheight p = 1 → ∀ y, y ≤ p → y = p)
    {U : X.Opens} (t : ↑((partsPresheaf D).presheaf.obj (op U)))
    {z : X} (hzU : z ∈ U) (g : ↑X.functionField)
    (hgz : ∀ hz1 : coheight z = 1, Component.mk D hz1 g = t.1 ⟨z, hz1, hzU⟩) :
    ∃ (V : X.Opens) (hVU : V ≤ U) (_ : z ∈ V),
      (toPartsAb D).app (op V) (constSection g) =
        (partsPresheaf D).presheaf.map (homOfLE hVU).op t := by
  classical
  -- The bad set: support points of `t` and poles of `g` (relative to `D`), except `z`.
  set B : Set X :=
    (suppSet D t.1 ∪ ((U : Set X) ∩ Function.support ⇑(div g + D))) \ {z} with hB_def
  have hBfin : B.Finite :=
    Set.Finite.diff (Set.Finite.union t.2
      (LocallyFiniteSupport.finite_inter_support_of_isCompact
        (div g + D).locallyFiniteSupport (NoetherianSpace.isCompact (U : Set X))))
  have hBcodim : ∀ p ∈ B, coheight p = 1 := by
    rintro p ⟨hp, -⟩
    rcases hp with hp | ⟨-, hp⟩
    · exact suppSet_subset_coheight D t.1 hp
    · by_contra h1
      have hdg : X.ord g p = 0 := Scheme.ord_eq_zero_of_coheight_neq_one h1 g
      have hDp : D p = 0 := by
        by_contra h0
        exact h1 (hD (Function.mem_support.mpr h0))
      refine hp ?_
      simp only [Function.mem_support, ne_eq, not_not,
        Function.locallyFinsuppWithin.coe_add, Pi.add_apply, div_eq_ord]
      omega
  have hBclosed : IsClosed B := by
    rw [← Set.biUnion_of_singleton B]
    exact hBfin.isClosed_biUnion fun p hp =>
      isClosed_singleton_of_forall_le hcl (hBcodim p hp)
  refine ⟨U ⊓ ⟨Bᶜ, hBclosed.isOpen_compl⟩, inf_le_left, ⟨hzU, fun hzB => hzB.2 rfl⟩, ?_⟩
  refine Subtype.ext (funext fun i => ?_)
  obtain ⟨q, hq1, hqV⟩ := i
  have hqU' : q ∈ U := (inf_le_left : U ⊓ ⟨Bᶜ, hBclosed.isOpen_compl⟩ ≤ U) hqV
  have hqB : q ∉ B := (inf_le_right : U ⊓ ⟨Bᶜ, hBclosed.isOpen_compl⟩ ≤ _) hqV
  show Component.mk D hq1 (eval ⟨⟨genericPoint_mem hqV⟩⟩ (constSection g)) =
    t.1 ⟨q, hq1, hqU'⟩
  rw [eval_constSection]
  rcases eq_or_ne q z with rfl | hqz
  · exact hgz hq1
  · have hqsupp : q ∉ suppSet D t.1 := fun hmem => hqB ⟨Or.inl hmem, hqz⟩
    have ht0 : t.1 ⟨q, hq1, hqU'⟩ = 0 := by
      by_contra h0
      exact hqsupp ⟨⟨hq1, hqU'⟩, h0⟩
    have hord : X.ord g q + D q = 0 := by
      have hpole : q ∉ Function.support ⇑(div g + D) :=
        fun h0 => hqB ⟨Or.inr ⟨hqU', h0⟩, hqz⟩
      simp only [Function.mem_support, ne_eq, not_not,
        Function.locallyFinsuppWithin.coe_add, Pi.add_apply, div_eq_ord] at hpole
      omega
    have hmem : g ∈ ordSubmodule hq1 (-D q) := fun _ => by omega
    rw [ht0]
    exact (Component.mk_eq_zero_iff D hq1).mpr hmem

/-- The principal-parts complex is short exact: the quotient map is locally surjective
because a principal part at `q` is represented by an actual rational function near `q`. -/
lemma partsComplex_shortExact [IsNoetherian X] (hD : D.support ⊆ {x | coheight x = 1})
    (hcl : ∀ p : X, coheight p = 1 → ∀ y, y ≤ p → y = p) :
    (partsComplex D).ShortExact where
  exact := partsComplex_exact D hD
  mono_f := inferInstanceAs (Mono (iotaSheaf D))
  epi_g := by
    have h : Sheaf.IsLocallySurjective
        ((SheafOfModules.toSheaf X.ringCatSheaf).map (toPartsHom D)) := by
      refine (TopCat.Presheaf.isLocallySurjective_iff _).mpr ?_
      intro U t z hzU
      classical
      by_cases hz1 : coheight z = 1
      · obtain ⟨g, hg⟩ := Component.mk_surjective D hz1 (t.1 ⟨z, hz1, hzU⟩)
        obtain ⟨V, hVU, hzV, heq⟩ := exists_eq_restriction D hD hcl t hzU g (fun _ => hg)
        exact ⟨V, hVU, ⟨constSection g, heq⟩, hzV⟩
      · obtain ⟨V, hVU, hzV, heq⟩ := exists_eq_restriction D hD hcl t hzU 0
          (fun h => absurd h hz1)
        exact ⟨V, hVU, ⟨constSection 0, heq⟩, hzV⟩
    exact (SheafOfModules.toSheaf X.ringCatSheaf).epi_of_epi_map
      ((CategoryTheory.Sheaf.isLocallySurjective_iff_epi'
        (φ := (SheafOfModules.toSheaf X.ringCatSheaf).map (toPartsHom D))).mp h)

end PrincipalParts

/-! ### Vanishing of `Hⁿ(X, 𝒪ₓ)` for `n ≥ 2`, and Riemann–Roch from `H⁰` and `H¹` alone -/

section Consequences

variable (k : Type u) [Field k] [X.Over (Spec (CommRingCat.of k))]

include k in
/-- **Unconditional vanishing.** On a Noetherian integral scheme, regular in codimension one,
whose codimension-one points are closed, the divisorial structure sheaf `𝒪ₓ = 𝒪ₓ(0)` has no
cohomology in degrees `≥ 2`: it admits the two-step flasque resolution
`0 ⟶ 𝒪ₓ ⟶ 𝒦 ⟶ Q(0) ⟶ 0` by the sheaf of rational functions and the sheaf of principal
parts. This discharges the vanishing hypothesis of `riemann_roch_of_structureSheaf`
with `N = 1`. -/
theorem subsingleton_H_structureSheaf [IsNoetherian X]
    (hcl : ∀ p : X, coheight p = 1 → ∀ y, y ≤ p → y = p)
    {n : ℕ} (hn : 1 < n) :
    Subsingleton ((sheaf (0 : AlgebraicCycle X ℤ)).H n) :=
  subsingleton_H_structureSheaf_of_flasque_ses k (PrincipalParts.partsComplex 0)
    (shortExact_map_toSheaf (PrincipalParts.partsComplex_shortExact 0 (by simp) hcl))
    rfl
    (inferInstanceAs (TopCat.Sheaf.IsFlasque ((SheafOfModules.toSheaf X.ringCatSheaf).obj
      (skyscraperSheafOfModules (genericPoint X) X.ringCatSheaf ↑X.functionField))))
    (inferInstanceAs (TopCat.Sheaf.IsFlasque ((SheafOfModules.toSheaf X.ringCatSheaf).obj
      (PrincipalParts.partsSheaf 0))))
    hn

open Order in
/-- **Riemann–Roch, assuming only `H⁰` and `H¹` finiteness.** Let `X` be a curve over `k`
(integral, Noetherian, regular in codimension one, of Krull dimension at most one, locally of
finite type over `k`). If `H⁰(X, 𝒪ₓ)` and `H¹(X, 𝒪ₓ)` are finite dimensional over `k`, then
for every Weil divisor `D`, `χ(𝒪ₓ(D)) = deg D + χ(𝒪ₓ)`.

All the cohomological hypotheses above degree one are discharged by the flasque resolution by
principal parts; the two remaining ones are the content of properness of `X` over `k`
(for `X` proper: `H⁰` is a finite field extension of `k` and `H¹` is the genus). -/
theorem riemann_roch_of_finite_H0_H1 [IsNoetherian X] [Order.KrullDimLE 1 X]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k))]
    (h0 : Module.Finite k ((sheaf (0 : AlgebraicCycle X ℤ)).H 0))
    (h1 : Module.Finite k ((sheaf (0 : AlgebraicCycle X ℤ)).H 1))
    {D : AlgebraicCycle X ℤ} (hD : D.support ⊆ {x | coheight x = 1}) :
    (sheaf D).eulerChar k =
      D.degree k + (sheaf (0 : AlgebraicCycle X ℤ)).eulerChar k := by
  have hcl : ∀ p : X, coheight p = 1 → ∀ y, y ≤ p → y = p := fun p hp y hy =>
    have hmin : IsMin p :=
      Order.KrullDimLE.isMin_of_le_coheight (n := 1) (by simpa using hp.ge)
    ((Scheme.le_iff_specializes.mp (hmin hy)).antisymm (Scheme.le_iff_specializes.mp hy)).eq
  have hb₀ : ∀ n, 1 < n → Subsingleton ((sheaf (0 : AlgebraicCycle X ℤ)).H n) :=
    fun _ hn => subsingleton_H_structureSheaf k hcl hn
  have hf₀ : ∀ n, Module.Finite k ((sheaf (0 : AlgebraicCycle X ℤ)).H n) := by
    intro n
    match n with
    | 0 => exact h0
    | 1 => exact h1
    | (m + 2) =>
      haveI := hb₀ (m + 2) (by omega)
      exact ⟨⟨∅, Subsingleton.elim _ _⟩⟩
  exact riemann_roch_of_structureSheaf_of_locallyOfFiniteType k (N := 1) hf₀ hb₀ hD

end Consequences

end SheafViaSubmodule
end AlgebraicGeometry.AlgebraicCycle
