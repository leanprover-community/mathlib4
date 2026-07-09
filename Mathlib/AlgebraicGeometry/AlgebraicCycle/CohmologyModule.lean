module

public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Over
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.Combinatorics.Quiver.ReflQuiver

open CategoryTheory AlgebraicGeometry Scheme

@[expose] public section

universe u

variable {X : Scheme.{u}} {R : CommRingCat} [X.Over (Spec R)] (F : X.Modules)

/-- The structure morphism `X ↘ Spec R` induces a ring homomorphism `R → Γ(X, ⊤)`
via the Γ–Spec adjunction (`ΓSpecIso`). -/
noncomputable def globalSec : R →+* Γ(X, ⊤) :=
  ((Scheme.ΓSpecIso R).inv ≫ (X ↘ Spec R).appTop).hom

/-- The structure morphism `X ↘ Spec R` induces a ring homomorphism `R → Γ(X, U)`
for every open `U`, via the Γ–Spec adjunction (`ΓSpecIso`) and restriction. -/
noncomputable def structureRingHom (U : X.Opens) : R →+* Γ(X, U) :=
  (X.presheaf.map U.leTop.op).hom.comp (globalSec (X := X))

lemma structureRingHom_apply (U : X.Opens) (r : R) :
    structureRingHom U r = X.presheaf.map U.leTop.op (globalSec (X := X) r) := rfl

lemma structureRingHom_naturality {U V : X.Opens} (i : U ⟶ V) (r : R) :
    X.presheaf.map i.op (structureRingHom V r) = structureRingHom U r := by
  rw [structureRingHom_apply, structureRingHom_apply, ← ConcreteCategory.comp_apply,
    ← X.presheaf.map_comp]
  congr 1

noncomputable instance {U : X.Opens} : Module R Γ(F, U) :=
  Module.compHom Γ(F, U) (structureRingHom U)

lemma smul_presheaf_map {U V : X.Opens} (i : U ⟶ V) (r : R) (x : Γ(F, V)) :
    F.presheaf.map i.op (r • x) = r • F.presheaf.map i.op x := by
  change F.presheaf.map i.op (structureRingHom V r • x)
    = structureRingHom U r • F.presheaf.map i.op x
  rw [Scheme.Modules.map_smul, structureRingHom_naturality]

open CategoryTheory.Abelian in
@[simp]
lemma CategoryTheory.Abelian.Ext.homEquiv_symm_zero {C : Type*} [Category* C] [Abelian C]
    [HasExt C] {X Y : C} [HasDerivedCategory C] {n : ℕ} :
    (Ext.homEquiv (C := C) (X := X) (Y := Y) (n := n)).symm Zero.zero = 0 := by
  ext : 1
  simp_all only [Equiv.apply_symm_apply, Ext.zero_hom]
  rfl


open CategoryTheory.Abelian in
/-- Given a ring homomorphism `φ : R →+* End G` into the endomorphism ring of an object `G`
of an abelian category, the groups `Ext A G n` become `R`-modules, with `r` acting by
postcomposition with `mk₀ (φ r)`. This is the additivity of `Ext` (in the second variable)
packaged as a module structure. -/
noncomputable def extModuleOfRingHom {𝒜 : Type*} [Category 𝒜] [Abelian 𝒜] [HasExt 𝒜]
    {A G : 𝒜} (φ : R →+* CategoryTheory.End G) (n : ℕ) :
    Module R (Ext A G n) where
  smul r x := x.comp (Ext.mk₀ (φ r)) (add_zero n)
  one_smul x := by
    change x.comp (Ext.mk₀ (φ 1)) (add_zero n) = x
    rw [map_one, End.one_def, Ext.comp_mk₀_id]
  mul_smul r s x := by
    change x.comp (Ext.mk₀ (φ (r * s))) (add_zero n) =
      (x.comp (Ext.mk₀ (φ s)) (add_zero n)).comp (Ext.mk₀ (φ r)) (add_zero n)
    rw [map_mul, End.mul_def, ← Ext.mk₀_comp_mk₀, Ext.comp_assoc_of_third_deg_zero]
  smul_zero r := by
    unfold_projs
    simp
  zero_smul x := by
    change x.comp (Ext.mk₀ (φ 0)) (add_zero n) = 0
    rw [map_zero]
    change x.comp (Ext.mk₀ (0 : G ⟶ G)) (add_zero n) = 0
    rw [Ext.mk₀_zero, Ext.comp_zero]
  smul_add r x y := by
    change (x + y).comp (Ext.mk₀ (φ r)) (add_zero n) =
      x.comp (Ext.mk₀ (φ r)) (add_zero n) + y.comp (Ext.mk₀ (φ r)) (add_zero n)
    rw [Ext.add_comp]
  add_smul r s x := by
    have h : ∀ g₁ g₂ : G ⟶ G, x.comp (Ext.mk₀ (g₁ + g₂)) (add_zero n) =
        x.comp (Ext.mk₀ g₁) (add_zero n) + x.comp (Ext.mk₀ g₂) (add_zero n) := by
      intro g₁ g₂; rw [Ext.mk₀_add, Ext.comp_add]
    change x.comp (Ext.mk₀ (φ (r + s))) (add_zero n) =
      x.comp (Ext.mk₀ (φ r)) (add_zero n) + x.comp (Ext.mk₀ (φ s)) (add_zero n)
    rw [map_add]
    exact h (φ r) (φ s)

/-- The underlying natural transformation of "multiplication by `r`" on `G = toSheaf F`. -/
noncomputable def smulNatTrans (r : R) :
    ((SheafOfModules.toSheaf X.ringCatSheaf).obj F).obj ⟶
      ((SheafOfModules.toSheaf X.ringCatSheaf).obj F).obj where
  app U := AddCommGrpCat.ofHom (DistribSMul.toAddMonoidHom (Γ(F, U.unop)) r)
  naturality U V f := by
    ext x
    exact (smul_presheaf_map F f.unop r x).symm

/-- Scalar multiplication by `r : R` acts as an endomorphism of `G = toSheaf F`, the underlying
abelian sheaf of the `𝒪_X`-module `F`. This packages "a global section of `𝒪_X` acts on `F`"
(equivalently, `H⁰(𝒪_X) = Γ(X, 𝒪_X)` acting via the structure map `R → Γ(X, ⊤)`). -/
noncomputable def smulEnd :
    R →+* CategoryTheory.End ((SheafOfModules.toSheaf _).obj F) where
  toFun r := Sheaf.homEquiv.symm (smulNatTrans F r)
  map_one' := by
    apply Sheaf.hom_ext
    refine NatTrans.ext (funext fun U => ?_)
    have key : DistribSMul.toAddMonoidHom Γ(F, U.unop) (1 : R) = AddMonoidHom.id _ := by
      ext y; exact one_smul R y
    exact congrArg AddCommGrpCat.ofHom key
  map_mul' r s := by
    apply Sheaf.hom_ext
    refine NatTrans.ext (funext fun U => ?_)
    have key : DistribSMul.toAddMonoidHom Γ(F, U.unop) (r * s) =
        (DistribSMul.toAddMonoidHom Γ(F, U.unop) r).comp
          (DistribSMul.toAddMonoidHom Γ(F, U.unop) s) := by
      ext y; exact mul_smul r s y
    exact congrArg AddCommGrpCat.ofHom key
  map_zero' := by
    apply Sheaf.hom_ext
    refine NatTrans.ext (funext fun U => ?_)
    have key : DistribSMul.toAddMonoidHom Γ(F, U.unop) (0 : R) = 0 := by
      ext y; exact zero_smul R y
    exact congrArg AddCommGrpCat.ofHom key
  map_add' r s := by
    apply Sheaf.hom_ext
    refine NatTrans.ext (funext fun U => ?_)
    have key : DistribSMul.toAddMonoidHom Γ(F, U.unop) (r + s) =
        DistribSMul.toAddMonoidHom Γ(F, U.unop) r +
          DistribSMul.toAddMonoidHom Γ(F, U.unop) s := by
      ext y; exact add_smul r s y
    exact congrArg AddCommGrpCat.ofHom key

noncomputable instance {n : ℕ} :
    Module R (((SheafOfModules.toSheaf _).obj F).H n) :=
  extModuleOfRingHom (smulEnd F) n

/--
The `k`-module structure on the sheaf cohomology of a scheme over `Spec (CommRingCat.of k)`,
keyed to `k` itself. This is definitionally the instance above at `R := CommRingCat.of k`;
restating it lets instance search find it for goals phrased directly over `k`, which cannot
unify `k =?= ↥?R` on their own.
-/
noncomputable instance {k : Type u} [CommRing k] [X.Over (Spec (CommRingCat.of k))] {n : ℕ} :
    Module k (((SheafOfModules.toSheaf _).obj F).H n) :=
  extModuleOfRingHom (smulEnd (R := CommRingCat.of k) F) n

/-- `Hⁿ(F)`: the `n`-th cohomology of the underlying abelian sheaf
`(SheafOfModules.toSheaf _).obj F` of the `𝒪_X`-module `F`. For a scheme over `Spec R` this
type carries an `R`-module structure by functoriality (the instances above). -/
abbrev AlgebraicGeometry.Scheme.Modules.H (F : X.Modules) (n : ℕ) :=
  ((SheafOfModules.toSheaf X.ringCatSheaf).obj F).H n

/-- A sheaf of modules on a scheme over a ring `k` has finite cohomology if each of its
cohomology modules `Hⁿ(F)` is a finite `k`-module. For a curve proper over a field `k` and `F`
coherent this holds by the finiteness theorem for coherent cohomology (EGA III 3.2.1). -/
def AlgebraicGeometry.Scheme.Modules.HasFiniteCohomology (k : Type u) [CommRing k]
    [X.Over (Spec (CommRingCat.of k))] (F : X.Modules) : Prop :=
  ∀ n, Module.Finite k (F.H n)

/-- A sheaf of modules has finite cohomological dimension if its cohomology `Hⁿ(F)` vanishes in
all sufficiently large degrees. By Grothendieck's vanishing theorem this holds (with bound
`dim X`) for every sheaf on a finite-dimensional Noetherian scheme. -/
def AlgebraicGeometry.Scheme.Modules.HasFiniteCohomologicalDimension (F : X.Modules) : Prop :=
  ∃ N : ℕ, ∀ n, N < n → Subsingleton (F.H n)

/-- A sheaf of modules has a (well-defined) Euler characteristic over `k` if its cohomology is
finite dimensional in every degree and vanishes in all sufficiently large degrees. This is
precisely the condition under which `Scheme.Modules.eulerChar` computes the honest alternating
sum `∑ₙ (-1)ⁿ hⁿ(F)` rather than the junk value `0` of an infinite `finsum`. For a coherent
sheaf on a scheme proper over a field `k` this holds by the finiteness theorem for coherent
cohomology (EGA III 3.2.1) and Grothendieck vanishing. -/
structure AlgebraicGeometry.Scheme.Modules.HasEulerCharacteristic (k : Type u) [CommRing k]
    [X.Over (Spec (CommRingCat.of k))] (F : X.Modules) : Prop where
  /-- Every cohomology module of `F` is a finite `k`-module. -/
  finite : F.HasFiniteCohomology k
  /-- The cohomology of `F` vanishes in all sufficiently large degrees. -/
  vanishing : F.HasFiniteCohomologicalDimension
