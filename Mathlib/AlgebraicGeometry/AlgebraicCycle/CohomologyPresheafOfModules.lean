module

public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic

/-!
# The cohomology presheaf of a sheaf of modules, as a presheaf of modules

Let `F` be a sheaf of `𝒪_X`-modules on a scheme `X`. Multiplication by a global section
`r : Γ(X, ⊤)` is an endomorphism of the underlying abelian sheaf of `F` (`globalSMulEnd`), so by
functoriality of `Ext` in the second variable every group `Ext A ((toSheaf _).obj F) n` is a
`Γ(X, ⊤)`-module (`Ext.moduleOfRingHom`). In particular:

* the sheaf cohomology `((SheafOfModules.toSheaf _).obj F).H n` is a `Γ(X, ⊤)`-module, with no
  need for a `X.Over (Spec R)` hypothesis (the `R`-module structure of
  `Mathlib.AlgebraicGeometry.AlgebraicCycle.CohmologyModule` is recovered by restricting
  scalars along the structure map `R →+* Γ(X, ⊤)`);
* every value `Hⁿ(U, F)` of the cohomology presheaf `Sheaf.cohomologyPresheaf` is a
  `Γ(X, ⊤)`-module, and since the restriction maps of the cohomology presheaf act on the
  *first* `Ext`-variable while the module structure acts on the *second*, associativity of the
  composition product makes the restriction maps linear. This upgrades the cohomology presheaf
  to a presheaf of `Γ(X, ⊤)`-modules, `cohomologyPresheafOfModules`.

## TODO

Upgrade `cohomologyPresheafOfModules` to a presheaf of modules over `𝒪_X` itself, where
`r : Γ(X, U)` acts on `Hⁿ(U, F)`. Since `r` is only defined over `U`, multiplication by `r` is
an endomorphism of `F` restricted to `U` and not of `F`, so this action is not visible on
`Ext A ((toSheaf _).obj F) n` directly; it should be obtained from the comparison
`Hⁿ(U, F) ≃+ H ((toSheaf _).obj F |over U) n` (a TODO of
`Mathlib.CategoryTheory.Sites.SheafCohomology.Basic`), after which the strategy of this file
applies verbatim on each over-site. Note that the resulting presheaf of modules is *not* a
sheaf for `n ≥ 1`: cohomology classes vanish locally, so the sheafification of
`U ↦ Hⁿ(U, F)` is zero in positive degrees (in degree zero it recovers `F`).
-/

open CategoryTheory AlgebraicGeometry Scheme Opposite

@[expose] public section

universe u

namespace CategoryTheory.Abelian.Ext

open CategoryTheory.Abelian

@[simp]
lemma homEquiv_symm_zero {C : Type*} [Category* C] [Abelian C] [HasExt C] {X Y : C}
    [HasDerivedCategory C] {n : ℕ} :
    (Ext.homEquiv (C := C) (X := X) (Y := Y) (n := n)).symm Zero.zero = 0 := by
  ext : 1
  simp_all only [Equiv.apply_symm_apply, Ext.zero_hom]
  rfl

/-- Given a ring homomorphism `φ : R →+* End G` into the endomorphism ring of an object `G`
of an abelian category, the groups `Ext A G n` become `R`-modules, with `r` acting by
postcomposition with `mk₀ (φ r)`. This is the additivity of `Ext` (in the second variable)
packaged as a module structure. -/
@[reducible]
noncomputable def moduleOfRingHom {𝒜 : Type*} [Category* 𝒜] [Abelian 𝒜] [HasExt 𝒜]
    {R : Type*} [Ring R] {A G : 𝒜} (φ : R →+* CategoryTheory.End G) (n : ℕ) :
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

end CategoryTheory.Abelian.Ext

section GlobalSections

open CategoryTheory.Abelian

variable {X : Scheme.{u}} (F : X.Modules)

lemma restrictTop_naturality {U V : X.Opens} (i : U ⟶ V) (r : ↑Γ(X, ⊤)) :
    X.presheaf.map i.op (X.presheaf.map V.leTop.op r) = X.presheaf.map U.leTop.op r := by
  rw [← ConcreteCategory.comp_apply, ← X.presheaf.map_comp]
  congr 1

/-- Multiplication by the restriction of a global section commutes with the restriction maps
of a sheaf of modules. -/
lemma smul_restrictTop_presheaf_map {U V : X.Opens} (i : U ⟶ V) (r : ↑Γ(X, ⊤)) (x : Γ(F, V)) :
    F.presheaf.map i.op (X.presheaf.map V.leTop.op r • x) =
      X.presheaf.map U.leTop.op r • F.presheaf.map i.op x := by
  rw [Scheme.Modules.map_smul, restrictTop_naturality]

/-- Multiplication by (the restrictions of) a global section `r : Γ(X, ⊤)`, as an endomorphism
of the underlying abelian sheaf of a sheaf of modules. -/
noncomputable def globalSMulNatTrans (r : ↑Γ(X, ⊤)) :
    ((SheafOfModules.toSheaf X.ringCatSheaf).obj F).obj ⟶
      ((SheafOfModules.toSheaf X.ringCatSheaf).obj F).obj where
  app U := AddCommGrpCat.ofHom
    (DistribSMul.toAddMonoidHom Γ(F, U.unop) (X.presheaf.map U.unop.leTop.op r))
  naturality U V f := by
    ext x
    exact (smul_restrictTop_presheaf_map F f.unop r x).symm

/-- The action of global sections of the structure sheaf on the underlying abelian sheaf of a
sheaf of modules, as a ring homomorphism into its endomorphism ring. This requires no
`X.Over (Spec R)` hypothesis: it is the intrinsic module structure of cohomology over
`H⁰(X, 𝒪_X) = Γ(X, ⊤)`. -/
noncomputable def globalSMulEnd :
    ↑Γ(X, ⊤) →+* CategoryTheory.End ((SheafOfModules.toSheaf X.ringCatSheaf).obj F) where
  toFun r := Sheaf.homEquiv.symm (globalSMulNatTrans F r)
  map_one' := by
    apply Sheaf.hom_ext
    refine NatTrans.ext (funext fun U => ?_)
    have key : DistribSMul.toAddMonoidHom Γ(F, U.unop)
        (X.presheaf.map U.unop.leTop.op (1 : ↑Γ(X, ⊤))) = AddMonoidHom.id _ := by
      ext y
      change X.presheaf.map U.unop.leTop.op (1 : ↑Γ(X, ⊤)) • y = y
      rw [map_one, one_smul]
    exact congrArg AddCommGrpCat.ofHom key
  map_mul' r s := by
    apply Sheaf.hom_ext
    refine NatTrans.ext (funext fun U => ?_)
    have key : DistribSMul.toAddMonoidHom Γ(F, U.unop)
        (X.presheaf.map U.unop.leTop.op (r * s)) =
        (DistribSMul.toAddMonoidHom Γ(F, U.unop) (X.presheaf.map U.unop.leTop.op r)).comp
          (DistribSMul.toAddMonoidHom Γ(F, U.unop) (X.presheaf.map U.unop.leTop.op s)) := by
      ext y
      change X.presheaf.map U.unop.leTop.op (r * s) • y =
        X.presheaf.map U.unop.leTop.op r • (X.presheaf.map U.unop.leTop.op s • y)
      rw [map_mul, mul_smul]
    exact congrArg AddCommGrpCat.ofHom key
  map_zero' := by
    apply Sheaf.hom_ext
    refine NatTrans.ext (funext fun U => ?_)
    have key : DistribSMul.toAddMonoidHom Γ(F, U.unop)
        (X.presheaf.map U.unop.leTop.op (0 : ↑Γ(X, ⊤))) = 0 := by
      ext y
      change X.presheaf.map U.unop.leTop.op (0 : ↑Γ(X, ⊤)) • y = 0
      rw [map_zero, zero_smul]
    exact congrArg AddCommGrpCat.ofHom key
  map_add' r s := by
    apply Sheaf.hom_ext
    refine NatTrans.ext (funext fun U => ?_)
    have key : DistribSMul.toAddMonoidHom Γ(F, U.unop)
        (X.presheaf.map U.unop.leTop.op (r + s)) =
        DistribSMul.toAddMonoidHom Γ(F, U.unop) (X.presheaf.map U.unop.leTop.op r) +
          DistribSMul.toAddMonoidHom Γ(F, U.unop) (X.presheaf.map U.unop.leTop.op s) := by
      ext y
      change X.presheaf.map U.unop.leTop.op (r + s) • y =
        X.presheaf.map U.unop.leTop.op r • y + X.presheaf.map U.unop.leTop.op s • y
      rw [map_add, add_smul]
    exact congrArg AddCommGrpCat.ofHom key

/-- Every `Ext`-group into the underlying abelian sheaf of a sheaf of modules is a module over
the global sections of the structure sheaf. This covers both the sheaf cohomology
`((SheafOfModules.toSheaf _).obj F).H n` and the values `Hⁿ(U, F)` of the cohomology presheaf
`Sheaf.cohomologyPresheaf`, uniformly in the first variable. -/
noncomputable instance extGlobalSectionsModule
    (A : Sheaf (Opens.grothendieckTopology ↑X.toPresheafedSpace) Ab) (n : ℕ) :
    Module ↑Γ(X, ⊤) (Ext A ((SheafOfModules.toSheaf X.ringCatSheaf).obj F) n) :=
  Ext.moduleOfRingHom (globalSMulEnd F) n

lemma globalSections_smul_ext_def
    {A : Sheaf (Opens.grothendieckTopology ↑X.toPresheafedSpace) Ab} {n : ℕ}
    (r : ↑Γ(X, ⊤)) (x : Ext A ((SheafOfModules.toSheaf X.ringCatSheaf).obj F) n) :
    r • x = x.comp (Ext.mk₀ (globalSMulEnd F r)) (add_zero n) :=
  rfl

/-- The free abelian sheaf generated by an open `U`: the first variable in the definition of
the cohomology presheaf `Sheaf.cohomologyPresheaf`. -/
noncomputable def freeAbelianSheaf (U : (TopologicalSpace.Opens ↑X.toPresheafedSpace)ᵒᵖ) :
    Sheaf (Opens.grothendieckTopology ↑X.toPresheafedSpace) Ab :=
  (yoneda ⋙ (Functor.whiskeringRight _ _ _).obj AddCommGrpCat.free ⋙
    presheafToSheaf _ _).obj U.unop

/--
The cohomology presheaf `U ↦ Hⁿ(U, F)` of a sheaf of modules `F`, as a presheaf of modules
over the global sections of the structure sheaf. The restriction maps act on the first
`Ext`-variable and the module structure on the second, so linearity is the associativity of
the composition product on `Ext`.
-/
noncomputable def cohomologyPresheafOfModules (n : ℕ) :
    (TopologicalSpace.Opens ↑X.toPresheafedSpace)ᵒᵖ ⥤ ModuleCat ↑Γ(X, ⊤) where
  obj U := ModuleCat.of ↑Γ(X, ⊤)
    (Ext (freeAbelianSheaf U) ((SheafOfModules.toSheaf X.ringCatSheaf).obj F) n)
  map {U V} i := ModuleCat.ofHom
    { toFun := ((((SheafOfModules.toSheaf X.ringCatSheaf).obj F).cohomologyPresheaf n).map i).hom
      map_add' := map_add _
      map_smul' := fun r x => by
        change (Ext.mk₀ _).comp (x.comp (Ext.mk₀ (globalSMulEnd F r)) (add_zero n))
            (zero_add n) =
          ((Ext.mk₀ _).comp x (zero_add n)).comp (Ext.mk₀ (globalSMulEnd F r)) (add_zero n)
        rw [Ext.comp_assoc_of_third_deg_zero] }
  map_id U := by
    ext x
    change ((((SheafOfModules.toSheaf X.ringCatSheaf).obj F).cohomologyPresheaf n).map
      (𝟙 U)).hom x = x
    rw [CategoryTheory.Functor.map_id]
    rfl
  map_comp i j := by
    ext x
    change ((((SheafOfModules.toSheaf X.ringCatSheaf).obj F).cohomologyPresheaf n).map
      (i ≫ j)).hom x = _
    rw [CategoryTheory.Functor.map_comp]
    rfl

/-- The sheaf cohomology of a sheaf of modules is a module over global sections, with no
`X.Over (Spec R)` hypothesis. -/
noncomputable example (n : ℕ) :
    Module ↑Γ(X, ⊤) (((SheafOfModules.toSheaf X.ringCatSheaf).obj F).H n) :=
  inferInstance

/-- Forgetting the module structures recovers the cohomology presheaf of the underlying
abelian sheaf. -/
lemma cohomologyPresheafOfModules_comp_forget₂ (n : ℕ) :
    cohomologyPresheafOfModules F n ⋙ forget₂ (ModuleCat ↑Γ(X, ⊤)) Ab =
      ((SheafOfModules.toSheaf X.ringCatSheaf).obj F).cohomologyPresheaf n :=
  rfl

end GlobalSections
