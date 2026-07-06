import Mathlib.Algebra.Category.Grp.Zero
import Mathlib.Topology.Sheaves.Skyscraper
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.AlgebraicGeometry.Modules.Presheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.AlgebraicGeometry.AlgebraicCycle.CohmologyModule
import Mathlib.Topology.Sheaves.Flasque
import Mathlib.CategoryTheory.Sites.Point.Skyscraper
import Mathlib.Topology.Sheaves.Points

open AlgebraicGeometry Opposite CategoryTheory Limits

/-!
# The skyscraper sheaf of modules at a point of a topos

Given a point `Φ` of a site `(C, J)` and a sheaf of rings `R`, we upgrade the skyscraper sheaf
`Φ.skyscraperSheaf` (`Mathlib.CategoryTheory.Sites.Point.Skyscraper`) to a sheaf of modules
over `R`: sections of `R` act on the products `∏_{x : Φ.fiber X} M` componentwise through
their germs. This requires no case distinction on whether fibers are empty (unlike the
classical construction over a topological space, which splits on `p ∈ U`).

* `skyscraperSheafOfModulesFunctor`: the functor from modules over the fiber of `R` at `Φ`
  to sheaves of modules over `R`.
* `skyscraperSheafOfModules_eq_skyscraperSheaf`: its underlying abelian sheaf is the
  skyscraper sheaf, definitionally.

We then specialize to a point `p` of a topological space via
`Opens.pointGrothendieckTopology p` (whose fibers are subsingletons), giving
`skyscraperSheafOfModules p R M` for a module `M` over the stalk `R.presheaf.stalk p`, and
we prove that its underlying abelian sheaf is flasque, so its positive-degree cohomology on a
scheme vanishes (`subsingleton_H_skyscraper`).
-/

@[expose] public section


section topos

namespace CategoryTheory.GrothendieckTopology.Point

universe w v u

open Limits

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} (Φ : Point.{w} J)

section Presheaf

set_option backward.isDefEq.respectTransparency false

variable (R : Cᵒᵖ ⥤ RingCat.{w}) (M : ModuleCat.{w} ↑(Φ.presheafFiber.obj R))

/--
The action of a section `r : R.obj X` on the component at `x : Φ.fiber.obj X.unop` of the
skyscraper presheaf: the action of the germ of `r` at `x` on `M`.
-/
noncomputable def skyscraperSMulComponent (X : Cᵒᵖ) (r : ↑(R.obj X)) (x : Φ.fiber.obj X.unop) :
    AddCommGrpCat.of (↑M : Type w) ⟶ AddCommGrpCat.of (↑M : Type w) :=
  AddCommGrpCat.ofHom
    (AddMonoidHom.mk' (fun m => (Φ.toPresheafFiber X.unop x R).hom r • m)
      (fun m n => smul_add _ m n))

@[simp]
lemma skyscraperSMulComponent_apply (X : Cᵒᵖ) (r : ↑(R.obj X)) (x : Φ.fiber.obj X.unop)
    (m : AddCommGrpCat.of (↑M : Type w)) :
    (skyscraperSMulComponent Φ R M X r x).hom m =
      (Φ.toPresheafFiber X.unop x R).hom r • m :=
  rfl

lemma skyscraperSMulComponent_one (X : Cᵒᵖ) (x : Φ.fiber.obj X.unop) :
    skyscraperSMulComponent Φ R M X (1 : ↑(R.obj X)) x = 𝟙 _ := by
  refine AddCommGrpCat.hom_ext (AddMonoidHom.ext fun m => ?_)
  change (Φ.toPresheafFiber X.unop x R).hom 1 • m = m
  rw [map_one, one_smul]

lemma skyscraperSMulComponent_mul (X : Cᵒᵖ) (r s : ↑(R.obj X)) (x : Φ.fiber.obj X.unop) :
    skyscraperSMulComponent Φ R M X (r * s) x =
      skyscraperSMulComponent Φ R M X s x ≫ skyscraperSMulComponent Φ R M X r x := by
  refine AddCommGrpCat.hom_ext (AddMonoidHom.ext fun m => ?_)
  change (Φ.toPresheafFiber X.unop x R).hom (r * s) • m =
    (Φ.toPresheafFiber X.unop x R).hom r • ((Φ.toPresheafFiber X.unop x R).hom s • m)
  rw [map_mul, mul_smul]

lemma skyscraperSMulComponent_add (X : Cᵒᵖ) (r s : ↑(R.obj X)) (x : Φ.fiber.obj X.unop) :
    skyscraperSMulComponent Φ R M X (r + s) x =
      skyscraperSMulComponent Φ R M X r x + skyscraperSMulComponent Φ R M X s x := by
  refine AddCommGrpCat.hom_ext (AddMonoidHom.ext fun m => ?_)
  change (Φ.toPresheafFiber X.unop x R).hom (r + s) • m =
    (Φ.toPresheafFiber X.unop x R).hom r • m + (Φ.toPresheafFiber X.unop x R).hom s • m
  rw [map_add, add_smul]

lemma skyscraperSMulComponent_zero (X : Cᵒᵖ) (x : Φ.fiber.obj X.unop) :
    skyscraperSMulComponent Φ R M X (0 : ↑(R.obj X)) x = 0 := by
  refine AddCommGrpCat.hom_ext (AddMonoidHom.ext fun m => ?_)
  change (Φ.toPresheafFiber X.unop x R).hom 0 • m = 0
  rw [map_zero, zero_smul]

/-- The germ of a section is unchanged by restriction, so the componentwise actions on the
skyscraper presheaf are compatible with its restriction maps. -/
lemma skyscraperSMulComponent_naturality {X Y : Cᵒᵖ} (f : X ⟶ Y) (r : ↑(R.obj X))
    (y : Φ.fiber.obj Y.unop) :
    skyscraperSMulComponent Φ R M X r (Φ.fiber.map f.unop y) =
      skyscraperSMulComponent Φ R M Y ((R.map f).hom r) y := by
  have h0 := congrArg RingCat.Hom.hom (toPresheafFiber_w Φ f.unop y R)
  rw [RingCat.hom_comp] at h0
  have h : (Φ.toPresheafFiber X.unop (Φ.fiber.map f.unop y) R).hom r =
      (Φ.toPresheafFiber Y.unop y R).hom ((R.map f).hom r) :=
    (DFunLike.congr_fun h0 r).symm
  simp only [skyscraperSMulComponent, h]

/--
The scalar action of a section `r : R.obj X` on the value `∏_{x : Φ.fiber.obj X.unop} M` of
the skyscraper presheaf: on the component at `x`, it is the action of the germ of `r` at `x`.
-/
noncomputable def skyscraperSMul (X : Cᵒᵖ) (r : ↑(R.obj X)) :
    (Φ.skyscraperPresheaf (AddCommGrpCat.of (↑M : Type w))).obj X ⟶
      (Φ.skyscraperPresheaf (AddCommGrpCat.of (↑M : Type w))).obj X :=
  Limits.Pi.map fun x => skyscraperSMulComponent Φ R M X r x

@[reassoc (attr := simp)]
lemma skyscraperSMul_π (X : Cᵒᵖ) (r : ↑(R.obj X)) (x : Φ.fiber.obj X.unop) :
    skyscraperSMul Φ R M X r ≫ Limits.Pi.π _ x =
      Limits.Pi.π _ x ≫ skyscraperSMulComponent Φ R M X r x :=
  Limits.Pi.map_π _ x

lemma skyscraperSMul_one (X : Cᵒᵖ) :
    skyscraperSMul Φ R M X (1 : ↑(R.obj X)) = 𝟙 _ := by
  unfold skyscraperSMul
  simp only [skyscraperSMulComponent_one]
  exact Limits.Pi.map_id

lemma skyscraperSMul_mul (X : Cᵒᵖ) (r s : ↑(R.obj X)) :
    skyscraperSMul Φ R M X (r * s) =
      skyscraperSMul Φ R M X s ≫ skyscraperSMul Φ R M X r := by
  unfold skyscraperSMul
  rw [Limits.Pi.map_comp_map]
  simp only [skyscraperSMulComponent_mul]

lemma skyscraperSMul_add (X : Cᵒᵖ) (r s : ↑(R.obj X)) :
    skyscraperSMul Φ R M X (r + s) =
      skyscraperSMul Φ R M X r + skyscraperSMul Φ R M X s := by
  refine Limits.Pi.hom_ext _ _ fun x => ?_
  simp only [skyscraperSMul, Limits.Pi.map_π, skyscraperSMulComponent_add,
    Preadditive.add_comp, Preadditive.comp_add]

lemma skyscraperSMul_zero (X : Cᵒᵖ) :
    skyscraperSMul Φ R M X (0 : ↑(R.obj X)) = 0 := by
  refine Limits.Pi.hom_ext _ _ fun x => ?_
  simp only [skyscraperSMul, Limits.Pi.map_π, skyscraperSMulComponent_zero,
    Limits.comp_zero, Limits.zero_comp]

/--
The module structure on the value at `X` of the skyscraper presheaf associated to a module `M`
over the fiber of `R`: sections act componentwise through their germs. Note that this requires
no case distinction on whether the fiber at `X` is empty (where the empty product is zero).
-/
noncomputable instance skyscraperPresheafObjModule (X : Cᵒᵖ) :
    Module ↑(R.obj X)
      ↑((Φ.skyscraperPresheaf (AddCommGrpCat.of (↑M : Type w))).obj X) where
  smul r m := (skyscraperSMul Φ R M X r).hom m
  one_smul m := by
    change (skyscraperSMul Φ R M X 1).hom m = m
    rw [skyscraperSMul_one]
    rfl
  mul_smul r s m := by
    change (skyscraperSMul Φ R M X (r * s)).hom m =
      (skyscraperSMul Φ R M X r).hom ((skyscraperSMul Φ R M X s).hom m)
    rw [skyscraperSMul_mul]
    rfl
  smul_zero r := map_zero (skyscraperSMul Φ R M X r).hom
  smul_add r m n := map_add (skyscraperSMul Φ R M X r).hom m n
  add_smul r s m := by
    change (skyscraperSMul Φ R M X (r + s)).hom m =
      (skyscraperSMul Φ R M X r).hom m + (skyscraperSMul Φ R M X s).hom m
    rw [skyscraperSMul_add]
    rfl
  zero_smul m := by
    change (skyscraperSMul Φ R M X 0).hom m = 0
    rw [skyscraperSMul_zero]
    rfl

/-- The restriction maps of the skyscraper presheaf reindex the product along the fiber maps. -/
@[reassoc (attr := simp)]
lemma skyscraperPresheaf_map_π {A : Type*} [Category* A] [HasProducts.{w} A] (N : A)
    {X Y : Cᵒᵖ} (f : X ⟶ Y) (y : Φ.fiber.obj Y.unop) :
    (Φ.skyscraperPresheaf N).map f ≫ Limits.Pi.π _ y =
      Limits.Pi.π _ (Φ.fiber.map f.unop y) := by
  have h : (Φ.skyscraperPresheaf N).map f =
      Limits.Pi.map' (Φ.fiber.map f.unop) (fun _ => 𝟙 N) := rfl
  rw [h, Limits.Pi.map'_comp_π, Category.comp_id]

/-- The scalar action on the skyscraper presheaf is semilinear with respect to restriction. -/
lemma skyscraperSMul_naturality {X Y : Cᵒᵖ} (f : X ⟶ Y) (r : ↑(R.obj X)) :
    skyscraperSMul Φ R M X r ≫
        (Φ.skyscraperPresheaf (AddCommGrpCat.of (↑M : Type w))).map f =
      (Φ.skyscraperPresheaf (AddCommGrpCat.of (↑M : Type w))).map f ≫
        skyscraperSMul Φ R M Y ((R.map f).hom r) := by
  have hmap : (Φ.skyscraperPresheaf (AddCommGrpCat.of (↑M : Type w))).map f =
      Limits.Pi.map' (Φ.fiber.map f.unop) (fun _ => 𝟙 _) := rfl
  rw [hmap]
  unfold skyscraperSMul
  rw [Limits.Pi.map_comp_map', Limits.Pi.map'_comp_map]
  simp only [Category.comp_id, Category.id_comp, skyscraperSMulComponent_naturality]

/--
The skyscraper presheaf of modules at a point `Φ` of a site, valued in a module `M` over the
fiber of the presheaf of rings `R`: the underlying abelian presheaf is the skyscraper presheaf
`Φ.skyscraperPresheaf M`, and sections of `R` act componentwise through their germs.
-/
noncomputable def skyscraperPresheafOfModules : PresheafOfModules.{w} R :=
  PresheafOfModules.ofPresheaf
    (Φ.skyscraperPresheaf (AddCommGrpCat.of (↑M : Type w)))
    (fun _ _ f r m => CategoryTheory.congr_fun (skyscraperSMul_naturality Φ R M f r) m)

@[simp]
lemma skyscraperPresheafOfModules_presheaf :
    (skyscraperPresheafOfModules Φ R M).presheaf =
      Φ.skyscraperPresheaf (AddCommGrpCat.of (↑M : Type w)) :=
  rfl

variable {M} in
/-- The componentwise actions commute with the morphism of skyscraper presheaves induced by a
morphism of modules over the fiber. -/
lemma skyscraperSMulComponent_comm {N : ModuleCat.{w} ↑(Φ.presheafFiber.obj R)} (φ : M ⟶ N)
    (X : Cᵒᵖ) (r : ↑(R.obj X)) (x : Φ.fiber.obj X.unop) :
    skyscraperSMulComponent Φ R M X r x ≫ AddCommGrpCat.ofHom φ.hom.toAddMonoidHom =
      AddCommGrpCat.ofHom φ.hom.toAddMonoidHom ≫ skyscraperSMulComponent Φ R N X r x := by
  refine AddCommGrpCat.hom_ext (AddMonoidHom.ext fun m => ?_)
  change φ.hom ((Φ.toPresheafFiber X.unop x R).hom r • m) =
    (Φ.toPresheafFiber X.unop x R).hom r • φ.hom m
  rw [map_smul]

variable {M} in
/-- Morphisms of modules over the fiber induce componentwise `R`-linear morphisms of
skyscraper presheaves. -/
lemma skyscraperSMul_naturality₂ {N : ModuleCat.{w} ↑(Φ.presheafFiber.obj R)} (φ : M ⟶ N)
    (X : Cᵒᵖ) (r : ↑(R.obj X)) :
    skyscraperSMul Φ R M X r ≫
        (Φ.skyscraperPresheafFunctor.map
          (AddCommGrpCat.ofHom φ.hom.toAddMonoidHom :
            AddCommGrpCat.of (↑M : Type w) ⟶ AddCommGrpCat.of (↑N : Type w))).app X =
      (Φ.skyscraperPresheafFunctor.map
          (AddCommGrpCat.ofHom φ.hom.toAddMonoidHom :
            AddCommGrpCat.of (↑M : Type w) ⟶ AddCommGrpCat.of (↑N : Type w))).app X ≫
        skyscraperSMul Φ R N X r := by
  have happ : ∀ (P Q : Ab) (ψ : P ⟶ Q) (Z : Cᵒᵖ),
      (Φ.skyscraperPresheafFunctor.map ψ).app Z = Limits.Pi.map (fun _ => ψ) :=
    fun _ _ _ _ => rfl
  rw [happ]
  unfold skyscraperSMul
  rw [Limits.Pi.map_comp_map, Limits.Pi.map_comp_map]
  simp only [skyscraperSMulComponent_comm]

/--
The skyscraper presheaf-of-modules functor at a point `Φ` of a site: it sends a module over
the fiber of `R` to the associated skyscraper presheaf of modules.
-/
noncomputable def skyscraperPresheafOfModulesFunctor :
    ModuleCat.{w} ↑(Φ.presheafFiber.obj R) ⥤ PresheafOfModules.{w} R where
  obj M := skyscraperPresheafOfModules Φ R M
  map {M N} φ := PresheafOfModules.homMk
    (Φ.skyscraperPresheafFunctor.map
      (AddCommGrpCat.ofHom φ.hom.toAddMonoidHom :
        AddCommGrpCat.of (↑M : Type w) ⟶ AddCommGrpCat.of (↑N : Type w)))
    (fun X r m => CategoryTheory.congr_fun (skyscraperSMul_naturality₂ Φ R φ X r) m)
  map_id M := by
    apply (PresheafOfModules.toPresheaf R).map_injective
    ext X m
    change ((Φ.skyscraperPresheafFunctor.map
        (AddCommGrpCat.ofHom ((ModuleCat.Hom.hom (𝟙 M)).toAddMonoidHom) :
          AddCommGrpCat.of (↑M : Type w) ⟶ AddCommGrpCat.of (↑M : Type w))).app X).hom m = m
    rw [show (AddCommGrpCat.ofHom ((ModuleCat.Hom.hom (𝟙 M)).toAddMonoidHom) :
        AddCommGrpCat.of (↑M : Type w) ⟶ AddCommGrpCat.of (↑M : Type w)) = 𝟙 _ from rfl,
      Functor.map_id]
    rfl
  map_comp {M N P} φ ψ := by
    apply (PresheafOfModules.toPresheaf R).map_injective
    ext X m
    change ((Φ.skyscraperPresheafFunctor.map
        (AddCommGrpCat.ofHom ((ModuleCat.Hom.hom (φ ≫ ψ)).toAddMonoidHom) :
          AddCommGrpCat.of (↑M : Type w) ⟶ AddCommGrpCat.of (↑P : Type w))).app X).hom m = _
    rw [show (AddCommGrpCat.ofHom ((ModuleCat.Hom.hom (φ ≫ ψ)).toAddMonoidHom) :
        AddCommGrpCat.of (↑M : Type w) ⟶ AddCommGrpCat.of (↑P : Type w)) =
        (AddCommGrpCat.ofHom ((ModuleCat.Hom.hom φ).toAddMonoidHom) :
          AddCommGrpCat.of (↑M : Type w) ⟶ AddCommGrpCat.of (↑N : Type w)) ≫
        (AddCommGrpCat.ofHom ((ModuleCat.Hom.hom ψ).toAddMonoidHom) :
          AddCommGrpCat.of (↑N : Type w) ⟶ AddCommGrpCat.of (↑P : Type w)) from rfl,
      Functor.map_comp]
    rfl

end Presheaf

section Sheaf

variable (R : Sheaf J RingCat.{w})

/--
The skyscraper sheaf-of-modules functor at a point `Φ` of a site: it sends a module over the
fiber of the sheaf of rings `R` to the associated skyscraper sheaf of modules. The underlying
abelian sheaf is the skyscraper sheaf `Φ.skyscraperSheaf`
(see `skyscraperSheafOfModules_eq_skyscraperSheaf`).
-/
noncomputable def skyscraperSheafOfModulesFunctor :
    ModuleCat.{w} ((Point.sheafFiber Φ).obj R).carrier ⥤ SheafOfModules.{w} R where
  obj M := ⟨(skyscraperPresheafOfModulesFunctor Φ R.obj).obj M,
    Φ.isSheaf_skyscraperPresheaf _⟩
  map φ := ⟨(skyscraperPresheafOfModulesFunctor Φ R.obj).map φ⟩
  map_id M := by
    ext1
    exact (skyscraperPresheafOfModulesFunctor Φ R.obj).map_id M
  map_comp φ ψ := by
    ext1
    exact (skyscraperPresheafOfModulesFunctor Φ R.obj).map_comp φ ψ

/--
The underlying sheaf of abelian groups of the skyscraper sheaf of modules is the
skyscraper sheaf.
-/
lemma skyscraperSheafOfModules_eq_skyscraperSheaf :
    (skyscraperSheafOfModulesFunctor Φ R) ⋙ SheafOfModules.toSheaf R =
    forget₂ (ModuleCat ((Point.sheafFiber Φ).obj R).carrier) Ab ⋙
    Φ.skyscraperSheafFunctor := rfl

end Sheaf

end CategoryTheory.GrothendieckTopology.Point
end topos

/-!
## Specialization to topological spaces and schemes

A point `p` of a topological space gives a point `Opens.pointGrothendieckTopology p` of the
site of opens, whose fibers are subsingletons (`p ∈ U` or not). We specialize the skyscraper
sheaf of modules to this situation: the module is transported along the canonical comparison
map from the site-theoretic fiber of the sheaf of rings to its topological stalk, and
flasqueness of the underlying abelian sheaf is immediate from the subsingleton fibers.
-/

section TopCatPoint

set_option backward.isDefEq.respectTransparency false

open CategoryTheory.GrothendieckTopology

universe u

variable {Y : TopCat.{u}} (p : ↑Y)

/--
The skyscraper sheaf at a point of a topological space is flasque: a restriction map is a
reindexing of a product over subsingleton fibers, hence split epi when `p` belongs to the
smaller open, and a map to a zero object otherwise.
-/
instance skyscraperSheaf_isFlasque (A : Ab.{u}) :
    TopCat.Presheaf.IsFlasque
      ((Opens.pointGrothendieckTopology p).skyscraperSheaf A).obj where
  epi {U V} i := by
    have hmap : ((Opens.pointGrothendieckTopology p).skyscraperPresheaf A).map i =
        Limits.Pi.map' ((Opens.pointGrothendieckTopology p).fiber.map i.unop)
          (fun _ => 𝟙 A) := rfl
    by_cases hp : p ∈ V.unop
    · -- A section is given by reindexing back through the (subsingleton) fibers.
      refine CategoryTheory.SplitEpi.epi
        ⟨Limits.Pi.map' (fun _ => ⟨⟨hp⟩⟩) (fun _ => 𝟙 A), ?_⟩
      change Limits.Pi.map' _ _ ≫
        ((Opens.pointGrothendieckTopology p).skyscraperPresheaf A).map i = 𝟙 _
      rw [hmap, Limits.Pi.map'_comp_map']
      refine (Limits.Pi.map'_eq (funext fun x =>
        Subsingleton.elim (α := (Opens.pointGrothendieckTopology p).fiber.obj V.unop) _ _)
        ?_).trans Limits.Pi.map'_id_id
      intro b
      simp
    · -- The target is a product over an empty fiber, hence a zero object.
      have hterm : Limits.IsTerminal
          (((Opens.pointGrothendieckTopology p).skyscraperPresheaf A).obj V) :=
        Limits.IsTerminal.ofUniqueHom
          (fun Z => Limits.Pi.lift (fun x => absurd x.down.down hp))
          (fun Z m => Limits.Pi.hom_ext _ _ (fun x => absurd x.down.down hp))
      have hzero : Limits.IsZero
          (((Opens.pointGrothendieckTopology p).skyscraperPresheaf A).obj V) :=
        (Limits.isZero_zero _).of_iso (hterm.uniqueUpToIso (Limits.isZero_zero _).isTerminal)
      constructor
      intro Z g h _
      exact hzero.eq_of_src g h

variable (R : TopCat.Sheaf RingCat.{u} Y)

/--
The canonical comparison map from the site-theoretic fiber of a presheaf of rings at
`Opens.pointGrothendieckTopology p` to its topological stalk at `p`, induced by the germ maps.
(It is in fact an isomorphism, but we only need the morphism here.)
-/
noncomputable def pointPresheafFiberToStalk :
    (Opens.pointGrothendieckTopology p).presheafFiber.obj R.presheaf ⟶ R.presheaf.stalk p :=
  (Opens.pointGrothendieckTopology p).presheafFiberDesc
    (fun U x => R.presheaf.germ U p x.down.down)
    (by intro U V f x; exact R.presheaf.germ_res f p x.down.down)

@[reassoc (attr := simp)]
lemma toPresheafFiber_pointPresheafFiberToStalk (U : TopologicalSpace.Opens ↑Y) (hp : p ∈ U) :
    (Opens.pointGrothendieckTopology p).toPresheafFiber U ⟨⟨hp⟩⟩ R.presheaf ≫
      pointPresheafFiberToStalk p R = R.presheaf.germ U p hp :=
  (Opens.pointGrothendieckTopology p).toPresheafFiber_presheafFiberDesc _ _ U ⟨⟨hp⟩⟩

variable (M : Type u) [AddCommGroup M] [Module ↑(R.presheaf.stalk p) M]

/--
A module over the topological stalk of `R` at `p` is a module over the site-theoretic fiber,
via the canonical comparison map.
-/
noncomputable instance pointSheafFiberModule :
    Module ↑((Opens.pointGrothendieckTopology p).sheafFiber.obj R) M :=
  Module.compHom M (pointPresheafFiberToStalk p R).hom

/--
The skyscraper sheaf of modules at a point `p` of a topological space, valued in a module `M`
over the stalk at `p` of the sheaf of rings `R`: the specialization of the site-theoretic
`skyscraperSheafOfModulesFunctor` to the point `Opens.pointGrothendieckTopology p`.
-/
noncomputable def skyscraperSheafOfModules : SheafOfModules.{u} R :=
  ((Opens.pointGrothendieckTopology p).skyscraperSheafOfModulesFunctor R).obj
    (ModuleCat.of _ M)

/-- The underlying abelian sheaf of the skyscraper sheaf of modules is the skyscraper sheaf. -/
lemma toSheaf_obj_skyscraperSheafOfModules :
    (SheafOfModules.toSheaf _).obj (skyscraperSheafOfModules p R M) =
      (Opens.pointGrothendieckTopology p).skyscraperSheaf (AddCommGrpCat.of M) :=
  rfl

/-- The underlying abelian sheaf of the skyscraper sheaf of modules is flasque. -/
instance : TopCat.Sheaf.IsFlasque
    ((SheafOfModules.toSheaf _).obj (skyscraperSheafOfModules p R M)) :=
  inferInstanceAs (TopCat.Presheaf.IsFlasque
    ((Opens.pointGrothendieckTopology p).skyscraperSheaf (AddCommGrpCat.of M)).obj)

end TopCatPoint

section Scheme

universe u

variable {X : Scheme.{u}} (p : X)

/--
The residue field at `p` is a module over the `RingCat`-valued stalk of the structure sheaf,
via the canonical comparison map to the `CommRingCat`-valued stalk followed by the residue map.
-/
noncomputable instance : Module ↑(X.ringCatSheaf.presheaf.stalk p) ↑(X.residueField p) :=
  Module.compHom _ (RingCat.Hom.hom
    (colimit.post ((TopologicalSpace.OpenNhds.inclusion p).op ⋙ X.presheaf)
        (forget₂ CommRingCat RingCat) ≫
      (forget₂ CommRingCat RingCat).map (X.residue p)))

open TopologicalSpace in
/--
Germ-compatibility for the module structure above: acting on the residue field by a section
through its `RingCat`-valued germ is multiplication by the evaluation of the section at `p`.

TODO: Move this somewhere sensible
-/
lemma residueField_compHom_smul_eq {U : X.Opens} (hp' : p ∈ U)
    (a : ↑(X.ringCatSheaf.presheaf.obj (op U))) (m : ↑(X.residueField p)) :
    letI : Module ↑(X.ringCatSheaf.presheaf.obj (op U)) ↑(X.residueField p) :=
      Module.compHom ↑(X.residueField p) (X.ringCatSheaf.presheaf.germ U p hp').hom
    a • m = (X.evaluation U p hp').hom a * m := by
  -- The comparison map `colimit.post` intertwines the `RingCat`- and `CommRingCat`-germs.
  have hpost : (RingCat.Hom.hom (colimit.post ((OpenNhds.inclusion p).op ⋙ X.presheaf)
      (forget₂ CommRingCat RingCat))) ((X.ringCatSheaf.presheaf.germ U p hp').hom a) =
      (X.presheaf.germ U p hp').hom a := by
    have h := colimit.ι_post ((OpenNhds.inclusion p).op ⋙ X.presheaf)
      (forget₂ CommRingCat RingCat) (op ⟨U, hp'⟩)
    exact congrArg (fun f => (RingCat.Hom.hom f) a) h
  change (X.residue p).hom ((RingCat.Hom.hom (colimit.post ((OpenNhds.inclusion p).op ⋙ X.presheaf)
      (forget₂ CommRingCat RingCat))) ((X.ringCatSheaf.presheaf.germ U p hp').hom a)) * m =
    (X.evaluation U p hp').hom a * m
  rw [hpost]
  rfl

/--
The germ action of `Γ(X, U)` on the stalk at `p ∈ U` and the residue action of the stalk on the
residue field form a scalar tower over the evaluation action of `Γ(X, U)` on the residue field,
since `residue ∘ germ = evaluation`.
-/
lemma isScalarTower_evaluation {U : X.Opens} (hp' : p ∈ U) :
    letI : Module ↑Γ(X, U) ↑(X.presheaf.stalk p) := (X.presheaf.germ U p hp').hom.toModule
    letI : Module ↑(X.presheaf.stalk p) ↑(X.residueField p) := (X.residue p).hom.toModule
    letI : Module ↑Γ(X, U) ↑(X.residueField p) := (X.evaluation U p hp').hom.toModule
    IsScalarTower ↑Γ(X, U) ↑(X.presheaf.stalk p) ↑(X.residueField p) := by
  letI : Module ↑Γ(X, U) ↑(X.presheaf.stalk p) := (X.presheaf.germ U p hp').hom.toModule
  letI : Module ↑(X.presheaf.stalk p) ↑(X.residueField p) := (X.residue p).hom.toModule
  letI : Module ↑Γ(X, U) ↑(X.residueField p) := (X.evaluation U p hp').hom.toModule
  constructor
  intro r s t
  change (X.residue p).hom ((X.presheaf.germ U p hp').hom r * s) * t =
    (X.evaluation U p hp').hom r * ((X.residue p).hom s * t)
  rw [map_mul, mul_assoc]
  rfl

/-- Positive-degree cohomology of the (flasque) skyscraper sheaf at `p` is subsingleton. -/
lemma subsingleton_H_skyscraper (n : ℕ) :
    Subsingleton (Scheme.Modules.H
      (skyscraperSheafOfModules p X.ringCatSheaf ↑(X.residueField p)) (n + 1)) :=
  inferInstanceAs (Subsingleton (((SheafOfModules.toSheaf X.ringCatSheaf).obj
    (skyscraperSheafOfModules p X.ringCatSheaf ↑(X.residueField p))).H (n + 1)))

/-- Positive-degree cohomology of the (flasque) skyscraper sheaf at `p` is subsingleton. -/
lemma subsingleton_H_skyscraper_of_pos {n : ℕ} (hn : 0 < n) :
    Subsingleton (Scheme.Modules.H
      (skyscraperSheafOfModules p X.ringCatSheaf ↑(X.residueField p)) n) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  exact subsingleton_H_skyscraper p m

end Scheme
