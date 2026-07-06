import Mathlib.AlgebraicGeometry.AlgebraicCycle.Sheaf

open AlgebraicGeometry CategoryTheory

universe u

variable {X : Scheme.{u}} (F : X.Modules)

/-- The stalk of the structure sheaf acts on the stalk of any sheaf of modules. -/
noncomputable
instance (x : X) : Module (X.presheaf.stalk x) ↑(TopCat.Presheaf.stalk F.val.presheaf x) :=
  PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier F.val x

noncomputable
def l (U : TopologicalSpace.Opens ↑X) (x : ↑X) (hx : x ∈ U) :
    Module Γ(X, U) ↑(TopCat.Presheaf.stalk F.val.presheaf x) :=
  Module.compHom ↑(TopCat.Presheaf.stalk F.val.presheaf x) (X.ringCatSheaf.presheaf.germ U x hx).hom

noncomputable
def germModuleHom (U : TopologicalSpace.Opens ↑X) (x : ↑X) (hx : x ∈ U) :
    letI := l F U x hx
    Γ(F, U) →ₗ[Γ(X, U)] ↑(TopCat.Presheaf.stalk F.val.presheaf x) :=
  letI := l F U x hx
  {
    __ := (TopCat.Presheaf.germ F.val.presheaf U x hx).hom
    map_smul' := PresheafOfModules.germ_ringCat_smul F.val x U hx
  }

/--
The `Γ(X, U)`-action `l` on the stalk of `F` at `x ∈ U` is given by acting through the germ in
the structure-sheaf stalk: `r • m = germ r • m`.
-/
lemma l_smul_eq_germ_smul (U : TopologicalSpace.Opens ↑X) (x : ↑X) (hx : x ∈ U)
    (r : ↑Γ(X, U)) (m : ↑(TopCat.Presheaf.stalk F.val.presheaf x)) :
    letI := l F U x hx
    r • m = (X.presheaf.germ U x hx r : ↑(X.presheaf.stalk x)) • m := by
  letI := l F U x hx
  obtain ⟨W, hxW, m', rfl⟩ := TopCat.Presheaf.exists_germ_eq F.val.presheaf m
  have hxΩ : x ∈ U ⊓ W := ⟨hx, hxW⟩
  change TopCat.Presheaf.germ X.ringCatSheaf.presheaf U x hx r •
    TopCat.Presheaf.germ F.val.presheaf W x hxW m' = _
  rw [← TopCat.Presheaf.germ_res_apply F.val.presheaf
      (homOfLE (inf_le_right : U ⊓ W ≤ W)) x hxΩ m',
    ← TopCat.Presheaf.germ_res_apply X.ringCatSheaf.presheaf
      (homOfLE (inf_le_left : U ⊓ W ≤ U)) x hxΩ r,
    ← TopCat.Presheaf.germ_res_apply X.presheaf
      (homOfLE (inf_le_left : U ⊓ W ≤ U)) x hxΩ r,
    ← PresheafOfModules.germ_ringCat_smul (M := F.val) x (U ⊓ W) hxΩ]
  exact PresheafOfModules.germ_smul (R := X.presheaf) (M := F.val) x (U ⊓ W) hxΩ _ _

/--
The `Γ(X, U)`-action `l` on the stalk of `F` at `x ∈ U` forms a scalar tower with the germ
action of `Γ(X, U)` on the structure-sheaf stalk.
-/
lemma isScalarTower_l (U : TopologicalSpace.Opens ↑X) (x : ↑X) (hx : x ∈ U) :
    letI := l F U x hx
    letI : Module ↑Γ(X, U) ↑(X.presheaf.stalk x) := (X.presheaf.germ U x hx).hom.toModule
    IsScalarTower ↑Γ(X, U) ↑(X.presheaf.stalk x) ↑(TopCat.Presheaf.stalk F.val.presheaf x) := by
  letI := l F U x hx
  letI : Module ↑Γ(X, U) ↑(X.presheaf.stalk x) := (X.presheaf.germ U x hx).hom.toModule
  constructor
  intro r s m
  rw [l_smul_eq_germ_smul F U x hx r (s • m)]
  change ((X.presheaf.germ U x hx r : ↑(X.presheaf.stalk x)) * s) • m = _
  rw [mul_smul]

/--
`𝒪ₓ,ₓ`-linear maps out of the stalk of `F` at `x ∈ U` are `Γ(X, U)`-linear for the germ
actions (`l` on the source and `(germ).toModule` on the target).
-/
lemma compatibleSMul_l (U : TopologicalSpace.Opens ↑X) (x : ↑X) (hx : x ∈ U) :
    letI := l F U x hx
    letI : Module ↑Γ(X, U) ↑(X.presheaf.stalk x) := (X.presheaf.germ U x hx).hom.toModule
    LinearMap.CompatibleSMul ↑(TopCat.Presheaf.stalk F.val.presheaf x) ↑(X.presheaf.stalk x)
      ↑Γ(X, U) ↑(X.presheaf.stalk x) := by
  letI := l F U x hx
  letI : Module ↑Γ(X, U) ↑(X.presheaf.stalk x) := (X.presheaf.germ U x hx).hom.toModule
  constructor
  intro f r m
  rw [l_smul_eq_germ_smul F U x hx r m, map_smul]
  rfl
