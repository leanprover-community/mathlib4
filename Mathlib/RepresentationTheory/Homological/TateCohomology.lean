import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
import Mathlib.RepresentationTheory.Homological.GroupHomology.Functoriality

universe v u

open CategoryTheory ShortComplex Limits

section

variable {C D : Type*} [Category C] [Abelian C] [Category D] [Abelian D] (F G : C ⥤ D)
  [F.Additive] [G.Additive] [F.PreservesZeroMorphisms] [G.PreservesZeroMorphisms]
  (X : ShortComplex C) (hX : ShortExact X) [PreservesFiniteColimits F] [PreservesFiniteLimits G]
  (T : F ⟶ G)

@[simps]
noncomputable def CategoryTheory.ShortComplex.natTransSnakeInput : SnakeInput D where
  L₀ := kernel (X.mapNatTrans T)
  L₁ := F.mapShortComplex.obj X
  L₂ := G.mapShortComplex.obj X
  L₃ := cokernel (X.mapNatTrans T)
  v₀₁ := kernel.ι (X.mapNatTrans T)
  v₁₂ := X.mapNatTrans T
  v₂₃ := cokernel.π (X.mapNatTrans T)
  w₀₂ := kernel.condition (X.mapNatTrans T)
  w₁₃ := cokernel.condition (X.mapNatTrans T)
  h₀ := kernelIsKernel (X.mapNatTrans T)
  h₃ := cokernelIsCokernel (X.mapNatTrans T)
  L₁_exact := by
    have := (F.preservesFiniteColimits_tfae.out 3 0).1
    apply (this ⟨inferInstance⟩ X hX).1
  epi_L₁_g := by
    have := (F.preservesFiniteColimits_tfae.out 3 0).1
    apply (this ⟨inferInstance⟩ X hX).2
  L₂_exact := by
    have := (G.preservesFiniteLimits_tfae.out 3 0).1
    apply (this ⟨inferInstance⟩ X hX).1
  mono_L₂_f := by
    have := (G.preservesFiniteLimits_tfae.out 3 0).1
    apply (this ⟨inferInstance⟩ X hX).2

end

open Rep

noncomputable def TateCohomology {k G : Type u} [CommRing k] [Group G]
    [Fintype G] [DecidableEq G] (A : Rep k G) (i : ℤ) : ModuleCat k :=
  match i with
  | 0 => ModuleCat.of k (A.ρ.invariants ⧸ (LinearMap.range (liftRestrictNorm A)))
  | (n + 1 : ℕ) => groupCohomology A (n + 1)
  | -1 => ModuleCat.of k (LinearMap.ker (liftRestrictNorm A))
  | -(n + 2 : ℕ) => groupHomology A (n + 1)

namespace TateCohomology

variable {k G : Type u} [CommRing k] [Group G] [Fintype G] [DecidableEq G] (A : Rep k G)
  (X : ShortComplex (Rep k G)) (hX : X.ShortExact)

noncomputable def snakeInput : SnakeInput (ModuleCat k) :=
  X.natTransSnakeInput _ _ hX (liftRestrictNormNatTrans)

noncomputable def snakeInputIso₀₃ :
    (snakeInput X hX).L₀.X₃ ≅ TateCohomology X.X₃ (-1) :=
  let e₁ : (snakeInput X hX).L₀.X₃
      ≅ (limitCone (parallelPair (X.mapNatTrans liftRestrictNormNatTrans) 0)).pt.X₃ :=
    π₃.mapIso <| (Limits.limit.isoLimitCone ⟨limitCone _, isLimitLimitCone _⟩)
  let e₂ : (limitCone (parallelPair (X.mapNatTrans liftRestrictNormNatTrans) 0)).pt.X₃
      ≅ TateCohomology X.X₃ (-1) :=
    (isLimitπ₃MapConeLimitCone _).conePointsIsoOfNatIso (ModuleCat.kernelIsLimit _)
      (diagramIsoParallelPair <| parallelPair _ 0 ⋙ π₃)
  e₁ ≪≫ e₂

@[reassoc (attr := simp)]
theorem snakeInputIso₀₃_inv_comp_map_ι :
    (snakeInputIso₀₃ X hX).inv ≫ π₃.map (kernel.ι _) = Submodule.subtype _ := by
  unfold snakeInputIso₀₃
  simp only [Int.reduceNeg, Functor.comp_obj, parallelPair_obj_zero, parallelPair_obj_one,
    Functor.comp_map, parallelPair_map_left, Iso.trans_inv, IsLimit.conePointsIsoOfNatIso_inv,
    Functor.mapIso_inv, Category.assoc, ← Functor.map_comp, limit.isoLimitCone_inv_π,
    Fork.app_zero_eq_ι]
  exact IsLimit.map_π _ _ _ _

noncomputable def snakeInputIso₃₁ :
    (snakeInput X hX).L₃.X₁ ≅ TateCohomology X.X₁ 0 :=
  let e₁ : (snakeInput X hX).L₃.X₁
      ≅ (colimitCocone (parallelPair (X.mapNatTrans liftRestrictNormNatTrans) 0)).pt.X₁ :=
    π₁.mapIso <| (Limits.colimit.isoColimitCocone ⟨(colimitCocone _), isColimitColimitCocone _⟩)
  let e₂ : (colimitCocone (parallelPair (X.mapNatTrans liftRestrictNormNatTrans) 0)).pt.X₁
      ≅ TateCohomology X.X₁ 0 :=
    (isColimitπ₁MapCoconeColimitCocone _).coconePointsIsoOfNatIso (ModuleCat.cokernelIsColimit _)
      (diagramIsoParallelPair <| parallelPair _ 0 ⋙ π₁)
  e₁ ≪≫ e₂

@[reassoc (attr := simp)]
theorem map_π_comp_snakeInputIso₃₁_hom :
    π₁.map (cokernel.π _) ≫ (snakeInputIso₃₁ X hX).hom = Submodule.mkQ _ := by
  unfold snakeInputIso₃₁
  simp [-π₁_map, - π₁_obj, ← Functor.map_comp, snakeInputIso₃₁,
    ← Category.assoc]
  exact IsColimit.ι_map _ _ _ _

noncomputable def δ : TateCohomology X.X₃ (-1) ⟶ TateCohomology X.X₁ 0 :=
  (snakeInputIso₀₃ X hX).inv ≫ (TateCohomology.snakeInput X hX).δ ≫ (snakeInputIso₃₁ X hX).hom

theorem δ_apply (z : X.X₃) (hz : (Submodule.mkQ _ z) ∈ LinearMap.ker (liftRestrictNorm X.X₃))
    (y : X.X₂) (x : X.X₁.ρ.invariants)
    (hyz : hom X.g y - z ∈ X.X₃.ρ.coinvariantsKer) (hx : hom X.f x.1 = hom X.X₂.norm y) :
    TateCohomology.δ X hX ⟨Submodule.mkQ _ z, hz⟩ = Submodule.mkQ _ x := by
  convert congr((snakeInputIso₃₁ X hX).hom $((TateCohomology.snakeInput X hX).δ_apply
    ((snakeInputIso₀₃ X hX).inv ⟨Submodule.mkQ _ z, hz⟩) (Submodule.mkQ _ y) x
    (((Submodule.Quotient.eq _).2 hyz).trans (congr($(snakeInputIso₀₃_inv_comp_map_ι X hX)
      ⟨Submodule.mkQ _ z, hz⟩)).symm) (Subtype.ext hx)))
  exact congr($((map_π_comp_snakeInputIso₃₁_hom X hX).symm) _)


-- lol
noncomputable def TateCohomology2 [DecidableEq G] (i : ℤ) : ModuleCat k :=
  match i with
  | 0 => ModuleCat.of k (A.ρ.invariants ⧸ (LinearMap.range (liftRestrictNorm A)))
  | 1 => ModuleCat.of k (groupCohomology.H1 A)
  | 2 => ModuleCat.of k (groupCohomology.H2 A)
  | (n + 3 : ℕ) => groupCohomology A (n + 3)
  | -1 => ModuleCat.of k (LinearMap.ker (liftRestrictNorm A))
  | -2 => ModuleCat.of k (groupHomology.H1 A)
  | -3 => ModuleCat.of k (groupHomology.H2 A)
  | -(n + 4 : ℕ) => groupHomology A (n + 3)

end TateCohomology
