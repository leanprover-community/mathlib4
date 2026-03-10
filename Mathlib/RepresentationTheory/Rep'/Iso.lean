module

public import Mathlib.RepresentationTheory.Rep'.Basic
public import Mathlib.Algebra.Category.ModuleCat.Projective

@[expose] public section

universe w w' u u' v v'

namespace Rep

open CategoryTheory

suppress_compilation

attribute [local simp] ModuleCat.MonoidalCategory.tensorObj_carrier

section Group

variable (k G H : Type u) [Group G] [Monoid H] [MulAction G H] [CommRing k] (n : ℕ)

open MonoidalCategory Finsupp ModuleCat.MonoidalCategory Representation.IntertwiningMap

-- set_option allowUnsafeReducibility true in
-- attribute [local irreducible] ofMulAction in
/-- An isomorphism of `k`-linear representations of `G` from `k[Gⁿ⁺¹]` to `k[G] ⊗ₖ k[Gⁿ]` (on
which `G` acts by `ρ(g₁)(g₂ ⊗ x) = (g₁ * g₂) ⊗ x`) sending `(g₀, ..., gₙ)` to
`g₀ ⊗ (g₀⁻¹g₁, g₁⁻¹g₂, ..., gₙ₋₁⁻¹gₙ)`. The inverse sends `g₀ ⊗ (g₁, ..., gₙ)` to
`(g₀, g₀g₁, ..., g₀g₁...gₙ)`. -/
abbrev diagonalSuccIsoTensorTrivial :
    diagonal k G (n + 1) ≅ leftRegular k G ⊗ trivial k G ((Fin n → G) →₀ k) :=
  -- (linearizarionObjOfMulAction k G (Fin (n + 1) → G)).symm ≪≫
  linearizationObjOfMulAction k G (n + 1) ≪≫ (linearization k G).mapIso
    (Action.diagonalSuccIsoTensorTrivial G n) ≪≫
    (Functor.Monoidal.μIso (linearization k G) _ _).symm ≪≫
    tensorIso (linearizationOfMulActionIso k G G) (linearizationTrivialIso k G (Fin n → G)) --≪≫
    --   tensorIso (linearizarionObjOfMulAction k G G) (linearizationTrivialIso k G (Fin n → G))

-- set_option backward.isDefEq.respectTransparency false in
-- theorem diagonalSuccIsoTensorTrivial_inv_hom_single_single (g : G) (f : Fin n → G) (a b : k) :
--     (diagonalSuccIsoTensorTrivial k G n).inv.hom (single g a ⊗ₜ single f b) =
--       single (g • Fin.partialProd f) (a * b) := by
--   have := Action.diagonalSuccIsoTensorTrivial_inv_hom_apply (G := G) (n := n)
--   -- simp [diagonalSuccIsoTensorTrivial, linearizationTrivialIso]
--   sorry
  -- simp_all [diagonalSuccIsoTensorTrivial, ModuleCat.MonoidalCategory.tensorHom_def,
  --   tensorObj_carrier, types_tensorObj_def, ModuleCat.hom_id (M := .of _ _), Action.ofMulAction_V]

-- unif_hint (G : Type*) [Monoid G] where ⊢ G ≟ (Action.leftRegular G).V

-- set_option backward.isDefEq.respectTransparency false in
-- @[simp]
-- theorem diagonalSuccIsoTensorTrivial_hom_hom_single (f : Fin (n + 1) → G) (a : k) :
--     (diagonalSuccIsoTensorTrivial k G n).hom.hom.toLinearMap (ofMulAction.single G f a) =
--       ofMulAction.single G (f 0) 1 ⊗ₜ single (fun i => (f (Fin.castSucc i))⁻¹ * f i.succ) a := by
--   dsimp [diagonalSuccIsoTensorTrivial, Action.ofMulAction_V, -tensor_V, -tensor_ρ]
--   simp only [linearization_map_hom_single, Action.diagonalSuccIsoTensorTrivial_hom_hom_apply,
--     linearization_δ_apply, Action.ofMulAction_V, Action.trivial_V, Action.tensorObj_V,
--     LinearEquiv.coe_coe]
--   have := linearizationObjEquiv_single (k := k)
--     (Action.leftRegular G ⊗ Action.trivial G (Fin n → G))
--     (f 0, fun i ↦ (f i.castSucc)⁻¹ * f i.succ) a
--   dsimp at this
--   simp only [tensor_V, tensorObj_carrier, coe_of, this]
--   rw [finsuppTensorFinsupp'_symm_single_eq_single_one_tmul]
--   simp only [TensorProduct.congr_symm_tmul, (linearizationObjEquiv_symm_single),
--     TensorProduct.map_tmul, toLinearMap_apply, linearizarionObjOfMulAction_single]
--   congr 1

-- example {V : Type*} [AddCommGroup V] [Module k V] (ρ : Representation k G V) :
--     (Rep.of ρ).ρ = ρ := rfl

-- unif_hint {V : Type*} [AddCommGroup V] [Module k V] (ρ : Representation k G V) where ⊢
--     (Rep.of ρ).V ≟ V

-- -- unif_hint {V : Type*} [AddCommGroup V] [Module k V] (ρ : Representation k G V) where ⊢
-- --     (Rep.of ρ).ρ ≟ ρ

-- set_option backward.isDefEq.respectTransparency false in
-- -- set_option pp.all true in
-- -- set_option pp.maxSteps 1000000000 in
-- attribute [local irreducible] linearization ofMulAction in
-- theorem diagonalSuccIsoTensorTrivial_inv_hom_single_single (g : G) (f : Fin n → G) (a b : k) :
--     (diagonalSuccIsoTensorTrivial k G n).inv.hom (ofMulAction.single G g a ⊗ₜ single f b) =
--       ofMulAction.single G (g • Fin.partialProd f) (a * b) := by
--   have := Action.diagonalSuccIsoTensorTrivial_inv_hom_apply (G := G) (n := n)
--   dsimp [diagonalSuccIsoTensorTrivial, Action.tensor_ρ, tensorObj_carrier]
--   have heq := linearization_μ_apply (k := k) (Action.leftRegular G) (Action.trivial G (Fin n → G))
--   dsimp [ModuleCat.MonoidalCategory.tensorObj_carrier] at heq
--   rw [heq]
--   simp only [TensorProduct.map_tmul, LinearEquiv.coe_coe, linearizationObjEquiv_single]
--   rw [linearizationTrivialIso_inv_single]
--   dsimp [Action.trivial]
--   rw [linearizationObjEquiv_single]
--   simp only [finsuppTensorFinsupp'_single_tmul_single]
--   dsimp [Action.leftRegular, Action.ofMulAction, Action.tensorObj_V]
--   -- rw [linearizationObjEquiv_symm_single]
--   -- simp only [TensorProduct.map_tmul, LinearEquiv.coe_coe, linearizationObjEquiv_single]
--   -- conv_lhs => enter [2, 2, 2, 2, 3]; erw [linearizationObjEquiv_single]
--   -- simp only [Action.trivial_V, finsuppTensorFinsupp'_single_tmul_single]
--   erw [linearizationObjEquiv_symm_single, linearization_map_hom_single]
--   rw [this]
--   rfl

-- set_option backward.isDefEq.respectTransparency false in
-- theorem diagonalSuccIsoTensorTrivial_inv_hom_single_left (g : G) (f : (Fin n → G) →₀ k) (r : k) :
--     (diagonalSuccIsoTensorTrivial k G n).inv.hom (ofMulAction.single G g r ⊗ₜ f) =
--       (ofMulAction.equivFinsupp k G (Fin (n + 1) → G)).symm (Finsupp.lift ((Fin (n + 1) → G) →₀ k)
--       k (Fin n → G) (fun f => single (g • Fin.partialProd f) r) f) := by
--   refine f.induction ?_ ?_
--   · simp only [TensorProduct.tmul_zero, map_zero]
--   · intro a b x _ _ hx
--     classical
--     simp only [tensor_V, tensorObj_carrier, coe_of, tensor_ρ, of_ρ, lift_apply, smul_single,
--       smul_eq_mul, TensorProduct.tmul_add, map_add, zero_mul, single_zero, sum_single_index,
--       ofMulAction.equivFinsupp_symm_single] at hx ⊢
--     rw [← hx]
--     simp only [add_left_inj]
--     erw [diagonalSuccIsoTensorTrivial_inv_hom_single_single k G n g a r b]
--     rw [mul_comm]

-- set_option backward.isDefEq.respectTransparency false in
-- theorem diagonalSuccIsoTensorTrivial_inv_hom_single_right (g : G →₀ k) (f : Fin n → G) (r : k) :
--     (diagonalSuccIsoTensorTrivial k G n).inv.hom (g ⊗ₜ single f r) =
--       (ofMulAction.equivFinsupp k G (Fin (n + 1) → G)).symm (Finsupp.lift _ k G (fun a => single
--       (a • Fin.partialProd f) r) g) := by
--   refine g.induction ?_ ?_
--   · simp only [TensorProduct.zero_tmul, map_zero]
--   · intro a b x _ _ hx
--     classical
--     simp only [tensor_V, tensorObj_carrier, coe_of, tensor_ρ, of_ρ, lift_apply, smul_single,
--       smul_eq_mul] at hx ⊢
--     rw [Finsupp.sum_add_index (by simp) (by simp [add_mul])]
--     simp only [TensorProduct.add_tmul, map_add, zero_mul, single_zero, sum_single_index,
--       ofMulAction.equivFinsupp_symm_single, ← hx, add_left_inj]
--     rw [← ofMulAction.single_def]
--     exact diagonalSuccIsoTensorTrivial_inv_hom_single_single k G n ..

/-- Representation isomorphism `k[Gⁿ⁺¹] ≅ (Gⁿ →₀ k[G])`, where the right-hand representation is
defined pointwise by the left regular representation on `k[G]`. The map sends
`single (g₀, ..., gₙ) a ↦ single (g₀⁻¹g₁, ..., gₙ₋₁⁻¹gₙ) (single g₀ a)`. -/
abbrev diagonalSuccIsoFree : diagonal k G (n + 1) ≅ free k G (Fin n → G) :=
  diagonalSuccIsoTensorTrivial k G n ≪≫ leftRegularTensorTrivialIsoFree k G (Fin n → G)

-- set_option backward.isDefEq.respectTransparency false in
-- @[simp]
-- theorem diagonalSuccIsoFree_hom_hom_single (f : Fin (n + 1) → G) (a : k) :
--     (diagonalSuccIsoFree k G n).hom.hom (ofMulAction.single G f a) =
--       free.single _ (fun i => (f i.castSucc)⁻¹ * f i.succ) (single (f 0) a) := by
--   simp only [diagonalSuccIsoFree, Iso.trans_hom, hom_comp, tensor_V, tensorObj_carrier, coe_of,
--     tensor_ρ, of_ρ, Representation.IntertwiningMap.comp_apply]
--   erw [diagonalSuccIsoTensorTrivial_hom_hom_single k G n f a]
--   erw [leftRegularTensorTrivialIsoFree_hom_hom_single_tmul_single k G]
--   rw [one_mul]

-- set_option backward.isDefEq.respectTransparency false in
-- @[simp]
-- theorem diagonalSuccIsoFree_inv_hom_single_single (g : G) (f : Fin n → G) (a : k) :
--     (diagonalSuccIsoFree k G n).inv.hom (free.single _ f (single g a)) =
--       ofMulAction.single G (g • Fin.partialProd f) a := by
--   have := diagonalSuccIsoTensorTrivial_inv_hom_single_single k G n g f a 1
--   simp only [diagonalSuccIsoFree, Iso.trans_inv, hom_comp, tensor_V, tensor_ρ, coe_of, of_ρ,
--     Representation.IntertwiningMap.comp_apply, mul_one] at this ⊢
--   erw [leftRegularTensorTrivialIsoFree_inv_hom_single_single]
--   exact this

-- theorem diagonalSuccIsoFree_inv_hom_single (g : G →₀ k) (f : Fin n → G) :
--     (diagonalSuccIsoFree k G n).inv.hom (free.single _ f g) =
--       (ofMulAction.equivFinsupp k G (Fin (n + 1) → G)).symm (lift _ k G (fun a => single
--       (a • Fin.partialProd f) 1) g) :=
--   g.induction (by simp) fun g1 k1 l1 _ _ hh => by
--     simp only [lift_apply, smul_single, smul_eq_mul, mul_one, map_add,
--       diagonalSuccIsoFree_inv_hom_single_single, single_zero, sum_single_index,
--       ofMulAction.equivFinsupp_symm_single, add_right_inj] at hh ⊢
--     exact hh

variable (A : Rep k G)

/-- Given a `k`-linear `G`-representation `A`, the set of representation morphisms
`Hom(k[Gⁿ⁺¹], A)` is `k`-linearly isomorphic to the set of functions `Gⁿ → A`. -/
abbrev diagonalHomEquiv :
    (Rep.diagonal k G (n + 1) ⟶ A) ≃ₗ[k] (Fin n → G) → A :=
  Linear.homCongr k (diagonalSuccIsoFree k G n) (Iso.refl _) ≪≫ₗ
    freeLiftLEquiv k G (Fin n → G) A

variable {n A}

-- set_option backward.isDefEq.respectTransparency false in
-- /-- Given a `k`-linear `G`-representation `A`, `diagonalHomEquiv` is a `k`-linear isomorphism of
-- the set of representation morphisms `Hom(k[Gⁿ⁺¹], A)` with `Fun(Gⁿ, A)`. This lemma says that this
-- sends a morphism of representations `f : k[Gⁿ⁺¹] ⟶ A` to the function
-- `(g₁, ..., gₙ) ↦ f(1, g₁, g₁g₂, ..., g₁g₂...gₙ).` -/
-- theorem diagonalHomEquiv_apply (f : Rep.diagonal k G (n + 1) ⟶ A) (x : Fin n → G) :
--     diagonalHomEquiv k G n A f x = f.hom (ofMulAction.single G (Fin.partialProd x) 1) := by
--   simp [diagonalHomEquiv, Linear.homCongr_apply,
--     diagonalSuccIsoFree_inv_hom_single_single (k := k)]

-- set_option backward.isDefEq.respectTransparency false in
-- /-- Given a `k`-linear `G`-representation `A`, `diagonalHomEquiv` is a `k`-linear isomorphism of
-- the set of representation morphisms `Hom(k[Gⁿ⁺¹], A)` with `Fun(Gⁿ, A)`. This lemma says that the
-- inverse map sends a function `f : Gⁿ → A` to the representation morphism sending
-- `(g₀, ... gₙ) ↦ ρ(g₀)(f(g₀⁻¹g₁, g₁⁻¹g₂, ..., gₙ₋₁⁻¹gₙ))`, where `ρ` is the representation attached
-- to `A`. -/
-- theorem diagonalHomEquiv_symm_apply (f : (Fin n → G) → A) (x : Fin (n + 1) → G) :
--     ((diagonalHomEquiv k G n A).symm f).hom (ofMulAction.single G x 1) =
--       A.ρ (x 0) (f fun i : Fin n => (x (Fin.castSucc i))⁻¹ * x i.succ) := by
--   simp [diagonalHomEquiv, Linear.homCongr_symm_apply, diagonalSuccIsoFree_hom_hom_single (k := k)]

end Group

/-!
### The categorical equivalence `Rep k G ≌ Module.{u} k[G]`.
-/


variable {k : Type u} {G : Type v} [CommRing k] [Monoid G]

open MonoidAlgebra

/-- Auxiliary lemma for `toModuleMonoidAlgebra`. -/
theorem to_Module_monoidAlgebra_map_aux {k G : Type*} [CommRing k] [Monoid G] (V W : Type*)
    [AddCommGroup V] [AddCommGroup W] [Module k V] [Module k W] (ρ : G →* V →ₗ[k] V)
    (σ : G →* W →ₗ[k] W) (f : V →ₗ[k] W) (w : ∀ g : G, f.comp (ρ g) = (σ g).comp f)
    (r : k[G]) (x : V) :
    f (MonoidAlgebra.lift k (V →ₗ[k] V) G ρ r x) =
      MonoidAlgebra.lift k (W →ₗ[k] W) G σ r (f x) := by
  apply MonoidAlgebra.induction_on r
  · intro g
    simp only [one_smul, MonoidAlgebra.lift_single, MonoidAlgebra.of_apply]
    exact LinearMap.congr_fun (w g) x
  · intro g h gw hw; simp only [map_add, LinearMap.add_apply, hw, gw]
  · intro r g w
    simp only [map_smul, w, LinearMap.smul_apply]

set_option backward.isDefEq.respectTransparency false in
/-- Auxiliary definition for `toModuleMonoidAlgebra`. -/
def toModuleMonoidAlgebraMap {V W : Rep.{w} k G} (f : V ⟶ W) :
    ModuleCat.of k[G] V.ρ.asModule ⟶ ModuleCat.of k[G] W.ρ.asModule :=
  ModuleCat.ofHom
    { f.hom.toLinearMap with
      map_smul' := fun r x => to_Module_monoidAlgebra_map_aux V.V W.V V.ρ W.ρ
        f.hom.toLinearMap f.hom.2 r x }

set_option backward.isDefEq.respectTransparency false in
/-- Functorially convert a representation of `G` into a module over `k[G]`. -/
def toModuleMonoidAlgebra : Rep.{w} k G ⥤ ModuleCat k[G] where
  obj V := ModuleCat.of _ V.ρ.asModule
  map f := toModuleMonoidAlgebraMap f

set_option backward.isDefEq.respectTransparency false in
/-- Functorially convert a module over `k[G]` into a representation of `G`. -/
def ofModuleMonoidAlgebra : ModuleCat k[G] ⥤ Rep.{w} k G where
  obj M := Rep.of (Representation.ofModule M)
  map f := ofHom {
    __ := f.hom
    map_smul' r x := f.hom.map_smul (algebraMap k _ r) x
    isIntertwining' g := by ext; apply f.hom.map_smul
  }

theorem ofModuleMonoidAlgebra_obj_coe (M : ModuleCat.{w} k[G]) :
    ofModuleMonoidAlgebra.obj M = RestrictScalars k k[G] M :=
  rfl

theorem ofModuleMonoidAlgebra_obj_ρ (M : ModuleCat.{w} k[G]) :
    (ofModuleMonoidAlgebra.obj M).ρ = Representation.ofModule M :=
  rfl

/-- Auxiliary definition for `equivalenceModuleMonoidAlgebra`. -/
def counitIsoAddEquiv {M : ModuleCat.{w} k[G]} :
    (ofModuleMonoidAlgebra ⋙ toModuleMonoidAlgebra).obj M ≃+ M := by
  dsimp [ofModuleMonoidAlgebra, toModuleMonoidAlgebra]
  exact (Representation.ofModule M).asModuleEquiv.toAddEquiv.trans
    (RestrictScalars.addEquiv k k[G] _)

/-- Auxiliary definition for `equivalenceModuleMonoidAlgebra`. -/
def unitIsoAddEquiv {V : Rep.{w} k G} : V ≃+ (toModuleMonoidAlgebra ⋙
    ofModuleMonoidAlgebra).obj V := by
  dsimp [ofModuleMonoidAlgebra, toModuleMonoidAlgebra]
  exact V.ρ.asModuleEquiv.symm.toAddEquiv.trans (RestrictScalars.addEquiv _ _ _).symm

set_option backward.isDefEq.respectTransparency false in
/-- Auxiliary definition for `equivalenceModuleMonoidAlgebra`. -/
def counitIso (M : ModuleCat.{w} k[G]) :
    (ofModuleMonoidAlgebra ⋙ toModuleMonoidAlgebra).obj M ≅ M :=
  LinearEquiv.toModuleIso
    { counitIsoAddEquiv with
      map_smul' := fun r x => by
        dsimp [counitIsoAddEquiv]
        simp }

set_option backward.isDefEq.respectTransparency false in
theorem unit_iso_comm (V : Rep.{w} k G) (g : G) (x : V) :
    unitIsoAddEquiv ((V.ρ g).toFun x) = ((ofModuleMonoidAlgebra.obj
      (toModuleMonoidAlgebra.obj V)).ρ g).toFun (unitIsoAddEquiv x) := by
  simp [unitIsoAddEquiv, ofModuleMonoidAlgebra, toModuleMonoidAlgebra]

set_option backward.isDefEq.respectTransparency false in
/-- Auxiliary definition for `equivalenceModuleMonoidAlgebra`. -/
def unitIso (V : Rep.{w} k G) : V ≅ (toModuleMonoidAlgebra ⋙ ofModuleMonoidAlgebra).obj V :=
  mkIso <| .mk
  { unitIsoAddEquiv (k := k) (G := G) with
    map_smul' r x := show (RestrictScalars.addEquiv _ _ _).symm
      (V.ρ.asModuleEquiv.symm (r • x)) = _ by
      simp only [Representation.asModuleEquiv_symm_map_smul]
      rfl } fun g ↦ by ext; apply unit_iso_comm

/-- The categorical equivalence `Rep k G ≌ ModuleCat k[G]`. -/
def equivalenceModuleMonoidAlgebra : Rep.{w} k G ≌ ModuleCat k[G] where
  functor := toModuleMonoidAlgebra
  inverse := ofModuleMonoidAlgebra
  unitIso := NatIso.ofComponents (fun V => unitIso V) (by cat_disch)
  counitIso := NatIso.ofComponents (fun M => counitIso M) (by cat_disch)

instance : (toModuleMonoidAlgebra.{w} (k := k) (G := G)).IsEquivalence :=
  (equivalenceModuleMonoidAlgebra (k := k) (G := G)).isEquivalence_functor

instance : (ofModuleMonoidAlgebra (k := k) (G := G)).IsEquivalence :=
  (equivalenceModuleMonoidAlgebra (k := k) (G := G)).isEquivalence_inverse

open MonoidalCategory in
instance : Limits.HasBinaryBiproducts (Rep.{w} k G) where
  has_binary_biproduct A B := Limits.hasBinaryBiproduct_of_total
    ⟨Rep.of (X := A.V × B.V) (Representation.prod A.ρ B.ρ), Rep.ofHom ⟨LinearMap.fst k _ _, by
      simp [LinearMap.ext_iff]⟩, Rep.ofHom ⟨LinearMap.snd k _ _, by simp [LinearMap.ext_iff]⟩,
      Rep.ofHom ⟨LinearMap.inl _ _ _, by simp [LinearMap.ext_iff]⟩, Rep.ofHom ⟨LinearMap.inr _ _ _,
      by simp [LinearMap.ext_iff]⟩, by ext : 2; simp, by ext : 2; simp [zero_hom], by
      ext : 2; simp [zero_hom], by ext : 2; simp⟩ <| by
    ext : 2; simp [← ofHom_comp, ← ofHom_add, LinearMap.ext_iff]

instance : Limits.HasZeroObject (Rep.{w} k G) where
  zero := ⟨Rep.trivial k G PUnit, {
    unique_to X := Nonempty.intro ⟨⟨0⟩, fun f ↦ by
      ext x; have : x = 0 := Subsingleton.elim _ _; subst this; simp⟩
    unique_from X := Nonempty.intro ⟨⟨0⟩, fun f ↦ by ext⟩
  }⟩

instance : Limits.HasFiniteProducts (Rep.{w} k G) := hasFiniteProducts_of_has_binary_and_terminal

instance : Abelian (Rep.{w} k G) := abelianOfEquivalence toModuleMonoidAlgebra

-- TODO Verify that the equivalence with `ModuleCat k[G]` is a monoidal functor.

variable {k G : Type u} [CommRing k] [Monoid G] in
instance : CategoryTheory.EnoughProjectives (Rep.{max w u} k G) :=
  equivalenceModuleMonoidAlgebra.enoughProjectives_iff.2 ModuleCat.enoughProjectives.{max w u}

set_option backward.isDefEq.respectTransparency false in
instance free_projective {α : Type (max w u)} :
    Projective (free k G α) :=
  equivalenceModuleMonoidAlgebra.toAdjunction.projective_of_map_projective _ <|
    @ModuleCat.projective_of_free _ _
      (ModuleCat.of k[G] (Representation.free k G α).asModule)
      _ (Representation.freeAsModuleBasis k G α)

section

variable {G : Type u} [Group G] {n : ℕ}

instance diagonal_succ_projective :
    Projective (diagonal k G (n + 1)) := by
  classical
  exact Projective.of_iso (diagonalSuccIsoFree k G n).symm inferInstance

instance leftRegular_projective :
    Projective (leftRegular k G) :=
  Projective.of_iso (diagonalOneIsoLeftRegular k G) inferInstance

instance trivial_projective_of_subsingleton [Subsingleton G] :
    Projective (trivial k G k) :=
  Projective.of_iso (ofMulActionSubsingletonIsoTrivial _ _ (Fin 1 → G)) diagonal_succ_projective

end

end Rep
