module

public import Mathlib.RepresentationTheory.Intertwining
public import Mathlib.CategoryTheory.Action.Monoidal

universe w w' u u' v v'
@[expose] public section
namespace Representation

open Representation.IntertwiningMap Representation.TensorProduct

noncomputable section

variable {k : Type u} {G : Type v} {V : Type u'} {W : Type v'} [Monoid G] [Semiring k]
  [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
  {σ : Representation k G V} {ρ : Representation k G W}

open CategoryTheory

variable (k G) in
@[simps]
def linearize (X : Action (Type w) G) : Representation k G (X.V →₀ k) where
  toFun g := Finsupp.lmapDomain k k (X.ρ g)
  map_one' := by ext; simp
  map_mul' _ _ := by ext; simp

lemma linearize_single (X : Action (Type w) G) (g : G) (x : X.V) :
    linearize k G X g (Finsupp.single x 1) = Finsupp.single (X.ρ g x) 1 := by
  simp

def linearizeMap {X Y : Action (Type w) G} (f : X ⟶ Y) : IntertwiningMap (linearize k G X)
    (linearize k G Y) where
  __ := Finsupp.lmapDomain k k f.hom
  isIntertwining' g := by ext x y; simp [(congr($(f.comm g) x) : f.hom (X.ρ g x) = Y.ρ g (f.hom x))]

@[simp]
lemma linearizeMap_single {X Y : Action (Type w) G} (f : X ⟶ Y) (x : X.V) :
    linearizeMap f (Finsupp.single x (1 : k)) = Finsupp.single (f.hom x) 1 := by
  simp [linearizeMap]

lemma linearizeMap_toLinearMap {X Y : Action (Type w) G} (f : X ⟶ Y) :
    (linearizeMap f).toLinearMap = Finsupp.lmapDomain k k f.hom := rfl

namespace LinearizeMonoidal

#check Finsupp.LinearEquiv.finsuppUnique --TODO: change this to the root namespace

variable (k G) in
-- I could use `Action.trivial G (PUnit)` but that's not reducibly equal to the tensor unit
def ε : (trivial k G k).IntertwiningMap (linearize k G (MonoidalCategoryStruct.tensorUnit
    (Action (Type w) G))) where
  __ := Finsupp.LinearEquiv.finsuppUnique k k PUnit|>.symm.toLinearMap
  isIntertwining' g := by
    ext1
    simp only [LinearMap.comp_apply, trivial_apply, linearize_apply]
    simp [types_tensorUnit_def]

lemma ε_one : ε k G 1 = Finsupp.single PUnit.unit 1 := by simp [ε]

open scoped MonoidalCategory

variable (k G) in
def η : (linearize k G (𝟙_ (Action (Type u) G))).IntertwiningMap (trivial k G k) where
  __ := (Finsupp.LinearEquiv.finsuppUnique k k PUnit).toLinearMap
  isIntertwining' g := by
    ext (p : PUnit) : 2
    simp [types_tensorUnit_def, linearize]

lemma η_single (x : PUnit) : η k G (Finsupp.single x 1) = 1 := by simp [η]

variable (k G) in
lemma ε_η : (ε k G).comp (η k G) = .id _ := by ext; simp [ε, η]

variable (k G) in
lemma η_ε : (η k G).comp (ε k G) = .id _ := by ext; simp [ε, η]

section comm

open scoped MonoidalCategory

variable {k : Type u} [CommSemiring k] [Module k V] [Module k W] {σ : Representation k G V}
  {ρ : Representation k G W}

def μ (X Y : Action (Type w) G) : ((linearize k G X).tprod (linearize k G Y)).IntertwiningMap
    (linearize k G (X ⊗ Y)) where
  __ := finsuppTensorFinsupp' k X.V Y.V
  -- ≪≫ₗ
  --   Finsupp.mapDomain.linearEquiv k k (Equiv.cast (Action.tensorObj_V X Y).symm)
  isIntertwining' g := by ext : 5; simp [(linearize_single)]

-- @[simp]
lemma μ_apply_single_single {X Y : Action (Type w) G} (x : X.V) (y : Y.V) :
    μ (k := k) X Y (Finsupp.single x 1 ⊗ₜ Finsupp.single y 1) = Finsupp.single (x, y) 1 := by
  simp [μ]

open TensorProduct in
lemma μ_apply_apply {X Y : Action (Type w) G} (l1 : X.V →₀ k) (l2 : Y.V →₀ k)
    (xy : (X ⊗ Y).V) : μ X Y (l1 ⊗ₜ l2) xy = l1 xy.1 * l2 xy.2 := by
  simp [μ, finsuppTensorFinsupp'_apply_apply k]

lemma μ_comp_rTensor {X Y : Action (Type w) G} (f : X ⟶ Y)
    (Z : Action (Type w) G) : (μ Y Z).comp (rTensor (linearize k G Z) (linearizeMap f)) =
    (linearizeMap (f ▷ Z)).comp (μ X Z) := by
  ext x z
  simp [μ_apply_single_single (f.hom x), μ_apply_single_single x, linearizeMap_single (f ▷ Z)]

lemma μ_comp_lTensor {X Y : Action (Type w) G} (f : X ⟶ Y)
    (Z : Action (Type w) G) : (μ Z Y).comp ((linearizeMap f).lTensor (linearize k G Z)) =
    (linearizeMap (Z ◁ f)).comp (μ Z X) := by
  ext x z : 6
  simp [μ_apply_single_single x, linearizeMap_single (Z ◁ f)]

lemma μ_comp_assoc (X Y Z : Action (Type w) G) : ((linearizeMap (α_ X Y Z).hom).comp
    (μ (X ⊗ Y) Z)).comp ((μ X Y).rTensor (linearize k G Z)) = ((μ X (Y ⊗ Z)).comp
    ((μ Y Z).lTensor (linearize k G X))).comp (assoc (linearize k G X) (linearize k G Y)
    (linearize k G Z)).toIntertwiningMap := by
  ext; simp [(μ_apply_single_single), (linearizeMap_single)]

lemma μ_leftUnitor (X : Action (Type w) G) : (lid k (linearize k G X)).toIntertwiningMap =
    ((linearizeMap (λ_ X).hom).comp (μ (𝟙_ (Action (Type w) G)) X)).comp (rTensor
    (linearize k G X) (ε k G)) := by
  ext x : 5
  simp [ε_one (k := k), μ_apply_single_single _ x, linearizeMap_single _]

lemma μ_rightUnitor (X : Action (Type w) G) : (rid k (linearize k G X)).toIntertwiningMap =
    ((linearizeMap (ρ_ X).hom).comp (μ X (𝟙_ (Action (Type w) G)))).comp ((ε k G).lTensor
    (linearize k G X)) := by
  ext x : 5
  simp [ε_one (k := k), μ_apply_single_single x _, linearizeMap_single _]

def δ (X Y : Action (Type w) G) : (linearize k G (X ⊗ Y)).IntertwiningMap
    ((linearize k G X).tprod (linearize k G Y)) where
  __ := (finsuppTensorFinsupp' k X.V Y.V).symm
  isIntertwining' g := by
    ext; simp [linearize_single _, finsuppTensorFinsupp'_symm_single_eq_single_one_tmul k]

lemma δ_apply_single {X Y : Action (Type w) G} (xy : (X ⊗ Y).V) :
    δ (k := k) X Y (Finsupp.single xy 1) = Finsupp.single xy.1 1 ⊗ₜ Finsupp.single xy.2 1 := by
  simp [δ, finsuppTensorFinsupp'_symm_single_eq_single_one_tmul k]

lemma rTensor_comp_δ {X Y : Action (Type w) G} (f : X ⟶ Y) (Z : Action (Type w) G) :
    ((linearizeMap f).rTensor (linearize k G Z)).comp (δ X Z) =
      (δ Y Z).comp (linearizeMap (f ▷ Z)) := by
  ext; simp [linearizeMap_single _, δ_apply_single _]

lemma lTensor_comp_δ {X Y : Action (Type w) G} (f : X ⟶ Y) (Z : Action (Type w) G) :
    ((linearizeMap f).lTensor (linearize k G Z)).comp (δ Z X) =
      (δ Z Y).comp (linearizeMap (Z ◁ f)) := by
  ext; simp [linearizeMap_single _, δ_apply_single _]

lemma assoc_comp_δ (X Y Z : Action (Type w) G) : ((assoc (linearize k G X) (linearize k G Y)
    (linearize k G Z)).toIntertwiningMap.comp ((δ X Y).rTensor (linearize k G Z))).comp
    (δ (X ⊗ Y) Z) = (((δ Y Z).lTensor (linearize k G X)).comp (δ X (Y ⊗ Z))).comp
    (linearizeMap (α_ X Y Z).hom) := by
  ext; simp [δ_apply_single _, linearizeMap_single _]

lemma leftUnitor_δ (X : Action (Type u) G) : (lid k (linearize k G X)).symm.toIntertwiningMap =
    (((η k G).rTensor (linearize k G X) ).comp (δ (𝟙_ (Action (Type u) G)) X)).comp
      (linearizeMap (λ_ X).inv) := by
  ext; simp [linearizeMap_single _, δ_apply_single _, η_single _]

lemma rightUnitor_δ (X : Action (Type u) G) : (rid k (linearize k G X)).symm.toIntertwiningMap =
    (((η k G).lTensor (linearize k G X)).comp (δ X (𝟙_ (Action (Type u) G)))).comp
      (linearizeMap (ρ_ X).inv) := by
  ext; simp [linearizeMap_single _, δ_apply_single _, η_single _]

lemma μ_δ (X Y : Action (Type w) G) : (μ X Y).comp (δ (k := k) X Y) = .id _ := by
  ext; simp [δ, μ]

lemma δ_μ (X Y : Action (Type w) G) : (δ X Y).comp (μ (k := k) X Y) = .id _ := by
  ext; simp [δ, μ]

end comm

end LinearizeMonoidal

variable (k G) in
def diagonalOneEquivLeftRegular : (diagonal k G 1).Equiv (leftRegular k G) :=
  .mk' (Finsupp.domLCongr (Equiv.funUnique (Fin 1) G)) fun g ↦ by ext; simp

def ofMulActionSubsingletonEquivTrivial (k : Type u) (G : Type v) [Monoid G] [Semiring k]
    (H : Type w) [Subsingleton H] [MulOneClass H]
    [MulAction G H] : (ofMulAction k G H).Equiv (trivial k G k) :=
  letI : Unique H := uniqueOfSubsingleton 1
  .mk' (Finsupp.LinearEquiv.finsuppUnique _ _ _) fun g ↦ by
    ext a; simp [Subsingleton.elim (g • a) a]

lemma linearizeTrivial_def (X : Type w) (g : G) :
    linearize k G (Action.trivial _ X) g = LinearMap.id := by
  ext (x : X) : 2
  rw [LinearMap.comp_apply, LinearMap.id_comp, Finsupp.lsingle_apply, linearize_single]
  simp only [Action.trivial_V, Action.trivial_ρ]
  rfl

variable (k G) in
def linearizeTrivialIso (X : Type w) : (linearize k G (Action.trivial _ X)).Equiv
    (trivial k G (X →₀ k)) :=
  .mk' (LinearEquiv.refl _ _) fun g ↦ by
    simpa using linearizeTrivial_def (k := k) X g

@[simp]
lemma linearizeTrivialIso_single {X : Type w} (x : X) (r : k) :
    (linearizeTrivialIso k G X) (Finsupp.single x r) = Finsupp.single x r := rfl

@[simp]
lemma linearizeTrivialIso_symm_single {X : Type w} (x : X) (r : k) :
    (linearizeTrivialIso k G X).symm (Finsupp.single x r) = Finsupp.single x r := rfl

-- set_option backward.isDefEq.respectTransparency false in
variable (k G) in
def linearizeOfMulActionIso (H : Type w) [MulAction G H] :
    (linearize k G (Action.ofMulAction G H)).Equiv (ofMulAction k G H) :=
    .mk' (LinearEquiv.refl _ _) fun g ↦ by rfl

variable (k G) in
set_option backward.isDefEq.respectTransparency false in
def linearizeDiagonalEquiv (n : ℕ) : (linearize k G (Action.diagonal G n)).Equiv
    (diagonal k G n) :=
  .mk' (LinearEquiv.refl _ _) fun g ↦ by
    ext l : 2
    simp only [LinearEquiv.refl_toLinearMap, linearize_apply, LinearMap.id_comp, LinearMap.coe_comp,
      Function.comp_apply, Finsupp.lsingle_apply, LinearMap.comp_id]
    rfl

section comm

variable {k : Type u} [CommSemiring k] [Module k V] [Module k W] (σ : Representation k G V)
  (ρ : Representation k G W)

section finsupp

open Finsupp

@[simps!]
def freeLift {α : Type w'} (f : α → V) : (free k G α).IntertwiningMap σ where
  __ := linearCombination k (fun x => σ x.2 (f x.1)) ∘ₗ
    (curryLinearEquiv k).symm.toLinearMap
  isIntertwining' g := by ext; simp

@[simps]
def freeLiftLEquiv (α : Type w') : ((free k G α).IntertwiningMap σ) ≃ₗ[k] (α → V) where
  toFun f i := f (single i (single 1 1))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun := freeLift σ
  left_inv f := by
    have := f.2
    simp only [LinearMap.ext_iff, LinearMap.coe_comp, Function.comp_apply,
      toLinearMap_apply] at this
    ext; simp [← this]
  right_inv f := by simp

def finsuppTensorLeft (α : Type w') [DecidableEq α] :
    ((σ.finsupp α).tprod ρ).Equiv ((σ.tprod ρ).finsupp α) :=
  .mk' (TensorProduct.finsuppLeft _ _ _ _ _) fun g ↦ by
    ext; simp [TensorProduct.finsuppLeft_apply_tmul]

def finsuppTensorRight (α : Type w') [DecidableEq α] :
    (σ.tprod (ρ.finsupp α)).Equiv ((σ.tprod ρ).finsupp α) :=
  .mk' (TensorProduct.finsuppRight _ _ _ _ _) fun g ↦ by
    ext; simp [TensorProduct.finsuppRight_apply_tmul]

def leftRegularTensorTrivialIsoFree (α : Type w') :
    ((leftRegular k G).tprod (trivial k G (α →₀ k))).Equiv (free k G α) :=
  .mk' (finsuppTensorFinsupp' k G α ≪≫ₗ Finsupp.domLCongr (Equiv.prodComm G α) ≪≫ₗ
    curryLinearEquiv k) <| fun g ↦ by ext; simp

end finsupp

@[simps!]
def leftRegularMapEquiv : ((leftRegular k G).IntertwiningMap σ) ≃ₗ[k] V where
  toFun f := f (.single 1 1)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun v := ⟨Finsupp.lift _ _ _ (fun g ↦ σ g v), fun g ↦ by ext g'; simp⟩
  left_inv x := by
    ext g
    have := by simpa using LinearMap.ext_iff.1 (x.2 g)
    simp [← this]
  right_inv v:= by simp

lemma leftRegularMapEquiv_symm_single (g : G) (v : V) :
    ((leftRegularMapEquiv σ).symm v) (Finsupp.single g 1) = σ g v := by
  simp

end comm

end

end Representation
