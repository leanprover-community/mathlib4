import Mathlib.CategoryTheory.Bicategory.Functor.Pseudofunctor
import Mathlib.CategoryTheory.Bicategory.LocallyDiscrete
import Mathlib.CategoryTheory.Category.Cat
import Mathlib.CategoryTheory.Sites.Grothendieck
import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.CategoryTheory.Sites.Over

noncomputable section

universe v u v₁ u₁ v₂

open CategoryTheory Opposite Bicategory
open CategoryTheory.Limits LocallyDiscrete


variable {C : Type u} [Category.{v} C]

namespace CategoryTheory

namespace Presieve

variable {X : C}

class HasTriplewisePullbacks (R : Presieve X) extends HasPairwisePullbacks R where
  -- has_pairwise_pullbacks : ∀ {Y Z} {f : Y ⟶ X} (_ : R f) {g : Z ⟶ X} (_ : R g), HasPullback f g
  has_triplewise_pullbacks :
    ∀ {X₁ X₂ X₃} {f₁ : X₁ ⟶ X} (_ : R f₁) {f₂ : X₂ ⟶ X} (_ : R f₂) {f₃ : X₃ ⟶ X} (_ : R f₃)
    [HasPullback f₁ f₂] [HasPullback f₂ f₃], HasPullback (pullback.snd f₁ f₂) (pullback.fst f₂ f₃)

instance (R : Presieve X) [HasPullbacks C] : R.HasTriplewisePullbacks := ⟨inferInstance⟩

instance {α : Type v₂} {X : α → C} {B : C} (π : (a : α) → X a ⟶ B)
    [(Presieve.ofArrows X π).HasTriplewisePullbacks] (a b c : α) :
    HasPullback (pullback.snd (π a) (π b)) (pullback.fst (π b) (π c)) :=
  Presieve.HasTriplewisePullbacks.has_triplewise_pullbacks
    (Presieve.ofArrows.mk _) (Presieve.ofArrows.mk _) (Presieve.ofArrows.mk _)

end Presieve

namespace TriplePullback

variable {U V₁ V₂ V₃ : C}

abbrev triplePullback (f₁ : V₁ ⟶ U) (f₂ : V₂ ⟶ U) (f₃ : V₃ ⟶ U)
    [HasPullback f₁ f₂] [HasPullback f₂ f₃]
    [HasPullback (pullback.snd f₁ f₂) (pullback.fst f₂ f₃)] : C :=
  pullback (pullback.snd f₁ f₂) (pullback.fst f₂ f₃)

inductive Direction | left | middle | right

inductive DirectionPair
  | left_middle : DirectionPair
  | middle_right : DirectionPair
  | left_right : DirectionPair
  deriving Inhabited

instance : OfNat Direction 0 := ⟨Direction.left⟩
instance : OfNat Direction 1 := ⟨Direction.middle⟩
instance : OfNat Direction 2 := ⟨Direction.right⟩

instance : Coe (ℕ × ℕ) DirectionPair where
  coe d :=
    match d with
    | (0, 1) => DirectionPair.left_middle
    | (1, 2) => DirectionPair.middle_right
    | (0, 2) => DirectionPair.left_right
    | _ => Inhabited.default

@[simp]
def DirectionPair.fst : DirectionPair → Direction
  | DirectionPair.left_middle => 0
  | DirectionPair.middle_right => 1
  | DirectionPair.left_right => 0

@[simp]
def DirectionPair.snd : DirectionPair → Direction
  | DirectionPair.left_middle => 1
  | DirectionPair.middle_right => 2
  | DirectionPair.left_right => 2

variable {V : Direction → C} (f : (i : Direction) → V i ⟶ U)
variable {HasPullback : ∀ i j : Direction, HasPullback (f i) (f j)}
variable [(Presieve.ofArrows V f).HasTriplewisePullbacks]

def pr (p : DirectionPair) : triplePullback (f 0) (f 1) (f 2) ⟶ pullback (f p.fst) (f p.snd)  :=
  match p with
  | .left_middle => pullback.fst (pullback.snd (f 0) (f 1)) (pullback.fst (f 1) (f 2))
  | .middle_right => pullback.snd (pullback.snd (f 0) (f 1)) (pullback.fst (f 1) (f 2))
  | .left_right =>
    pullback.lift
      (pullback.fst (pullback.snd (f 0) (f 1)) (pullback.fst (f 1) (f 2)) ≫
        pullback.fst (f 0) (f 1))
      (pullback.snd (pullback.snd (f 0) (f 1)) (pullback.fst (f 1) (f 2)) ≫
        pullback.snd (f 1) (f 2)) <| by
        dsimp only [DirectionPair.fst, DirectionPair.snd]
        rw [Category.assoc, pullback.condition, ← Category.assoc, pullback.condition,
          Category.assoc, pullback.condition, Category.assoc]

def prToSingle (i : Direction) :
    triplePullback (f 0) (f 1) (f 2) ⟶ V i :=
  match i with
  | 0 => pr f .left_middle ≫ pullback.fst (f 0) (f 1)
  | 1 => pr f .left_middle ≫ pullback.snd (f 0) (f 1)
  | 2 => pr f .middle_right ≫ pullback.snd (f 1) (f 2)

variable {U : C} {I : Type v₂} {V : I → C} (f : (i : I) → V i ⟶ U)
variable [(Presieve.ofArrows V f).HasTriplewisePullbacks]

def pr₀₁₂_₀₁ (i j k : I) :
    triplePullback (f i) (f j) (f k) ⟶ pullback (f i) (f j) :=
  pullback.fst (pullback.snd (f i) (f j)) (pullback.fst (f j) (f k))

def pr₀₁₂_₁₂ (i j k : I) :
    triplePullback (f i) (f j) (f k) ⟶ pullback (f j) (f k) :=
  pullback.snd (pullback.snd (f i) (f j)) (pullback.fst (f j) (f k))

def pr₀₁₂_₀₂ (i j k : I) :
    triplePullback (f i) (f j) (f k) ⟶ pullback (f i) (f k) :=
  pullback.lift (pr₀₁₂_₀₁ f i j k ≫ pullback.fst (f i) (f j))
    (pr₀₁₂_₁₂ f i j k ≫ pullback.snd (f j) (f k)) <| by
      dsimp only [pr₀₁₂_₀₁, pr₀₁₂_₁₂]
      rw [Category.assoc, pullback.condition, ← Category.assoc, pullback.condition,
        Category.assoc, pullback.condition, Category.assoc]

abbrev pr₀₁_₀ (i j : I) :
    pullback (f i) (f j) ⟶ V i :=
  pullback.fst (f i) (f j)

abbrev pr₀₁_₁ (i j : I) :
    pullback (f i) (f j) ⟶ V j :=
  pullback.snd (f i) (f j)

abbrev pr₁₂_₁ (j k : I) :
    pullback (f j) (f k) ⟶ V j :=
  pullback.fst (f j) (f k)

abbrev pr₁₂_₂ (j k : I) :
    pullback (f j) (f k) ⟶ V k :=
  pullback.snd (f j) (f k)

abbrev pr₀₂_₀ (i k : I) :
    pullback (f i) (f k) ⟶ V i :=
  pullback.fst (f i) (f k)

abbrev pr₀₂_₂ (i k : I) :
    pullback (f i) (f k) ⟶ V k :=
  pullback.snd (f i) (f k)

-- theorem pullback_condition₀ (i j k : I) :
--     pr₀₁₂_₀₁ f i j k ≫ pr₀₁_₀ f i j = pr₀₁₂_₀₂ f i j k ≫ pr₀₂_₀ f i k := by
--   simp only [limit.lift_π, PullbackCone.mk_pt, PullbackCone.mk_π_app, pr₀₁₂_₀₁, pr₀₁₂_₀₂]

-- theorem pullback_condition₁ (i j k : I) :
--     pr₀₁₂_₀₁ f i j k ≫ pr₀₁_₁ f i j = pr₀₁₂_₁₂ f i j k ≫ pr₁₂_₁ f j k :=
--   pullback.condition

-- theorem pullback_condition₂ (i j k : I) :
--     pr₀₁₂_₀₂ f i j k ≫ pr₀₂_₂ f i k = pr₀₁₂_₁₂ f i j k ≫ pr₁₂_₂ f j k := by
--   simp only [limit.lift_π, PullbackCone.mk_pt, PullbackCone.mk_π_app, pr₀₁₂_₀₂, pr₀₁₂_₀₂, pr₀₁₂_₁₂]

def pr₀₁₂_₀ (i j k : I) : triplePullback (f i) (f j) (f k) ⟶ V i :=
  pr₀₁₂_₀₁ f i j k ≫ pr₀₁_₀ f i j

theorem pr₀₁₂_₀_def₀₁ {i j k : I} :
    pr₀₁₂_₀ f i j k = pr₀₁₂_₀₁ f i j k ≫ pr₀₁_₀ f i j :=
  rfl

theorem pr₀₁₂_₀_def₀₂ {i j k : I} :
    pr₀₁₂_₀ f i j k = pr₀₁₂_₀₂ f i j k ≫ pr₀₂_₀ f i k := by
  simp only [pr₀₁₂_₀_def₀₁, pr₀₁₂_₀₁, pr₀₁₂_₀₂, limit.lift_π, PullbackCone.mk_pt,
    PullbackCone.mk_π_app]

def pr₀₁₂_₁ (i j k : I) : triplePullback (f i) (f j) (f k) ⟶ V j :=
  pr₀₁₂_₀₁ f i j k ≫ pr₀₁_₁ f i j

theorem pr₀₁₂_₁_def₀₁ {i j k : I} :
    pr₀₁₂_₁ f i j k = pr₀₁₂_₀₁ f i j k ≫ pr₀₁_₁ f i j :=
  rfl

theorem pr₀₁₂_₁_def₁₂ {i j k : I} :
    pr₀₁₂_₁ f i j k = pr₀₁₂_₁₂ f i j k ≫ pr₁₂_₁ f j k :=
  pullback.condition

def pr₀₁₂_₂ (i j k : I) : triplePullback (f i) (f j) (f k) ⟶ V k :=
  pr₀₁₂_₁₂ f i j k ≫ pr₁₂_₂ f j k

theorem pr₀₁₂_₂_def₁₂ {i j k : I} :
    pr₀₁₂_₂ f i j k = pr₀₁₂_₁₂ f i j k ≫ pr₁₂_₂ f j k :=
  rfl

theorem pr₀₁₂_₂_def₀₂ {i j k : I} :
    pr₀₁₂_₂ f i j k = pr₀₁₂_₀₂ f i j k ≫ pr₀₂_₂ f i k := by
  simp only [pr₀₁₂_₂_def₁₂, pr₀₁₂_₁₂, pr₀₁₂_₀₂, limit.lift_π, PullbackCone.mk_pt,
    PullbackCone.mk_π_app]

end TriplePullback

namespace Pseudofunctor

open TriplePullback

-- set_option pp.universes true

def mkCat (S : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v₁, u₁}) (X : C) : Cat :=
  S.obj ⟨op X⟩

-- def mkFunctor (S : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v₁, u₁}) {X Y : C} (f : Y ⟶ X) :
--     S.mkCat X ⟶ S.mkCat Y :=
--   S.map ⟨op f⟩

-- def mkCat' (S : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v₁, u₁}) (X : C) : Type u₁ :=
--   S.obj ⟨op X⟩

abbrev mkFunctor (S : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v₁, u₁}) {X Y : C} (f : Y ⟶ X) :
    S.mkCat X ⟶ S.mkCat Y :=
  S.map (LocallyDiscrete.mkHom (op f))

-- @[to_app?]
-- @[simps!?]
abbrev mapCompObj (S : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v₁, u₁}) {X Y Z : C}
    (f : Y ⟶ X) (g : Z ⟶ Y) {x : S.mkCat X} :
    (S.mkFunctor (g ≫ f)).obj x ≅ (S.mkFunctor g).obj ((S.mkFunctor f).obj x) :=
  (S.mapComp (mkHom (op f)) (mkHom (op g))).app x

structure PreDescentData (S : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v₁, u₁})
    (U : C) {I : Type v₂} {V : I → C} (f : (i : I) → V i ⟶ U)
    [(Presieve.ofArrows V f).HasTriplewisePullbacks] where
  /-- An object `Xᵢ` of `S Vᵢ` for each `i : I`. -/
  X : ∀ i, S.obj ⟨op (V i)⟩
  /-- An isomorphism `φᵢⱼ : pr₀* Xᵢ ≅ pr₁* Xⱼ` for each `i j : I`. -/
  φ : ∀ i j : I,
    (S.mkFunctor (pullback.fst (f i) (f j))).obj (X i) ≅
      (S.mkFunctor (pullback.snd (f i) (f j))).obj (X j)

namespace PreDescentData

variable {S : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v₁, u₁}}
    {U : C} {I : Type v₂} {V : I → C} {f : (i : I) → V i ⟶ U}
    [(Presieve.ofArrows V f).HasTriplewisePullbacks]

@[simp]
def objAtDirection (V : I → C) (i j k : I) : Direction → C
  | 0 => V i
  | 1 => V j
  | 2 => V k

@[simp]
def morAtDirection (f : (i : I) → V i ⟶ U) (i j k : I) : (d : Direction) → objAtDirection V i j k d ⟶ U
  | 0 => f i
  | 1 => f j
  | 2 => f k

instance {i j k : I} :
    (Presieve.ofArrows (objAtDirection V i j k) (morAtDirection f i j k)).HasTriplewisePullbacks :=
  sorry

instance {ι : Direction → I} :
  (Presieve.ofArrows (fun j ↦ V (ι j)) fun j ↦ f (ι j)).HasTriplewisePullbacks := sorry

def cocycleMap (d : PreDescentData S U f) (ι : Direction → I) (ij : DirectionPair) :
    (S.mkFunctor (prToSingle (fun j ↦ f (ι j)) ij.fst)).obj (d.X (ι ij.fst)) ≅
      (S.mkFunctor (prToSingle (fun j ↦ f (ι j)) ij.snd)).obj (d.X  (ι ij.snd)) :=
  let f' := fun j ↦ f (ι j)
  let i := ij.fst
  let j := ij.snd
  calc
    (S.mkFunctor (prToSingle f' i)).obj (d.X (ι i)) ≅
        (S.mkFunctor (pr f' ij ≫ pr₀₁_₀ f (ι i) (ι j))).obj (d.X (ι i)) :=
      (S.map₂Iso (Discrete.eqToIso' (congrArg op sorry))).app (d.X (ι i))
    _ ≅ (S.mkFunctor (pr₀₁_₀ f (ι i) (ι j)) ≫ S.mkFunctor (pr f' ij)).obj (d.X (ι i)) :=
      (S.mapComp (mkHom ((pr₀₁_₀ f (ι i) (ι j)).op)) (mkHom ((pr f' ij).op))).app (d.X (ι i))
    _ ≅ (S.mkFunctor (pr₀₁_₁ f (ι i) (ι j)) ≫ S.mkFunctor (pr f' ij)).obj (d.X (ι j)) :=
      /- Here is the main part. -/
      (S.mkFunctor (pr f' ij)).mapIso (d.φ (ι i) (ι j))
    _ ≅ (S.mkFunctor ((pr f' ij) ≫ pr₀₁_₁ f (ι i) (ι j))).obj (d.X (ι j)) :=
      (S.mapComp (mkHom ((pr₀₁_₁ f (ι i) (ι j)).op)) (mkHom ((pr f' ij).op))).symm.app (d.X (ι j))
    _ ≅ (S.mkFunctor (prToSingle f' j)).obj (d.X (ι j)) :=
      (S.map₂Iso (Discrete.eqToIso' (congrArg op sorry))).symm.app (d.X (ι j))

def cocycleMapAux (d : PreDescentData S U f) (ι : Direction → I) (ij : DirectionPair) :
    (S.mkFunctor (prToSingle (fun j ↦ f (ι j)) ij.fst)) ≅
      (S.mkFunctor (pr₀₁_₀ f (ι ij.fst) (ι ij.snd)) ≫ S.mkFunctor (pr (fun j ↦ f (ι j)) ij)) :=
  let f' := fun j ↦ f (ι j)
  let i := ij.fst
  let j := ij.snd
  calc
    (S.mkFunctor (prToSingle f' i)) ≅ (S.mkFunctor (pr f' ij ≫ pr₀₁_₀ f (ι i) (ι j))) :=
      (S.map₂Iso (Discrete.eqToIso' (congrArg op sorry)))
    _ ≅ (S.mkFunctor (pr₀₁_₀ f (ι i) (ι j)) ≫ S.mkFunctor (pr f' ij)) :=
      (S.mapComp (mkHom ((pr₀₁_₀ f (ι i) (ι j)).op)) (mkHom ((pr f' ij).op)))

def cocycleMap₀₁ (d : PreDescentData S U f) (i j k : I) :
    (S.mkFunctor (pr₀₁₂_₀ f i j k)).obj (d.X i) ≅ (S.mkFunctor (pr₀₁₂_₁ f i j k)).obj (d.X j) :=
  calc
    (S.mkFunctor (pr₀₁₂_₀ f i j k)).obj (d.X i) ≅
        (S.mkFunctor (pr₀₁₂_₀₁ f i j k ≫ pr₀₁_₀ f i j)).obj (d.X i) :=
      (S.map₂Iso (Discrete.eqToIso' (congrArg op (pr₀₁₂_₀_def₀₁ f)))).app (d.X i)
    _ ≅ (S.mkFunctor (pr₀₁_₀ f i j) ≫ S.mkFunctor (pr₀₁₂_₀₁ f i j k)).obj (d.X i) :=
      (S.mapComp (mkHom ((pr₀₁_₀ f i j).op)) (mkHom ((pr₀₁₂_₀₁ f i j k).op))).app (d.X i)
    _ ≅ (S.mkFunctor (pr₀₁_₁ f i j) ≫ S.mkFunctor (pr₀₁₂_₀₁ f i j k)).obj (d.X j) :=
      /- Here is the main part. -/
      (S.mkFunctor (pr₀₁₂_₀₁ f i j k)).mapIso (d.φ i j)
    _ ≅ (S.mkFunctor ((pr₀₁₂_₀₁ f i j k) ≫ pr₀₁_₁ f i j)).obj (d.X j) :=
      (S.mapComp (mkHom ((pr₀₁_₁ f i j).op)) (mkHom ((pr₀₁₂_₀₁ f i j k).op))).symm.app (d.X j)
    _ ≅ (S.mkFunctor (pr₀₁₂_₁ f i j k)).obj (d.X j) :=
      (S.map₂Iso (Discrete.eqToIso' (congrArg op (pr₀₁₂_₁_def₀₁ f)))).symm.app (d.X j)

def cocycleMap₁₂ (d : PreDescentData S U f) (i j k : I) :
    (S.mkFunctor (pr₀₁₂_₁ f i j k)).obj (d.X j) ≅ (S.mkFunctor (pr₀₁₂_₂ f i j k)).obj (d.X k) :=
  calc
    (S.mkFunctor (pr₀₁₂_₁ f i j k)).obj (d.X j) ≅
        (S.mkFunctor (pr₀₁₂_₁₂ f i j k ≫ pr₁₂_₁ f j k)).obj (d.X j) :=
      (S.map₂Iso (Discrete.eqToIso' (congrArg op (pr₀₁₂_₁_def₁₂ f)))).app (d.X j)
    _ ≅ (S.mkFunctor (pr₁₂_₁ f j k) ≫ S.mkFunctor (pr₀₁₂_₁₂ f i j k)).obj (d.X j) :=
      (S.mapComp (mkHom ((pr₁₂_₁ f j k).op)) (mkHom ((pr₀₁₂_₁₂ f i j k).op))).app (d.X j)
    _ ≅ (S.mkFunctor (pr₁₂_₂ f j k) ≫ S.mkFunctor (pr₀₁₂_₁₂ f i j k)).obj (d.X k) :=
      /- Here is the main part. -/
      (S.mkFunctor (pr₀₁₂_₁₂ f i j k)).mapIso (d.φ j k)
    _ ≅ (S.mkFunctor ((pr₀₁₂_₁₂ f i j k) ≫ pr₁₂_₂ f j k)).obj (d.X k) :=
      (S.mapComp (mkHom ((pr₁₂_₂ f j k).op)) (mkHom ((pr₀₁₂_₁₂ f i j k).op))).symm.app (d.X k)
    _ ≅ (S.mkFunctor (pr₀₁₂_₂ f i j k)).obj (d.X k) :=
      (S.map₂Iso (Discrete.eqToIso' (congrArg op (pr₀₁₂_₂_def₁₂ f)))).symm.app (d.X k)

def cocycleMap₀₂ (d : PreDescentData S U f) (i j k : I) :
    (S.mkFunctor (pr₀₁₂_₀ f i j k)).obj (d.X i) ≅ (S.mkFunctor (pr₀₁₂_₂ f i j k)).obj (d.X k) :=
  calc
    (S.mkFunctor (pr₀₁₂_₀ f i j k)).obj (d.X i) ≅
        (S.mkFunctor (pr₀₁₂_₀₂ f i j k ≫ pr₀₂_₀ f i k)).obj (d.X i) :=
      (S.map₂Iso (Discrete.eqToIso' (congrArg op (pr₀₁₂_₀_def₀₂ f)))).app (d.X i)
    _ ≅ (S.mkFunctor (pr₀₂_₀ f i k) ≫ S.mkFunctor (pr₀₁₂_₀₂ f i j k)).obj (d.X i) :=
      (S.mapComp (mkHom ((pr₀₂_₀ f i k).op)) (mkHom ((pr₀₁₂_₀₂ f i j k).op))).app (d.X i)
    _ ≅ (S.mkFunctor (pr₀₂_₂ f i k) ≫ S.mkFunctor (pr₀₁₂_₀₂ f i j k)).obj (d.X k) :=
      /- Here is the main part. -/
      (S.mkFunctor (pr₀₁₂_₀₂ f i j k)).mapIso (d.φ i k)
    _ ≅ (S.mkFunctor ((pr₀₁₂_₀₂ f i j k) ≫ pr₀₂_₂ f i k)).obj (d.X k) :=
      (S.mapComp (mkHom ((pr₀₂_₂ f i k).op)) (mkHom ((pr₀₁₂_₀₂ f i j k).op))).symm.app (d.X k)
    _ ≅ (S.mkFunctor (pr₀₁₂_₂ f i j k)).obj (d.X k) :=
      (S.map₂Iso (Discrete.eqToIso' (congrArg op (pr₀₁₂_₂_def₀₂ f)))).symm.app (d.X k)

#check op_comp

end PreDescentData

example (S : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v₁, u₁})
    (U : C) {I : Type v₂} {V : I → C} (f : (i : I) → V i ⟶ U)
    [(Presieve.ofArrows V f).HasTriplewisePullbacks] (d : PreDescentData S U f) : Prop :=
  ∀ i j k : I,
  let ι : Direction → I
    | .left => i
    | .middle => j
    | .right => k
  d.cocycleMap ι .left_middle ≪≫ d.cocycleMap ι .middle_right = d.cocycleMap ι .left_right

-- @[simp]
def fromDirection {I : Type v₂} (i j k : I) : Direction → I
  | .left => i
  | .middle => j
  | .right => k

@[simp]
theorem fromDirection_left {I : Type v₂} (i j k : I) : fromDirection i j k 0 = i := rfl

@[simp]
theorem fromDirection_middle {I : Type v₂} (i j k : I) : fromDirection i j k 1 = j := rfl

@[simp]
theorem fromDirection_right {I : Type v₂} (i j k : I) : fromDirection i j k 2 = k := rfl


def cocycleMap' {S : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v₁, u₁}}
    {U : C} {I : Type v₂} {V : I → C} (f : (i : I) → V i ⟶ U)
    [(Presieve.ofArrows V f).HasTriplewisePullbacks] (d : PreDescentData S U f) (i j k : I) :=
  d.cocycleMap (fromDirection i j k)

structure DescentData (S : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v₁, u₁})
    (U : C) {I : Type v₂} {V : I → C} (f : (i : I) → V i ⟶ U)
    [(Presieve.ofArrows V f).HasTriplewisePullbacks] extends PreDescentData S U f where
  /-- The cocycle condition for `φᵢⱼ`. -/
  cocycle_condition : ∀ i j k : I,
    -- PreDescentData.cocycleMap₀₁ toPreDescentData i j k ≪≫
    --   PreDescentData.cocycleMap₁₂ toPreDescentData i j k =
    --     PreDescentData.cocycleMap₀₂ toPreDescentData i j k
    toPreDescentData.cocycleMap (fromDirection i j k) .left_middle ≪≫
      toPreDescentData.cocycleMap (fromDirection i j k) .middle_right =
        toPreDescentData.cocycleMap (fromDirection i j k) .left_right

    -- let φ₁₂ :=
    --   (mapCompObj _ _ _).hom ≫ (S.mkFunctor (pr₁₂ f i j k)).map (φ j k).hom ≫ (mapCompObj _ _ _).inv
    -- let φ₀₂ :=
    --   (mapCompObj _ _ _).hom ≫ (S.mkFunctor (pr₀₂ f i j k)).map (φ i k).hom ≫ (mapCompObj _ _ _).inv
    -- let φ₀₁ :=
    --   (mapCompObj _ _ _).hom ≫ (S.mkFunctor (pr₀₁ f i j k)).map (φ i j).hom ≫ (mapCompObj _ _ _).inv
    -- φ₀₁ ≫
    -- (S.map₂ (Discrete.eqToHom' (by rw [pullback_condition₁]))).app (X j) ≫ φ₁₂ =
    --   (S.map₂ (Discrete.eqToHom' (by rw [pullback_condition₀]))).app (X i) ≫
    --   φ₀₂ ≫
    --     (S.map₂ (Discrete.eqToHom' (by rw [pullback_condition₂]))).app (X k)

namespace DescentData

export PreDescentData (cocycleMap₀₁ cocycleMap₁₂ cocycleMap₀₂ cocycleMap)
  -- PreDescentData.cocycleMap₁₂
  -- PreDescentData.cocycleMap₀₂

-- attribute [local simp] eqToHom_map

def canonicalAux (S : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v₁, u₁}) (U : C)
    {I : Type v₂} {V : I → C} (f : (i : I) → V i ⟶ U)
    [(Presieve.ofArrows V f).HasTriplewisePullbacks] (X : S.mkCat U) :
    PreDescentData S U f where
  X i := (S.mkFunctor (f i)).obj X
  φ i j :=
    ((S.mapComp (mkHom (f i).op) (mkHom (pullback.fst (f i) (f j)).op)).symm ≪≫
    S.map₂Iso
      ((compIso (f i).op (pullback.fst (f i) (f j)).op).symm ≪≫
      Discrete.eqToIso' (congrArg op pullback.condition) ≪≫
      compIso (f j).op (pullback.snd (f i) (f j)).op) ≪≫
    S.mapComp (mkHom (f j).op) (mkHom (pullback.snd (f i) (f j)).op)).app X

open DirectionPair

#check Pseudofunctor.map₂_associator_app

variable {D E E' : Type} [Category D] [Category E][Category E']
variable (F G H : C ⥤ D) {G : D ⥤ E} {H : E ⥤ E'} {X : C}
#check (H.obj (G.obj (F.obj X)))

example (S : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v₁, u₁}) (U : C)
    {I : Type v₂} {V : I → C} (f : (i : I) → V i ⟶ U)
    [(Presieve.ofArrows V f).HasTriplewisePullbacks] (X : S.mkCat U) (i j k : I) (p : DirectionPair) :
    (canonicalAux S U f X).cocycleMap (fromDirection i j k) .left_middle = sorry := by
  apply Iso.ext
  dsimp only [fromDirection_left, fromDirection_middle, fromDirection_right, fst, canonicalAux, snd,
    cocycleMap, - Cat.comp_obj, - eqToIso_refl, Iso.trans_def, Iso.trans_hom, Iso.app_hom,
    Functor.mapIso_hom, Iso.refl_hom, PrelaxFunctor.mapFunctor_map, Iso.symm_hom, - eqToIso.hom,
    NatTrans.comp_app, Functor.mapIso_inv, Iso.refl_inv]
  simp only [- eqToHom_refl, PrelaxFunctor.map₂_id, Cat.id_app, Category.id_comp,
    PrelaxFunctor.map₂_comp, Cat.comp_app, Category.assoc, Functor.map_comp, - eqToIso_refl,
    Iso.refl_inv]
  dsimp only [mkFunctor]
  set pr₀₁ := (pr (fun j_1 ↦ f (fromDirection i j k j_1)) left_middle)
  slice_lhs 2 3 =>
    change (S.map (mkHom (op (f i))) ◁ ((S.mapComp (mkHom (pr₀₁_₀ f i j).op) (mkHom pr₀₁.op)).hom)).app X ≫
        (((S.mapComp (mkHom (f i).op) (mkHom (pullback.fst (f i) (f j)).op)).inv ▷ S.map (mkHom (pr₀₁.op))).app X)

  simp only [PrelaxFunctor.map₂_id, Cat.id_app, Category.id_comp, PrelaxFunctor.map₂_comp,
    Cat.comp_app, Category.assoc, Functor.map_comp]
  set f' := (fun j_1 ↦ f (fromDirection i j k j_1))
  -- set S' := S.mkFunctor
  simp
  -- sorry

def canonical (S : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v₁, u₁}) (U : C)
    {I : Type v₂} {V : I → C} (f : (i : I) → V i ⟶ U) (X : S.mkCat U)
    [(Presieve.ofArrows V f).HasTriplewisePullbacks] :
    DescentData S U f where
  toPreDescentData := canonicalAux S U f X
  cocycle_condition i j k := by
    apply Iso.ext
    dsimp only [Iso.trans_hom]
    dsimp [canonicalAux, cocycleMap₀₁, cocycleMap₁₂, cocycleMap₀₂]
    dsimp [PreDescentData.cocycleMap]
    simp only [PrelaxFunctor.map₂_id, Cat.id_app, Category.id_comp, PrelaxFunctor.map₂_comp,
      Cat.comp_app, Category.assoc, Functor.map_comp]
    simp?
    sorry
  -- cocycle_condition i j k := by
  --   -- intro i j k
  --   dsimp
  --   simp only [PrelaxFunctor.map₂_comp, Cat.comp_app, Category.assoc, Functor.map_comp]
  --   -- dsimp [mapCompObj]
  --   simp_rw [← Functor.map_comp_assoc]
  --   simp_rw [← NatTrans.comp_app_assoc]
  --   simp_rw [← S.map₂_comp_assoc]

  --   sorry

instance (U : C) :
    (Presieve.ofArrows (fun (_ : Unit) ↦ U) (fun _ ↦ 𝟙 U)).HasTriplewisePullbacks where
  has_pullbacks := by
    intro Y Z f hf g hg
    rw [Presieve.ofArrows_pUnit] at hf
    cases hf
    exact hasPullback_of_left_iso (𝟙 U) g
  has_triplewise_pullbacks := by
    intro X₁ X₂ X₃ f₁ hf₁ f₂ hf₂ f₃ hf₃ _ _
    rw [Presieve.ofArrows_pUnit] at hf₁ hf₂ hf₃
    cases hf₁; cases hf₂; cases hf₃
    exact hasPullback_of_right_iso (pullback.snd (𝟙 U) (𝟙 U)) (pullback.fst (𝟙 U) (𝟙 U))

def trivial (S : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v₁, u₁}) (U : C) (X : S.mkCat U) :
    DescentData S U (fun (_ : Unit) ↦ 𝟙 U) where
  X _ := (S.mkFunctor (𝟙 U)).obj X
  φ _ _ :=
    (S.map₂Iso (Discrete.eqToIso' (by rw [fst_eq_snd_of_mono_eq (𝟙 U)]))).app ((S.mkFunctor (𝟙 U)).obj X)
  -- Iso.refl _
  cocycle_condition := by
    -- ext x
    intro ⟨⟩ ⟨⟩ ⟨⟩

    dsimp only [Iso.app_hom, Lean.Elab.WF.paramLet, mapCompObj]
    dsimp only [mkFunctor]
    simp only [Functor.mapIso_hom, eqToIso.hom, PrelaxFunctor.mapFunctor_map, Iso.app_inv,
      Category.assoc]
    simp_rw [← NatTrans.comp_app_assoc]
    simp_rw [← NatTrans.comp_app]
    simp only [Cat.comp_obj, NatTrans.comp_app, Category.assoc]
    set Y := ((S.map (mkHom (op (𝟙 U)))).obj X)

    simp_rw [← NatTrans.comp_app_assoc]
    simp_rw [← NatTrans.comp_app]
    let α : S.map (mkHom ((pullback.fst (𝟙 U) (𝟙 U)).op)) ≅
        S.map (𝟙 _) ≫ S.map (mkHom (Quiver.Hom.op
          (by apply (IsPullback.id_vert (𝟙 U)).lift (pullback.fst (𝟙 U) (𝟙 U)) (pullback.snd (𝟙 U) (𝟙 U)) (by simp only [Category.comp_id]; exact fst_eq_snd_of_mono_eq (𝟙 U))))) := by
      apply _ ≪≫ S.mapComp _ _
      apply S.map₂Iso
      apply _ ≪≫ whiskerRightIso (LocallyDiscrete.idIso _) _
      apply _ ≪≫ (LocallyDiscrete.compIso _ _ _)
      apply Discrete.eqToIso' _
      apply congrArg op
      have := (IsPullback.id_vert (𝟙 U)).lift_fst (pullback.fst (𝟙 U) (𝟙 U)) (pullback.snd (𝟙 U) (𝟙 U)) sorry
      apply this.symm
    dsimp at α
    rw [Functor.app_hom]
    erw [PrelaxFunctor.mapFunctor_map]
    simp_rw [← NatTrans.comp_app_assoc]
    simp_rw [← NatTrans.comp_app]
    repeat rw [← eqToHom_app]
    simp only [- eqToHom_app, Category.assoc]
    repeat erw [← NatTrans.comp_app_assoc]
    simp [- eqToHom_app, - NatTrans.comp_app]
    simp [- NatTrans.comp_app]
    repeat erw [← eqToHom_app]
    repeat erw [← NatTrans.comp_app]
    simp only [← Category.assoc]
    repeat erw [← NatTrans.comp_app]
    repeat erw [← NatTrans.comp_app_assoc]
    simp only [Category.assoc]
    dsimp only [mkFunctor]
    repeat erw [← NatTrans.comp_app]

    -- simp
    -- set Y := (S.map (mkHom (op (𝟙 U)))).obj X
    -- simp only [mapCompObj, Iso.app_hom, eqToHom_map, Iso.app_inv]
    erw [← NatTrans.comp_app]
    dsimp

    dsimp [mkFunctor, pr₀₁, pr₁₂, pr₀₂]
    simp?
    have h2 : pullback.snd (𝟙 U) (𝟙 U) = 𝟙 U := by apply?
    simp only [Functor.map_id, Functor.id_obj, eqToHom_refl, Iso.refl_hom, Category.id_comp,
      Category.comp_id, Category.assoc]

def can (S : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v₁, u₁}) (U : C) :
    DescentData S U

end DescentData

end Pseudofunctor

end CategoryTheory

end
