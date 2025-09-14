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

-- instance : Coe (ℕ × ℕ) DirectionPair where
--   coe d :=
--     match d with
--     | (0, 1) => DirectionPair.left_middle
--     | (1, 2) => DirectionPair.middle_right
--     | (0, 2) => DirectionPair.left_right
--     | _ => Inhabited.default

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

def proj₂ (p : DirectionPair) : triplePullback (f 0) (f 1) (f 2) ⟶ pullback (f p.fst) (f p.snd) :=
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

def proj₁ (i : Direction) :
    triplePullback (f 0) (f 1) (f 2) ⟶ V i :=
  match i with
  | 0 => proj₂ f .left_middle ≫ pullback.fst (f 0) (f 1)
  | 1 => proj₂ f .left_middle ≫ pullback.snd (f 0) (f 1)
  | 2 => proj₂ f .middle_right ≫ pullback.snd (f 1) (f 2)

theorem proj₁_fst {ij : DirectionPair} :
    proj₁ f ij.fst = proj₂ f ij ≫ pullback.fst (f ij.fst) (f ij.snd) := by
  cases ij
  case left_middle => rfl
  case middle_right => exact pullback.condition
  case left_right => simp [proj₁, proj₂]

theorem proj₁_snd {ij : DirectionPair} :
    proj₁ f ij.snd = proj₂ f ij ≫ pullback.snd (f ij.fst) (f ij.snd) := by
  cases ij
  all_goals simp [proj₁, proj₂]

variable {U : C} {I : Type v₂} {V : I → C} (f : (i : I) → V i ⟶ U)
variable [(Presieve.ofArrows V f).HasTriplewisePullbacks]

-- def pr₀₁₂_₀₁ (i j k : I) :
--     triplePullback (f i) (f j) (f k) ⟶ pullback (f i) (f j) :=
--   pullback.fst (pullback.snd (f i) (f j)) (pullback.fst (f j) (f k))

-- def pr₀₁₂_₁₂ (i j k : I) :
--     triplePullback (f i) (f j) (f k) ⟶ pullback (f j) (f k) :=
--   pullback.snd (pullback.snd (f i) (f j)) (pullback.fst (f j) (f k))

-- def pr₀₁₂_₀₂ (i j k : I) :
--     triplePullback (f i) (f j) (f k) ⟶ pullback (f i) (f k) :=
--   pullback.lift (pr₀₁₂_₀₁ f i j k ≫ pullback.fst (f i) (f j))
--     (pr₀₁₂_₁₂ f i j k ≫ pullback.snd (f j) (f k)) <| by
--       dsimp only [pr₀₁₂_₀₁, pr₀₁₂_₁₂]
--       rw [Category.assoc, pullback.condition, ← Category.assoc, pullback.condition,
--         Category.assoc, pullback.condition, Category.assoc]

-- abbrev pr₀₁_₀ (i j : I) :
--     pullback (f i) (f j) ⟶ V i :=
--   pullback.fst (f i) (f j)

-- abbrev pr₀₁_₁ (i j : I) :
--     pullback (f i) (f j) ⟶ V j :=
--   pullback.snd (f i) (f j)

-- abbrev pr₁₂_₁ (j k : I) :
--     pullback (f j) (f k) ⟶ V j :=
--   pullback.fst (f j) (f k)

-- abbrev pr₁₂_₂ (j k : I) :
--     pullback (f j) (f k) ⟶ V k :=
--   pullback.snd (f j) (f k)

-- abbrev pr₀₂_₀ (i k : I) :
--     pullback (f i) (f k) ⟶ V i :=
--   pullback.fst (f i) (f k)

-- abbrev pr₀₂_₂ (i k : I) :
--     pullback (f i) (f k) ⟶ V k :=
--   pullback.snd (f i) (f k)

-- theorem pullback_condition₀ (i j k : I) :
--     pr₀₁₂_₀₁ f i j k ≫ pr₀₁_₀ f i j = pr₀₁₂_₀₂ f i j k ≫ pr₀₂_₀ f i k := by
--   simp only [limit.lift_π, PullbackCone.mk_pt, PullbackCone.mk_π_app, pr₀₁₂_₀₁, pr₀₁₂_₀₂]

-- theorem pullback_condition₁ (i j k : I) :
--     pr₀₁₂_₀₁ f i j k ≫ pr₀₁_₁ f i j = pr₀₁₂_₁₂ f i j k ≫ pr₁₂_₁ f j k :=
--   pullback.condition

-- theorem pullback_condition₂ (i j k : I) :
--     pr₀₁₂_₀₂ f i j k ≫ pr₀₂_₂ f i k = pr₀₁₂_₁₂ f i j k ≫ pr₁₂_₂ f j k := by
--   simp only [limit.lift_π, PullbackCone.mk_pt, PullbackCone.mk_π_app, pr₀₁₂_₀₂, pr₀₁₂_₀₂, pr₀₁₂_₁₂]

-- def pr₀₁₂_₀ (i j k : I) : triplePullback (f i) (f j) (f k) ⟶ V i :=
--   pr₀₁₂_₀₁ f i j k ≫ pr₀₁_₀ f i j

-- theorem pr₀₁₂_₀_def₀₁ {i j k : I} :
--     pr₀₁₂_₀ f i j k = pr₀₁₂_₀₁ f i j k ≫ pr₀₁_₀ f i j :=
--   rfl

-- theorem pr₀₁₂_₀_def₀₂ {i j k : I} :
--     pr₀₁₂_₀ f i j k = pr₀₁₂_₀₂ f i j k ≫ pr₀₂_₀ f i k := by
--   simp only [pr₀₁₂_₀_def₀₁, pr₀₁₂_₀₁, pr₀₁₂_₀₂, limit.lift_π, PullbackCone.mk_pt,
--     PullbackCone.mk_π_app]

-- def pr₀₁₂_₁ (i j k : I) : triplePullback (f i) (f j) (f k) ⟶ V j :=
--   pr₀₁₂_₀₁ f i j k ≫ pr₀₁_₁ f i j

-- theorem pr₀₁₂_₁_def₀₁ {i j k : I} :
--     pr₀₁₂_₁ f i j k = pr₀₁₂_₀₁ f i j k ≫ pr₀₁_₁ f i j :=
--   rfl

-- theorem pr₀₁₂_₁_def₁₂ {i j k : I} :
--     pr₀₁₂_₁ f i j k = pr₀₁₂_₁₂ f i j k ≫ pr₁₂_₁ f j k :=
--   pullback.condition

-- def pr₀₁₂_₂ (i j k : I) : triplePullback (f i) (f j) (f k) ⟶ V k :=
--   pr₀₁₂_₁₂ f i j k ≫ pr₁₂_₂ f j k

-- theorem pr₀₁₂_₂_def₁₂ {i j k : I} :
--     pr₀₁₂_₂ f i j k = pr₀₁₂_₁₂ f i j k ≫ pr₁₂_₂ f j k :=
--   rfl

-- theorem pr₀₁₂_₂_def₀₂ {i j k : I} :
--     pr₀₁₂_₂ f i j k = pr₀₁₂_₀₂ f i j k ≫ pr₀₂_₂ f i k := by
--   simp only [pr₀₁₂_₂_def₁₂, pr₀₁₂_₁₂, pr₀₁₂_₀₂, limit.lift_π, PullbackCone.mk_pt,
--     PullbackCone.mk_π_app]

end TriplePullback

namespace Pseudofunctor

open TriplePullback

-- set_option pp.universes true

abbrev mkCat (S : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v₁, u₁}) (X : C) : Cat :=
  S.obj ⟨op X⟩

-- def mkFunctor (S : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v₁, u₁}) {X Y : C} (f : Y ⟶ X) :
--     S.mkCat X ⟶ S.mkCat Y :=
--   S.map ⟨op f⟩

-- def mkCat' (S : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v₁, u₁}) (X : C) : Type u₁ :=
--   S.obj ⟨op X⟩

abbrev mkFunctor (S : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v₁, u₁}) {X Y : C} (f : Y ⟶ X) :
    S.mkCat X ⟶ S.mkCat Y :=
  S.map (LocallyDiscrete.mkHom f.op)

#check Pseudofunctor.mapComp

abbrev mapCompCat (S : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v₁, u₁}) {X Y Z : C}
    (f : Y ⟶ X) (g : Z ⟶ Y) :
    (S.mkFunctor (g ≫ f)) ≅ S.mkFunctor f ≫ S.mkFunctor g :=
  S.mapComp (mkHom f.op) (mkHom g.op)

-- @[to_app?]
-- @[simps!?]
abbrev mapCompCatApp (S : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v₁, u₁}) {X Y Z : C}
    (f : Y ⟶ X) (g : Z ⟶ Y) {x : S.mkCat X} :
    (S.mkFunctor (g ≫ f)).obj x ≅ (S.mkFunctor g).obj ((S.mkFunctor f).obj x) :=
  (mapCompCat S f g).app x

structure PreDescentData (S : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v₁, u₁})
    (U : C) {I : Type v₂} {V : I → C} (f : (i : I) → V i ⟶ U)
    [(Presieve.ofArrows V f).HasTriplewisePullbacks] where
  /-- An object `Xᵢ` of `S Vᵢ` for each `i : I`. -/
  X : ∀ i, S.obj ⟨op (V i)⟩
  /-- An isomorphism `φᵢⱼ : pr₀* Xᵢ ≅ pr₁* Xⱼ` for each `i j : I`, where `pr₀` and `pr₁`
  are the projections from the pullback. -/
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
    (S.mkFunctor (proj₁ (fun j ↦ f (ι j)) ij.fst)).obj (d.X (ι ij.fst)) ≅
      (S.mkFunctor (proj₁ (fun j ↦ f (ι j)) ij.snd)).obj (d.X  (ι ij.snd)) :=
  let f' := fun j ↦ f (ι j)
  let i := ij.fst
  let j := ij.snd
  calc
    (S.mkFunctor (proj₁ f' i)).obj (d.X (ι i)) ≅
        (S.mkFunctor (proj₂ f' ij ≫ pullback.fst (f (ι i)) (f (ι j)))).obj (d.X (ι i)) :=
      (S.map₂Iso (Discrete.eqToIso' (congrArg op (proj₁_fst f')))).app (d.X (ι i))
    _ ≅ (S.mkFunctor (pullback.fst (f (ι i)) (f (ι j))) ≫ S.mkFunctor (proj₂ f' ij)).obj (d.X (ι i)) :=
      (S.mapCompCat (pullback.fst (f (ι i)) (f (ι j))) (proj₂ f' ij)).app (d.X (ι i))
    _ ≅ (S.mkFunctor (pullback.snd (f (ι i)) (f (ι j))) ≫ S.mkFunctor (proj₂ f' ij)).obj (d.X (ι j)) :=
      /- Here is the main part. -/
      (S.mkFunctor (proj₂ f' ij)).mapIso (d.φ (ι i) (ι j))
    _ ≅ (S.mkFunctor ((proj₂ f' ij) ≫ pullback.snd (f (ι i)) (f (ι j)))).obj (d.X (ι j)) :=
      (S.mapCompCat (pullback.snd (f (ι i)) (f (ι j))) (proj₂ f' ij)).symm.app (d.X (ι j))
    _ ≅ (S.mkFunctor (proj₁ f' j)).obj (d.X (ι j)) :=
      (S.map₂Iso (Discrete.eqToIso' (congrArg op (proj₁_snd f')))).symm.app (d.X (ι j))

-- def cocycleMapAux (d : PreDescentData S U f) (ι : Direction → I) (ij : DirectionPair) :
--     (S.mkFunctor (proj₁ (fun j ↦ f (ι j)) ij.fst)) ≅
--       (S.mkFunctor (pr₀₁_₀ f (ι ij.fst) (ι ij.snd)) ≫ S.mkFunctor (proj₂ (fun j ↦ f (ι j)) ij)) :=
--   let f' := fun j ↦ f (ι j)
--   let i := ij.fst
--   let j := ij.snd
--   calc
--     (S.mkFunctor (proj₁ f' i)) ≅ (S.mkFunctor (proj₂ f' ij ≫ pr₀₁_₀ f (ι i) (ι j))) :=
--       (S.map₂Iso (Discrete.eqToIso' (congrArg op sorry)))
--     _ ≅ (S.mkFunctor (pr₀₁_₀ f (ι i) (ι j)) ≫ S.mkFunctor (proj₂ f' ij)) :=
--       (S.mapComp (mkHom ((pr₀₁_₀ f (ι i) (ι j)).op)) (mkHom ((proj₂ f' ij).op)))

-- def cocycleMap₀₁ (d : PreDescentData S U f) (i j k : I) :
--     (S.mkFunctor (pr₀₁₂_₀ f i j k)).obj (d.X i) ≅ (S.mkFunctor (pr₀₁₂_₁ f i j k)).obj (d.X j) :=
--   calc
--     (S.mkFunctor (pr₀₁₂_₀ f i j k)).obj (d.X i) ≅
--         (S.mkFunctor (pr₀₁₂_₀₁ f i j k ≫ pr₀₁_₀ f i j)).obj (d.X i) :=
--       (S.map₂Iso (Discrete.eqToIso' (congrArg op (pr₀₁₂_₀_def₀₁ f)))).app (d.X i)
--     _ ≅ (S.mkFunctor (pr₀₁_₀ f i j) ≫ S.mkFunctor (pr₀₁₂_₀₁ f i j k)).obj (d.X i) :=
--       (S.mapComp (mkHom ((pr₀₁_₀ f i j).op)) (mkHom ((pr₀₁₂_₀₁ f i j k).op))).app (d.X i)
--     _ ≅ (S.mkFunctor (pr₀₁_₁ f i j) ≫ S.mkFunctor (pr₀₁₂_₀₁ f i j k)).obj (d.X j) :=
--       /- Here is the main part. -/
--       (S.mkFunctor (pr₀₁₂_₀₁ f i j k)).mapIso (d.φ i j)
--     _ ≅ (S.mkFunctor ((pr₀₁₂_₀₁ f i j k) ≫ pr₀₁_₁ f i j)).obj (d.X j) :=
--       (S.mapComp (mkHom ((pr₀₁_₁ f i j).op)) (mkHom ((pr₀₁₂_₀₁ f i j k).op))).symm.app (d.X j)
--     _ ≅ (S.mkFunctor (pr₀₁₂_₁ f i j k)).obj (d.X j) :=
--       (S.map₂Iso (Discrete.eqToIso' (congrArg op (pr₀₁₂_₁_def₀₁ f)))).symm.app (d.X j)

-- def cocycleMap₁₂ (d : PreDescentData S U f) (i j k : I) :
--     (S.mkFunctor (pr₀₁₂_₁ f i j k)).obj (d.X j) ≅ (S.mkFunctor (pr₀₁₂_₂ f i j k)).obj (d.X k) :=
--   calc
--     (S.mkFunctor (pr₀₁₂_₁ f i j k)).obj (d.X j) ≅
--         (S.mkFunctor (pr₀₁₂_₁₂ f i j k ≫ pr₁₂_₁ f j k)).obj (d.X j) :=
--       (S.map₂Iso (Discrete.eqToIso' (congrArg op (pr₀₁₂_₁_def₁₂ f)))).app (d.X j)
--     _ ≅ (S.mkFunctor (pr₁₂_₁ f j k) ≫ S.mkFunctor (pr₀₁₂_₁₂ f i j k)).obj (d.X j) :=
--       (S.mapComp (mkHom ((pr₁₂_₁ f j k).op)) (mkHom ((pr₀₁₂_₁₂ f i j k).op))).app (d.X j)
--     _ ≅ (S.mkFunctor (pr₁₂_₂ f j k) ≫ S.mkFunctor (pr₀₁₂_₁₂ f i j k)).obj (d.X k) :=
--       /- Here is the main part. -/
--       (S.mkFunctor (pr₀₁₂_₁₂ f i j k)).mapIso (d.φ j k)
--     _ ≅ (S.mkFunctor ((pr₀₁₂_₁₂ f i j k) ≫ pr₁₂_₂ f j k)).obj (d.X k) :=
--       (S.mapComp (mkHom ((pr₁₂_₂ f j k).op)) (mkHom ((pr₀₁₂_₁₂ f i j k).op))).symm.app (d.X k)
--     _ ≅ (S.mkFunctor (pr₀₁₂_₂ f i j k)).obj (d.X k) :=
--       (S.map₂Iso (Discrete.eqToIso' (congrArg op (pr₀₁₂_₂_def₁₂ f)))).symm.app (d.X k)

-- def cocycleMap₀₂ (d : PreDescentData S U f) (i j k : I) :
--     (S.mkFunctor (pr₀₁₂_₀ f i j k)).obj (d.X i) ≅ (S.mkFunctor (pr₀₁₂_₂ f i j k)).obj (d.X k) :=
--   calc
--     (S.mkFunctor (pr₀₁₂_₀ f i j k)).obj (d.X i) ≅
--         (S.mkFunctor (pr₀₁₂_₀₂ f i j k ≫ pr₀₂_₀ f i k)).obj (d.X i) :=
--       (S.map₂Iso (Discrete.eqToIso' (congrArg op (pr₀₁₂_₀_def₀₂ f)))).app (d.X i)
--     _ ≅ (S.mkFunctor (pr₀₂_₀ f i k) ≫ S.mkFunctor (pr₀₁₂_₀₂ f i j k)).obj (d.X i) :=
--       (S.mapComp (mkHom ((pr₀₂_₀ f i k).op)) (mkHom ((pr₀₁₂_₀₂ f i j k).op))).app (d.X i)
--     _ ≅ (S.mkFunctor (pr₀₂_₂ f i k) ≫ S.mkFunctor (pr₀₁₂_₀₂ f i j k)).obj (d.X k) :=
--       /- Here is the main part. -/
--       (S.mkFunctor (pr₀₁₂_₀₂ f i j k)).mapIso (d.φ i k)
--     _ ≅ (S.mkFunctor ((pr₀₁₂_₀₂ f i j k) ≫ pr₀₂_₂ f i k)).obj (d.X k) :=
--       (S.mapComp (mkHom ((pr₀₂_₂ f i k).op)) (mkHom ((pr₀₁₂_₀₂ f i j k).op))).symm.app (d.X k)
--     _ ≅ (S.mkFunctor (pr₀₁₂_₂ f i j k)).obj (d.X k) :=
--       (S.map₂Iso (Discrete.eqToIso' (congrArg op (pr₀₁₂_₂_def₀₂ f)))).symm.app (d.X k)

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
    --   (mapCompCatApp _ _ _).hom ≫ (S.mkFunctor (pr₁₂ f i j k)).map (φ j k).hom ≫ (mapCompCatApp _ _ _).inv
    -- let φ₀₂ :=
    --   (mapCompCatApp _ _ _).hom ≫ (S.mkFunctor (pr₀₂ f i j k)).map (φ i k).hom ≫ (mapCompCatApp _ _ _).inv
    -- let φ₀₁ :=
    --   (mapCompCatApp _ _ _).hom ≫ (S.mkFunctor (pr₀₁ f i j k)).map (φ i j).hom ≫ (mapCompCatApp _ _ _).inv
    -- φ₀₁ ≫
    -- (S.map₂ (Discrete.eqToHom' (by rw [pullback_condition₁]))).app (X j) ≫ φ₁₂ =
    --   (S.map₂ (Discrete.eqToHom' (by rw [pullback_condition₀]))).app (X i) ≫
    --   φ₀₂ ≫
    --     (S.map₂ (Discrete.eqToHom' (by rw [pullback_condition₂]))).app (X k)

namespace DescentData

export PreDescentData (cocycleMap)
  -- PreDescentData.cocycleMap₁₂
  -- PreDescentData.cocycleMap₀₂

variable {S : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v₁, u₁}} {U : C}
    {I : Type v₂} {V : I → C} {f : (i : I) → V i ⟶ U}
    [(Presieve.ofArrows V f).HasTriplewisePullbacks]

@[ext]
structure Hom (d₁ d₂ : DescentData S U f) where
  /-- A morphism in `S Vᵢ` for each `i : I`. -/
  hom : ∀ i, d₁.X i ⟶ d₂.X i
  /-- The squares involving the `φᵢⱼ` commute. -/
  comm : ∀ i j : I,
    (S.mkFunctor (pullback.fst (f i) (f j))).map (hom i) ≫ (d₂.φ i j).hom =
      (d₁.φ i j).hom ≫ (S.mkFunctor (pullback.snd (f i) (f j))).map (hom j)

attribute [reassoc] Hom.comm

@[simps]
def Hom.id (d : DescentData S U f) : Hom d d where
  hom i := 𝟙 (d.X i)
  comm i j := by simp

@[simps]
def Hom.comp {d₁ d₂ d₃ : DescentData S U f} (f : Hom d₁ d₂) (g : Hom d₂ d₃) : Hom d₁ d₃ where
  hom i := f.hom i ≫ g.hom i
  comm i j := by simp [g.comm, f.comm_assoc]

-- attribute [local simp] Hom.comm Hom.comm_assoc

instance : Category (DescentData S U f) where
  Hom := Hom
  id d := Hom.id d
  comp f g := Hom.comp f g

def canonicalAux (S : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v₁, u₁}) (U : C)
    {I : Type v₂} {V : I → C} (f : (i : I) → V i ⟶ U)
    [(Presieve.ofArrows V f).HasTriplewisePullbacks] (X : S.mkCat U) :
    PreDescentData S U f where
  X i := (S.mkFunctor (f i)).obj X
  φ i j :=
    ((S.mapComp (mkHom (f i).op) (mkHom (pullback.fst (f i) (f j)).op)).symm ≪≫
    S.map₂Iso (Discrete.eqToIso' (congrArg op pullback.condition)) ≪≫
      -- ((compIso (f i).op (pullback.fst (f i) (f j)).op).symm ≪≫
      -- Discrete.eqToIso' (congrArg op pullback.condition) ≪≫
      -- compIso (f j).op (pullback.snd (f i) (f j)).op) ≪≫
    S.mapComp (mkHom (f j).op) (mkHom (pullback.snd (f i) (f j)).op)).app X

open DirectionPair

#check Pseudofunctor.map₂_associator_app

example {B : Type} [Bicategory B]
  (self : Pseudofunctor B Cat) {a b c d : B} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) (X : ↑(self.obj a)) :
  (self.map₂ (α_ f g h).hom).app X =
    (self.mapComp (f ≫ g) h).hom.app X ≫
      (self.map h).map ((self.mapComp f g).hom.app X) ≫
        (α_ (self.map f) (self.map g) (self.map h)).hom.app X ≫
          (self.mapComp g h).inv.app ((self.map f).obj X) ≫ (self.mapComp f (g ≫ h)).inv.app X := by
  dsimp only [Cat.comp_obj]
  apply Pseudofunctor.map₂_associator_app

variable {D E E' : Type} [Category D] [Category E][Category E']
variable (F G H : C ⥤ D) {G : D ⥤ E} {H : E ⥤ E'} {X : C}
#check (H.obj (G.obj (F.obj X)))


example (S : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v₁, u₁}) (U : C)
    {I : Type v₂} {V : I → C} (f : (i : I) → V i ⟶ U)
    [(Presieve.ofArrows V f).HasTriplewisePullbacks] (X : S.mkCat U) (i j k : I) (p : DirectionPair) :
    let ι := (fun t ↦ f (fromDirection i j k t))
    ((canonicalAux S U f X).cocycleMap (fromDirection i j k) .left_middle).hom =
      (S.mkFunctor (f i) ◁ S.map₂ (Discrete.eqToIso' sorry).hom ≫
        S.mkFunctor (f i) ◁ (S.mapCompCat (pullback.fst (f i) (f j)) (proj₂ ι .left_middle)).hom ≫
          (α_ _ _ _).inv ≫
          (S.mapCompCat (f i) (pullback.fst (f i) (f j))).inv ▷ S.mkFunctor (proj₂ ι .left_middle) ≫
              S.map₂
                ((compIso (f i).op (pullback.fst (f i) (f j)).op).inv ≫
                  (Discrete.eqToIso' sorry).hom ≫ (compIso (f j).op (pullback.snd (f i) (f j)).op).hom) ▷ S.mkFunctor (proj₂ ι .left_middle) ≫
          (S.mapCompCat (f j) (pullback.snd (f i) (f j))).hom ▷ S.mkFunctor (proj₂ ι .left_middle) ≫
          (α_ _ _ _).hom ≫
        S.mkFunctor (f j) ◁ (S.mapCompCat (pullback.snd (f i) (f j)) (proj₂ ι .left_middle)).inv ≫
      S.mkFunctor (f j) ◁ (S.map₂Iso (Discrete.eqToIso' sorry)).inv).app X := by
  dsimp only [fromDirection_left, fromDirection_middle, fromDirection_right, fst, mkFunctor,
    canonicalAux, compIso, snd, cocycleMap, op_comp, Cat.comp_obj, mapCompCat, Iso.trans_def,
    Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, eqToIso.hom, eqToHom_refl,
    PrelaxFunctor.mapFunctor_map, Iso.symm_hom, eqToIso.inv, NatTrans.comp_app, Functor.mapIso_inv,
    Cat.comp_app, Cat.whiskerLeft_app, Cat.whiskerRight_app, Lean.Elab.WF.paramLet]
  simp only [Functor.map_comp, Category.assoc]
  congr 2
  rw [Cat.associator_hom_app]
  rw [Cat.associator_inv_app]
  dsimp only [Iso.refl_inv, Cat.comp_obj]
  simp only [← Category.assoc]; congr 2; simp only [Category.assoc]
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]



def caconicalCocycleMapAux (S : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v₁, u₁}) (U : C)
    {I : Type v₂} {V : I → C} (f : (i : I) → V i ⟶ U)
    [(Presieve.ofArrows V f).HasTriplewisePullbacks] (X : S.mkCat U) (i j k : I) (p : DirectionPair) :
    let ι := (fun t ↦ f (fromDirection i j k t))
    let i' := (fromDirection i j k p.fst)
    let j' := (fromDirection i j k p.snd)
    S.mkFunctor (f i') ≫ S.mkFunctor (proj₁ ι p.fst) ⟶ S.mkFunctor (f j') ≫ S.mkFunctor (proj₁ ι p.snd) := by
  sorry

theorem canonical_cocycle_aux₁ (S : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v₁, u₁}) (U : C)
    {I : Type v₂} {V : I → C} (f : (i : I) → V i ⟶ U)
    [(Presieve.ofArrows V f).HasTriplewisePullbacks] (X : S.mkCat U) (i j k : I) (p : DirectionPair) :
    let ι := (fun t ↦ f (fromDirection i j k t))
    let i' := (fromDirection i j k p.fst)
    let j' := (fromDirection i j k p.snd)
    ((canonicalAux S U f X).cocycleMap (fromDirection i j k) p).hom =
      (S.mkFunctor (f i') ◁ S.map₂ (Discrete.eqToIso' sorry).hom ≫
        S.mkFunctor (f i') ◁ (S.mapCompCat (pullback.fst (f i') (f j')) (proj₂ ι p)).hom ≫
          (α_ _ _ _).inv ≫
          (S.mapCompCat (f i') (pullback.fst (f i') (f j'))).inv ▷ S.mkFunctor (proj₂ ι p) ≫
              S.map₂
                ((compIso (f i').op (pullback.fst (f i') (f j')).op).inv ≫
                  (Discrete.eqToIso' sorry).hom ≫ (compIso (f j').op (pullback.snd (f i') (f j')).op).hom) ▷ S.mkFunctor (proj₂ ι p) ≫
          (S.mapCompCat (f j') (pullback.snd (f i') (f j'))).hom ▷ S.mkFunctor (proj₂ ι p) ≫
          (α_ _ _ _).hom ≫
        S.mkFunctor (f j') ◁ (S.mapCompCat (pullback.snd (f i') (f j')) (proj₂ ι p)).inv ≫
      S.mkFunctor (f j') ◁ (S.map₂Iso (Discrete.eqToIso' sorry)).inv).app X := by
  dsimp only [fromDirection_left, fromDirection_middle, fromDirection_right, fst, mkFunctor,
    canonicalAux, compIso, snd, cocycleMap, op_comp, Cat.comp_obj, mapCompCat, Iso.trans_def,
    Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, eqToIso.hom, eqToHom_refl,
    PrelaxFunctor.mapFunctor_map, Iso.symm_hom, eqToIso.inv, NatTrans.comp_app, Functor.mapIso_inv,
    Cat.comp_app, Cat.whiskerLeft_app, Cat.whiskerRight_app, Lean.Elab.WF.paramLet]
  simp only [Functor.map_comp, Category.assoc]
  congr 2
  rw [Cat.associator_hom_app]
  rw [Cat.associator_inv_app]
  dsimp only [Iso.refl_inv, Cat.comp_obj]
  simp only [← Category.assoc]; congr 2; simp only [Category.assoc]
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

-- example (S : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v₁, u₁}) (U : C)
--     {I : Type v₂} {V : I → C} (f : (i : I) → V i ⟶ U)
--     [(Presieve.ofArrows V f).HasTriplewisePullbacks] (X : S.mkCat U) (i j k : I) (p : DirectionPair) :
--     let ι := (fun t ↦ f (fromDirection i j k t))
--     ((canonicalAux S U f X).cocycleMap (fromDirection i j k) .left_middle).hom =
--       (S.mkFunctor (f i) ◁ S.map₂ (Discrete.eqToIso' sorry).hom ≫
--         S.mkFunctor (f i) ◁ (S.mapCompCat (pullback.fst (f i) (f j)) (proj₂ ι .left_middle)).hom ≫
--           (α_ _ _ _).inv ≫
--           (S.mapCompCat (f i) (pullback.fst (f i) (f j))).inv ▷ S.mkFunctor (proj₂ ι .left_middle) ≫
--               S.map₂
--                 ((compIso (f i).op (pullback.fst (f i) (f j)).op).inv ≫
--                   (Discrete.eqToIso' sorry).hom ≫ (compIso (f j).op (pullback.snd (f i) (f j)).op).hom) ▷ S.mkFunctor (proj₂ ι .left_middle) ≫
--           (S.mapCompCat (f j) (pullback.snd (f i) (f j))).hom ▷ S.mkFunctor (proj₂ ι .left_middle) ≫
--           (α_ _ _ _).hom ≫
--         S.mkFunctor (f j) ◁ (S.mapCompCat (pullback.snd (f i) (f j)) (proj₂ ι .left_middle)).inv ≫
--       S.mkFunctor (f j) ◁ (S.map₂Iso (Discrete.eqToIso' sorry)).inv).app X := by
--   dsimp only [mkFunctor]
--   rw [S.mapComp_assoc_mapComp_inv_assoc]
--   rw [S.mapComp_assoc_inv_mapComp_inv_assoc]
--   rw [← S.map₂_whisker_right_assoc]
--   rw [← S.map₂_comp_assoc]
--   rw [← S.map₂_comp_assoc]
--   rw [LocallyDiscrete.associator_hom]
--   rw [LocallyDiscrete.associator_inv]
--   dsimp only [compIso, Discrete.eqToIso', Discrete.eqToIso]
--   dsimp only [eqToIso.hom, eqToIso.inv]
--   simp only [fromDirection_left, fromDirection_middle, fromDirection_right, fst, snd, op_comp,
--     - eqToHom_refl, Category.comp_id, Category.id_comp, Category.assoc, -PrelaxFunctor.map₂_comp,
--     map₂_whisker_right, - eqToIso_refl, - Functor.mapIso_refl, PrelaxFunctor.mapFunctor_obj,
--     Iso.refl_inv, -Cat.comp_app, Cat.comp_obj, Cat.whiskerLeft_app, Cat.whiskerRight_app, Cat.id_app]
--   simp only [eqToHom_trans, eqToHom_whiskerRight]
--   simp [- Cat.comp_app, Cat.comp_obj, Cat.whiskerLeft_app, Cat.id_app]
--   simp only [Cat.comp_app, Cat.comp_obj, Cat.whiskerLeft_app, Cat.id_app]
--   -- simp only [fromDirection_left, fromDirection_middle, fromDirection_right, fst, snd, op_comp,
--   --   -eqToHom_refl, -eqToIso_refl, Functor.mapIso_inv, Iso.refl_inv, -PrelaxFunctor.mapFunctor_map,
--   --   -Cat.comp_app, -Cat.comp_obj, -Cat.whiskerLeft_app]
--   -- rw [Cat.associator_hom_app]
--   dsimp
--   simp
--   -- simp only [fromDirection_left, fromDirection_middle, fromDirection_right, fst, snd, op_comp,
--   --   eqToIso_refl, Iso.refl_hom, eqToIso.hom, PrelaxFunctor.map₂_comp, comp_whiskerRight,
--   --   Functor.mapIso_refl, PrelaxFunctor.mapFunctor_obj, Iso.refl_inv, Category.assoc, Cat.comp_app,
--   --   Cat.comp_obj, Cat.whiskerLeft_app, Cat.whiskerRight_app, Cat.id_app]
--   -- rw?
--   sorry


theorem cocycle_aux (S : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v₁, u₁}) (U : C)
    {I : Type v₂} {V : I → C} (f : (i : I) → V i ⟶ U)
    [(Presieve.ofArrows V f).HasTriplewisePullbacks]
    (X : S.mkCat U) (i j k : I) (p : DirectionPair) :
    let ι := (fun t ↦ f (fromDirection i j k t))
    let i' := (fromDirection i j k p.fst)
    let j' := (fromDirection i j k p.snd)
    ((canonicalAux S U f X).cocycleMap (fromDirection i j k) p).hom =
      (S.map (mkHom (f i').op) ◁ S.map₂ (eqToHom sorry) ≫
        (S.mapComp (mkHom (f i').op)
              (mkHom (pullback.fst (f i') (f j')).op ≫
                mkHom (proj₂ ι p).op)).inv ≫
          S.map₂ (eqToHom sorry) ≫
            (S.mapComp (mkHom (f j').op)
                  (mkHom (pullback.snd (f i') (f j')).op ≫
                    mkHom (proj₂ ι p).op)).hom ≫
              S.map (mkHom (f j').op) ◁ (S.map₂Iso (eqToIso sorry)).inv).app X := by
  rw [canonical_cocycle_aux₁]
  congr 1
  dsimp only [mkFunctor]
  rw [S.mapComp_assoc_mapComp_inv_assoc]
  rw [S.mapComp_assoc_inv_mapComp_inv_assoc]
  rw [← S.map₂_whisker_right_assoc]
  rw [← S.map₂_comp_assoc]
  rw [← S.map₂_comp_assoc]
  rw [LocallyDiscrete.associator_hom]
  rw [LocallyDiscrete.associator_inv]
  dsimp only [fromDirection_left, fromDirection_middle, fromDirection_right, fst, snd, op_comp,
    -eqToIso_refl, Iso.refl_hom, eqToIso.hom, Functor.mapIso_inv, Iso.refl_inv,
    PrelaxFunctor.mapFunctor_map, -eqToHom_refl]
  simp only [-eqToHom_refl, comp_whiskerRight, Category.assoc, PrelaxFunctor.map₂_comp,
    -map₂_whisker_right, Iso.inv_hom_id_assoc, -eqToIso_refl, Iso.refl_inv, PrelaxFunctor.map₂_id,
    whiskerLeft_id, Category.id_comp]
  congr 2
  simp only [← Category.assoc]
  congr
  simp only [Category.assoc]
  rw [← S.map₂_comp_assoc]
  rw [← S.map₂_comp_assoc]
  rw [← S.map₂_comp_assoc]
  rw [← S.map₂_comp]
  congr 1
  apply Subsingleton.elim
  -- dsimp [mkFunctor, canonicalAux, cocycleMap]
  -- simp only [PrelaxFunctor.map₂_comp, Cat.comp_app, Category.assoc, Functor.map_comp,
  --   mapCompCat]
  -- -- simp only [← NatTrans.comp_app]
  -- rw [S.mapComp_assoc_mapComp_inv_assoc]
  -- rw [S.mapComp_assoc_inv_mapComp_inv_assoc]
  -- simp only [- map₂_associator_inv, comp_whiskerRight, map₂_associator, Category.assoc,
  --   Iso.inv_hom_id_assoc, PrelaxFunctor.map₂_id, whiskerLeft_id, Category.id_comp]
  -- rw [← S.map₂_whisker_right_assoc]
  -- rw [← S.map₂_comp_assoc]
  -- rw [← S.map₂_comp_assoc]
  -- rw [LocallyDiscrete.associator_hom]
  -- rw [LocallyDiscrete.associator_inv]

-- theorem cocycle_aux' (S : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v₁, u₁}) (U : C)
--     {I : Type v₂} {V : I → C} (f : (i : I) → V i ⟶ U)
--     [(Presieve.ofArrows V f).HasTriplewisePullbacks]
--     (X : S.mkCat U) (i j k : I) (p : DirectionPair) :
--     let ι := (fun t ↦ f (fromDirection i j k t))
--     let i' := (fromDirection i j k p.fst)
--     let j' := (fromDirection i j k p.snd)
--     ((canonicalAux S U f X).cocycleMap (fromDirection i j k) p).hom =
--       (S.map (mkHom (f i').op) ◁ S.map₂ (eqToHom sorry) ≫
--         (S.mapComp (mkHom (f i').op)
--               (mkHom (pullback.fst (f i') (f j')).op ≫
--                 mkHom (proj₂ ι p).op)).inv ≫
--           S.map₂ (eqToHom sorry) ≫
--             (S.mapComp (mkHom (f j').op)
--                   (mkHom (pullback.snd (f i') (f j')).op ≫
--                     mkHom (proj₂ ι p).op)).hom ≫
--               S.map (mkHom (f j').op) ◁ (S.map₂Iso (eqToIso sorry)).inv).app X := by
--   dsimp [mkFunctor, canonicalAux, cocycleMap]
--   simp only [PrelaxFunctor.map₂_comp, Cat.comp_app, Category.assoc, Functor.map_comp]
--   rw [S.mapComp_assoc_mapComp_inv_assoc]
--   rw [S.mapComp_assoc_inv_mapComp_inv_assoc]
--   rw [← S.map₂_whisker_right_assoc]
--   rw [← S.map₂_comp_assoc]
--   rw [← S.map₂_comp_assoc]
--   rw [LocallyDiscrete.associator_hom]
--   rw [LocallyDiscrete.associator_inv]
--   dsimp only [compIso, Discrete.eqToIso', Discrete.eqToIso]
--   dsimp only [eqToIso.hom, eqToIso.inv]
--   simp only [fromDirection_left, fromDirection_middle, fromDirection_right, fst, snd, op_comp,
--     - eqToHom_refl, Category.comp_id, Category.id_comp, Category.assoc, -PrelaxFunctor.map₂_comp,
--     map₂_whisker_right, - eqToIso_refl, - Functor.mapIso_refl, PrelaxFunctor.mapFunctor_obj,
--     Iso.refl_inv, -Cat.comp_app, Cat.comp_obj, Cat.whiskerLeft_app, Cat.whiskerRight_app, Cat.id_app]


def canonical (S : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v₁, u₁}) (U : C)
    {I : Type v₂} {V : I → C} (f : (i : I) → V i ⟶ U) (X : S.mkCat U)
    [(Presieve.ofArrows V f).HasTriplewisePullbacks] :
    DescentData S U f where
  toPreDescentData := canonicalAux S U f X
  cocycle_condition i j k := by
    apply Iso.ext
    dsimp only [Iso.trans_hom]
    rw [cocycle_aux _ _ _ _ _ _ _ DirectionPair.left_middle]
    rw [cocycle_aux _ _ _ _ _ _ _ DirectionPair.middle_right]
    rw [cocycle_aux _ _ _ _ _ _ _ DirectionPair.left_right]
    simp only [← NatTrans.comp_app]
    apply congrFun (congrArg _ _)
    simp only [Category.assoc]
    dsimp only [fromDirection_left, fromDirection_middle, fromDirection_right, fst, snd]
    rw [S.map₂Iso_inv]
    dsimp only [eqToIso.inv]
    slice_lhs 5 6 =>
      rw [← whiskerLeft_comp]
      rw [← S.map₂_comp]
      rw [eqToHom_trans]
    slice_lhs 4 6 =>
      rw [← map₂_whisker_left]
      rw [whiskerLeft_eqToHom]
    simp only [Category.assoc]
    rw [← S.map₂_comp_assoc]
    rw [← S.map₂_comp_assoc]
    simp only [eqToHom_trans]
    rw [S.map₂Iso_inv, S.map₂Iso_inv]
    simp only [eqToIso.inv]
    simp only [map₂_whisker_left_symm, Category.assoc]
    simp only [whiskerLeft_eqToHom]
    simp only [Iso.hom_inv_id_assoc]
    simp only [S.map₂_eqToHom]
    simp only [eqToHom_refl, Category.id_comp, eqToHom_trans_assoc]

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

    sorry

end DescentData

end Pseudofunctor

end CategoryTheory

end
