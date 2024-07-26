import Mathlib.CategoryTheory.Comma.Arrow
import Mathlib.CategoryTheory.MorphismProperty.Basic
import Mathlib.CategoryTheory.MorphismProperty.Limits

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

/- f : X ⟶ Y is a retract of g : Z ⟶ W if we have morphisms
   i : f ⟶ g and r : g ⟶ f in the arrow category of C such that i ≫ r = 𝟙 f -/
class IsRetract {X Y Z W : C} (f : X ⟶ Y) (g : Z ⟶ W) where
  i : Arrow.mk f ⟶ Arrow.mk g
  r : Arrow.mk g ⟶ Arrow.mk f
  retract : i ≫ r = 𝟙 Arrow.mk f

namespace MorphismProperty

def StableUnderRetracts (P : MorphismProperty C) : Prop :=
  ∀ ⦃X Y Z W : C⦄ ⦃f : X ⟶ Y⦄ ⦃g : Z ⟶ W⦄ (_ : IsRetract f g)
    (_ : P g), P f

instance : StableUnderRetracts (monomorphisms C) := by
  intro X Y Z W f g H p
  refine ⟨fun {A} α β ω ↦ ?_⟩
  have := H.i.w
  dsimp at this
  apply_fun (fun f ↦ f ≫ H.i.right) at ω
  rw [Category.assoc, Category.assoc, ← this, ← Category.assoc, ← Category.assoc] at ω
  have ω' := p.right_cancellation (α ≫ H.i.left) (β ≫ H.i.left) ω
  apply_fun (fun f ↦ f ≫ H.r.left) at ω'
  simp only [Category.assoc] at ω'
  have := Arrow.hom.congr_left H.retract
  aesop

def llp_wrt (T : MorphismProperty C) : MorphismProperty C := fun _ _ f ↦
  ∀ ⦃X Y : C⦄ ⦃g : X ⟶ Y⦄ (_ : T g), HasLiftingProperty f g

def rlp_wrt (T : MorphismProperty C) : MorphismProperty C := fun _ _ f ↦
  ∀ ⦃X Y : C⦄ ⦃g : X ⟶ Y⦄ (_ : T g), HasLiftingProperty g f

instance (T : MorphismProperty C) : StableUnderRetracts (llp_wrt T) := by
  intro C D C' D' f f' H L
  intro X Y g h
  refine ⟨?_⟩
  intro u v sq
  have : (H.r.left ≫ u) ≫ g = f' ≫ (H.r.right ≫ v) := by simp [sq.w]
  obtain ⟨lift⟩ := ((L h).sq_hasLift (CommSq.mk this)).exists_lift
  refine ⟨H.i.right ≫ lift.l, ?_, ?_⟩
  · rw [← Category.assoc]
    have := H.i.w
    dsimp at this
    rw [← this, Category.assoc, lift.fac_left, ← Category.assoc]
    have := Arrow.hom.congr_left H.retract
    aesop
  · rw [Category.assoc, lift.fac_right, ← Category.assoc]
    have := Arrow.hom.congr_right H.retract
    aesop

open Limits.PushoutCocone in
instance (T : MorphismProperty C) : StableUnderCobaseChange (llp_wrt T) := by
  intro A B A' B' f s f' t P L
  intro X Y g hg
  refine ⟨?_⟩
  intro u v sq
  have ω : (s ≫ u) ≫ g = f ≫ (t ≫ v) := by
    rw [← Category.assoc, ← P.toCommSq.w, Category.assoc, Category.assoc, sq.w]
  have newSq := CommSq.mk ω
  obtain ⟨lift⟩ := ((L hg).sq_hasLift (newSq)).exists_lift
  have fac_left : s ≫ u = f ≫ lift.l := by rw [lift.fac_left]
  refine ⟨IsColimit.desc P.isColimit u lift.l fac_left,
    IsColimit.inl_desc P.isColimit u lift.l fac_left, ?_⟩
  have := @IsColimit.inr_desc _ _ _ _ _ _ _ _ P.isColimit
  dsimp at this
  sorry

end MorphismProperty

end CategoryTheory
