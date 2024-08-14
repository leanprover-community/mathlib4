import Mathlib.CategoryTheory.Comma.Arrow
import Mathlib.CategoryTheory.MorphismProperty.Basic
import Mathlib.CategoryTheory.MorphismProperty.Limits
import Mathlib.AlgebraicTopology._Transfinite

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

instance monomorphisms.StableUnderRetracts : StableUnderRetracts (monomorphisms C) := by
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

def llp_wrt' {X Y : C} (p : X ⟶ Y) : MorphismProperty C := fun _ _ f ↦ HasLiftingProperty f p

def rlp_wrt' {X Y : C} (p : X ⟶ Y) : MorphismProperty C := fun _ _ f ↦ HasLiftingProperty p f

instance llp_retract {T : MorphismProperty C} : StableUnderRetracts (llp_wrt T) := by
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

instance llp_retract' {X Y : C} {p : X ⟶ Y} : StableUnderRetracts (llp_wrt' p) := by
  intro C D C' D' f f' H L
  refine ⟨?_⟩
  intro u v sq
  have : (H.r.left ≫ u) ≫ p = f' ≫ (H.r.right ≫ v) := by simp [sq.w]
  obtain ⟨lift⟩ := (L.sq_hasLift (CommSq.mk this)).exists_lift
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
instance llp_pushout {T : MorphismProperty C} : StableUnderCobaseChange (llp_wrt T) := by
  intro A B A' B' f s f' t P L
  intro X Y g hg
  refine ⟨?_⟩
  intro u v sq
  have w : (s ≫ u) ≫ g = f ≫ (t ≫ v) := by
    rw [← Category.assoc, ← P.toCommSq.w, Category.assoc, Category.assoc, sq.w]
  obtain ⟨lift⟩ := ((L hg).sq_hasLift (CommSq.mk w)).exists_lift
  let lift' : B' ⟶ X := IsColimit.desc P.isColimit u lift.l (by rw [lift.fac_left])
  let l : f' ≫ lift' = u := IsColimit.inl_desc P.isColimit u lift.l (by rw [lift.fac_left])
  let l' : t ≫ lift' = lift.l := IsColimit.inr_desc P.isColimit u lift.l (by rw [lift.fac_left])
  let newCocone := mk (f' ≫ v) (t ≫ v) (by have := P.w; apply_fun (fun f ↦ f ≫ v) at this; aesop)
  refine ⟨lift', l,
    (P.isColimit.uniq newCocone (lift' ≫ g) ?_).trans (P.isColimit.uniq newCocone v ?_).symm⟩
  all_goals
    dsimp [newCocone]
    intro j
    cases j
    simp only [Limits.span_zero, condition_zero, IsPushout.cocone_inl, Category.assoc]
  · rw [← Category.assoc, ← Category.assoc, Category.assoc s f' lift', l, ← sq.w, Category.assoc]
  · rename_i k; cases k; all_goals dsimp
    · rw [← Category.assoc, l, sq.w]
    · rw [← Category.assoc, l', lift.fac_right]
  · rename_i k; cases k; all_goals dsimp

open Limits.PushoutCocone in
instance llp_pushout' {X Y : C} {p : X ⟶ Y} : StableUnderCobaseChange (llp_wrt' p) := by
  intro A B A' B' f s f' t P L
  refine ⟨?_⟩
  intro u v sq
  have w : (s ≫ u) ≫ p = f ≫ (t ≫ v) := by
    rw [← Category.assoc, ← P.toCommSq.w, Category.assoc, Category.assoc, sq.w]
  obtain ⟨lift⟩ := (L.sq_hasLift (CommSq.mk w)).exists_lift
  let lift' : B' ⟶ X := IsColimit.desc P.isColimit u lift.l (by rw [lift.fac_left])
  let l : f' ≫ lift' = u := IsColimit.inl_desc P.isColimit u lift.l (by rw [lift.fac_left])
  let l' : t ≫ lift' = lift.l := IsColimit.inr_desc P.isColimit u lift.l (by rw [lift.fac_left])
  let newCocone := mk (f' ≫ v) (t ≫ v) (by have := P.w; apply_fun (fun f ↦ f ≫ v) at this; aesop)
  refine ⟨lift', l,
    (P.isColimit.uniq newCocone (lift' ≫ p) ?_).trans (P.isColimit.uniq newCocone v ?_).symm⟩
  all_goals
    dsimp [newCocone]
    intro j
    cases j
    simp only [Limits.span_zero, condition_zero, IsPushout.cocone_inl, Category.assoc]
  · rw [← Category.assoc, ← Category.assoc, Category.assoc s f' lift', l, ← sq.w, Category.assoc]
  · rename_i k; cases k; all_goals dsimp
    · rw [← Category.assoc, l, sq.w]
    · rw [← Category.assoc, l', lift.fac_right]
  · rename_i k; cases k; all_goals dsimp

def StableUnderTransfiniteComposition (P : MorphismProperty C) : Prop :=
  ∀ ⦃X Y: C⦄ ⦃f : X ⟶ Y⦄ (_ : IsTransfiniteComposition P f), P f

section llp_comp_aux

variable {α : Ordinal.{v}} (o : Ordinal.{v}) (ho : o ≤ α)
    (F : {β | β ≤ α} ⥤ C) (hF : Limits.PreservesColimits F) (T : MorphismProperty C)
    (hS : ∀ (β : Ordinal.{v}) (hβ : β < α), T.llp_wrt (F.map (to_succ hβ)))
    {X Y : C} {g : X ⟶ Y} {u : F.obj ord_zero_le ⟶ X} {v : F.obj (ord_le_refl α) ⟶ Y}
    (sq : CommSq u (F.map bot_to_top) g v)

structure llp_comp_aux {α : Ordinal.{v}} (o : Ordinal.{v}) (ho : o ≤ α)
    (F : {β | β ≤ α} ⥤ C) (hF : Limits.PreservesColimits F) (T : MorphismProperty C)
    (hS : ∀ (β : Ordinal.{v}) (hβ : β < α), T.llp_wrt (F.map (to_succ hβ)))
    {X Y : C} {g : X ⟶ Y} {u : F.obj ord_zero_le ⟶ X} {v : F.obj (ord_le_refl α) ⟶ Y}
    (sq : CommSq u (F.map bot_to_top) g v) : Sort (v + 2) where
  μ (β) (hβ : β ≤ o) : F.obj ⟨β, le_trans hβ ho⟩ ⟶ X
  μ_comp (β) (hβ : β ≤ o) : (μ β hβ) ≫ g = (F.map (ord_le_to_top (le_trans hβ ho))) ≫ v
  μ_fac (β γ) (hβ : β ≤ o) (hγ : γ ≤ o) (h : β ≤ γ) : μ β hβ = (F.map (LE.le.hom h)) ≫ μ γ hγ

def P : Ordinal.{v} → Sort (v + 2) :=
  fun o ↦ ((ho : o < (α + 1)) → llp_comp_aux o (Order.le_of_lt_succ ho) F hF T hS sq)

-- `006R`, this has been done by Joel
/-
want ∀ β ≤ α, a morphism (μ β) : F(β) ⟶ X such that
  ⬝ (μ β) ≫ g = F(β ⟶ α) ≫ v
  ⬝ ∀ β ≤ γ, (μ β) = F(β ⟶ γ) ≫ (μ γ)
Then to prove llp_comp below, the lift we need is (μ α) : F(α) ⟶ X
-/
instance llp_comp {T : MorphismProperty C} : StableUnderTransfiniteComposition (llp_wrt T) := by
  intro C0 Cα f h X Y g hg
  induction h with
  | mk α F hF hS =>
    refine ⟨?_⟩
    intro u v sq
    have U : llp_comp_aux α (le_refl α) F hF T hS sq := by
      apply @WellFounded.recursion _ _ Ordinal.lt_wf (P F hF T hS sq) α
      swap; exact Order.lt_succ α
      intro γ ih hγ
      refine ⟨?_, ?_, ?_⟩
      · intro β hβ
        by_cases β = 0
        · subst β
          exact u
        by_cases (∃ a, β = Order.succ a)
        rename_i h
        · let a := Exists.choose h
          have ha := Exists.choose_spec h
          change β = a + 1 at ha
          let a_lt_α : a < α := by
            rw [ha] at hβ
            exact Order.lt_of_succ_lt_succ (lt_of_le_of_lt hβ hγ)
          have a_prop : llp_comp_aux a (le_of_lt a_lt_α) F hF T hS sq := sorry
          --have := (a_prop.μ a (le_refl a))
          have a_succ_le_α : a + 1 ≤ α := sorry
          have newSq : CommSq (a_prop.μ a (le_refl a)) (F.map (to_succ a_lt_α))
            g (F.map (ord_le_to_top a_succ_le_α) ≫ v) := sorry
          have l := ((hS a a_lt_α hg).sq_hasLift newSq).exists_lift.some.l
          have last : ⟨β, le_trans hβ (Order.le_of_lt_succ hγ)⟩ =
              (ord_succ_le_of_lt a_lt_α) := by simp [ord_succ_le_of_lt, ha]
          rw [last]
          exact l
        . rename_i h₁ h₂
          have := Ordinal.zero_or_succ_or_limit β
          have : β.IsLimit := by aesop
          sorry
      · intro β hβ
        cases Ordinal.zero_or_succ_or_limit β with
        | inl h =>
          have := sq.w
          aesop
        | inr =>
          rename_i h
          cases h with
          | inl h =>
            let a := Exists.choose h
            have ha : β = a + 1 := Exists.choose_spec h
            sorry
          | inr h => sorry
      · sorry
    sorry

end llp_comp_aux

instance llp_comp' {X Y : C} {p : X ⟶ Y} : StableUnderTransfiniteComposition (llp_wrt' p) := sorry

-- maybe this should be a class
def WeaklySaturated (P : MorphismProperty C) : Prop :=
  P.StableUnderCobaseChange ∧ P.StableUnderRetracts ∧ P.StableUnderTransfiniteComposition

instance llp_weakly_saturated (T : MorphismProperty C) : WeaklySaturated (llp_wrt T) :=
  ⟨llp_pushout, llp_retract, llp_comp⟩

instance llp_weakly_saturated' {X Y : C} (p : X ⟶ Y) : WeaklySaturated (llp_wrt' p) :=
  ⟨llp_pushout', llp_retract', llp_comp'⟩

end MorphismProperty

end CategoryTheory
