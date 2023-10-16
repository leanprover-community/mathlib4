import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.CategoryTheory.Functor.Category
import Mathlib.CategoryTheory.FullSubcategory
import Mathlib.Order.CompleteLattice

set_option autoImplicit false

universe v u

noncomputable def WellFounded.recursion' {α : Sort u} {r : α → α → Prop} (hwf : WellFounded r)
  {C : α → Sort v} (h : ∀ x, (∀ y, r y x → C y) → C x) (a : α) : C a :=
WellFounded.recursion hwf a h

-- local notation:80 f " ∘ " g => g ≫ f
local notation C " ~> " D => C ⥤ D
local notation "ID" => CategoryTheory.CategoryStruct.id  -- type as \b1

open CategoryTheory Limits

namespace CategoryTheory

structure Contraction (C : Type u) [Category.{v} C] where
  center : C
  iso : (X : C) → X ≅ center
  eq : ∀ {X Y : C} (f g : X ⟶ Y), f = g

end CategoryTheory

namespace CategoryTheory.Transfinite

class WellOrderTop (γ : Type v) extends CompleteLinearOrder γ where
  wf_lt : WellFounded ((· < ·) : γ → γ → Prop)

section cocone

variable {γ : Type v} [PartialOrder γ]

def IsBot (j : γ) : Prop :=
∀ k, k ≤ j → k = j

def IsSucc (i j : γ) : Prop :=
∀ k, k < j ↔ k ≤ i

theorem IsSucc.lt {i j : γ} (h : IsSucc i j) : i < j :=
(h i).2 le_rfl

theorem IsSucc.le {i j : γ} (h : IsSucc i j) : i ≤ j :=
le_of_lt h.lt

def IsSucc.hom {i j : γ} (h : IsSucc i j) : i ⟶ j :=
homOfLE h.le

def IsSucc.orderIso {i j : γ} (h : IsSucc i j) : {k // k ≤ j} ≃o WithTop {k // k ≤ i} := sorry

theorem IsSucc.orderIso_low {i j : γ} (h : IsSucc i j) (k) (hk : k.1 ≤ i) :
  h.orderIso k = WithTop.some ⟨k.1, hk⟩ :=
sorry

inductive LeSuccCases (i j k : γ)
| lePrev : k ≤ i → LeSuccCases i j k
| eqSucc : k = j → LeSuccCases i j k

def IsSucc.analyzeLE {i j : γ} (hij : IsSucc i j) (k : γ) (hk : k ≤ j) : LeSuccCases i j k :=
sorry

def IsLimitStage (j : γ) : Prop :=
IsLUB {i | i < j} j

inductive StepType (j : γ) : Type v
| bot : IsBot j → StepType j
| succ : (i : γ) → IsSucc i j → StepType j
| limit : IsLimitStage j → StepType j

def coconeAt (j : γ) : Cocone (fullSubcategoryInclusion (fun i => i < j)) :=
{ pt := j,
  ι := { app := fun i => homOfLE (le_of_lt i.property) } }

def SmoothAt {C : Type u} [Category.{v} C] (F : γ ~> C) (j : γ) : Prop :=
Nonempty (IsColimit (F.mapCocone (coconeAt j)))

end cocone

variable (γ : Type v) [WellOrderTop γ]

theorem isBot_iff (j : γ) : IsBot j ↔ j = ⊥ :=
sorry

theorem isBot_iff' (j : γ) : IsBot j ↔ j ≤ ⊥ :=
sorry

def woStepType (j : γ) : StepType j :=
sorry

variable {C : Type u} [Category.{v} C]
variable (X : C) (F : C ~> C) (η : Functor.id C ⟶ F)
-- TODO: fancy 1 is untypable, but it's a good thing because it also breaks the server interaction

variable (α : γ)

structure GoodDiagram where
  fn : {i // i ≤ α} ~> C
  iso0 : fn.obj ⟨⊥, bot_le⟩ ≅ X
  isoStep : (i j : {i // i ≤ α}) → (h : IsSucc i j) →
    { φ : fn.obj j ≅ F.obj (fn.obj i) // fn.map h.hom ≫ φ.hom = η.app (fn.obj i) }
--  isoStepEq : (i j : {i // i ≤ α}) → (h : IsSucc i j) → fn.map h.hom ≫ (isoStep i j h).hom = η.app (fn.obj i)
  smooth : ∀ (j : {i // i ≤ α}), IsLimitStage j → SmoothAt fn j

@[ext] structure GoodDiagramHom (D1 D2 : GoodDiagram γ X F η α) where
  nat : D1.fn ⟶ D2.fn
  iso0 : D1.iso0.hom = nat.app ⟨⊥, bot_le⟩ ≫ D2.iso0.hom :=
    by aesop_cat
  isoStep : ∀ i j (h : IsSucc i j),
    (D1.isoStep i j h).val.hom ≫ F.map (nat.app i) = nat.app j ≫ (D2.isoStep i j h).val.hom :=
    by aesop_cat

instance : Category (GoodDiagram γ X F η α) where
  Hom := GoodDiagramHom γ X F η α
  id D := { nat := ID D.fn }
  comp {D1 D2 D3} f g :=
  { nat := f.nat ≫ g.nat,
    iso0 := sorry,
    isoStep := sorry }
  id_comp := sorry
  comp_id := sorry
  assoc := sorry

lemma GoodDiagramHom.nat_bot_eq (D1 D2 : GoodDiagram γ X F η α) (f : D1 ⟶ D2) :
  f.nat.app ⟨⊥, bot_le⟩ = D1.iso0.hom ≫ D2.iso0.inv :=
sorry

structure GoodDiagramIso (D1 D2 : GoodDiagram γ X F η α) where
  natIso : D1.fn ≅ D2.fn
  iso0 : D1.iso0 = natIso.app ⟨⊥, bot_le⟩ ≪≫ D2.iso0 :=
    by aesop_cat
  isoStep : ∀ i j (h : IsSucc i j),
    (D1.isoStep i j h).val ≪≫ F.mapIso (natIso.app i) = natIso.app j ≪≫ (D2.isoStep i j h).val :=
    by aesop_cat

def GoodDiagram.mkIso (D1 D2 : GoodDiagram γ X F η α) :
  GoodDiagramIso γ X F η α D1 D2 → (D1 ≅ D2) :=
sorry

def UniqueGoodDiagram_bot : Contraction (GoodDiagram γ X F η ⊥) := by
    fconstructor
    · fconstructor
      · exact (Functor.const _).obj X
      · exact Iso.refl X
      · intro i j h
        have : ¬ IsSucc i j := sorry
        apply (this h).elim
      · intro j h
        have : ¬ IsLimitStage j := sorry
        apply (this h).elim
    · intro D
      apply GoodDiagram.mkIso
      fconstructor
      · fapply NatIso.ofComponents
        · intro i
          haveI hi : i ≅ ⟨⊥, bot_le⟩ := { hom := homOfLE i.property, inv := homOfLE bot_le }
          exact D.fn.mapIso hi ≪≫ D.iso0
        · intro i j hij
          simp only [Functor.const_obj_obj, Functor.const_obj_map, Iso.trans_hom, Functor.mapIso_hom, Category.comp_id,
            ← Category.assoc, ← D.fn.map_comp]
          rfl
      · simp
        sorry
      · intro i j h
        have : ¬ IsSucc i j := sorry
        apply (this h).elim
    · intros D1 D2 f g
      apply GoodDiagramHom.ext
      ext i
      have : i = ⟨⊥, bot_le⟩ := sorry
      subst this
      rw [GoodDiagramHom.nat_bot_eq, GoodDiagramHom.nat_bot_eq]

section succ

open WithTop
def UniqueGoodDiagram_succ_aux (α β : γ) (hα : IsSucc α β)
  (IH : Contraction (GoodDiagram γ X F η α)) : WithTop {i // i ≤ α} ~> C where
  obj := fun
    | .some i => IH.center.fn.obj i
    | .none => F.obj (IH.center.fn.obj ⟨α, le_rfl⟩)
  map := @fun
    | .some i, .some j, hij => IH.center.fn.map (homOfLE $ coe_le_coe.1 $ leOfHom hij)
    | none, .some j, hij => False.elim (WithTop.not_top_le_coe _ $ leOfHom hij)
    | .some i, none, hij => IH.center.fn.map (homOfLE (by change i.1 ≤ α; exact i.2)) ≫ η.app (IH.center.fn.obj ⟨α, le_rfl⟩)
    | none, none, hij => ID _
  map_id := @fun
    | .some i => IH.center.fn.map_id _
    | none => rfl
  map_comp := sorry

def UniqueGoodDiagram_succ (α β : γ) (hα : IsSucc α β)
  (IH : Contraction (GoodDiagram γ X F η α)) : Contraction (GoodDiagram γ X F η β) where
  center := {
    fn := Monotone.functor (IsSucc.orderIso hα).monotone ⋙ UniqueGoodDiagram_succ_aux γ X F η α β hα IH
    iso0 := _
    isoStep := _
    smooth := _
  }
  iso := _
  eq := _
 /- by
  fconstructor
  · fconstructor
    · fconstructor
      · fconstructor
        · intro ⟨k, hk⟩
          rcases hα.analyzeLE k hk with (hk'|⟨rfl⟩)
          case lePrev => exact IH.center.fn.obj ⟨k, hk'⟩
          case eqSucc => exact F.obj (IH.center.fn.obj ⟨α, le_rfl⟩)
        · intro ⟨k1, hk1⟩ ⟨k2, hk2⟩ hk
          done -/

end succ

noncomputable
def UniqueGoodDiagram : Contraction (GoodDiagram γ X F η α) := by
  revert α
  refine WellOrderTop.wf_lt.recursion' ?_
  intros β IH
  rcases woStepType γ β with (hβ|⟨α,hα⟩|hβ)
  case bot =>
    rw [isBot_iff] at hβ
    subst hβ
    apply UniqueGoodDiagram_bot
  case succ =>
    exact UniqueGoodDiagram_succ γ X F η α β hα (IH α hα.lt)
  sorry
  done

end CategoryTheory.Transfinite
