import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.Order.CompleteLattice
import Mathlib.Order.InitialSeg
import Mathlib.SetTheory.Ordinal.Basic

set_option autoImplicit false

universe u v w

noncomputable section

section Order

def limit_oe {β : Type v} [Preorder β] : {i : WithTop β // i < ⊤} ≃o β where
  toFun := fun
    | ⟨(i : β), _⟩ => i
    | ⟨⊤, h⟩ => False.elim sorry
  invFun := fun i => ⟨i, WithTop.coe_lt_top i⟩
  left_inv := fun
    | ⟨(i : β), _⟩ => rfl
    | ⟨⊤, h⟩ => False.elim sorry
  right_inv := fun _ => rfl
  map_rel_iff' := @fun i j => sorry

variable {γ : Type v} [Preorder γ]

def IsSucc (i j : γ) : Prop :=
∀ k, k < j ↔ k ≤ i

theorem IsSucc.lt {i j : γ} (h : IsSucc i j) : i < j :=
(h i).2 le_rfl

theorem IsSucc.le {i j : γ} (h : IsSucc i j) : i ≤ j :=
le_of_lt h.lt

def IsLimitStage (j : γ) : Prop :=
IsLUB {i | i < j} j

inductive AnalyzeType (j : γ)
| isBot : IsBot j → AnalyzeType j
| isSucc : (i : γ) → IsSucc i j → AnalyzeType j
| isLimitStage : IsLimitStage j → AnalyzeType j

variable {β : Type v} [PartialOrder β] [OrderTop β]

lemma eq_top_of_is_succ_top {i : β} (h : IsSucc (i : WithTop β) ⊤) : i = (⊤ : β) :=
sorry

@[simp] lemma isSucc_top : IsSucc ((⊤ : β) : WithTop β) (⊤ : WithTop β) :=
sorry

def isoWithTopOpen {γ : Type v} [PartialOrder γ] [OrderTop γ] : γ ≃o WithTop {i : γ // i < ⊤} :=
sorry

section

variable (γ : Type v) [DecidableEq γ] [PartialOrder γ] [OrderTop γ] (α : γ) (hα : IsSucc α ⊤)

lemma ne_top_of_le_α (y : {i // i ≤ α}) : ((y : γ) = ⊤) ↔ False := by
  rcases y with ⟨yv, yp⟩
  rw [← hα yv] at yp
  rw [iff_false]
  exact ne_of_lt yp

def succ_oe' : WithTop {i // i ≤ α} ≃o γ where
  invFun x := if h : x = ⊤ then ⊤ else WithTop.some ⟨x, (hα _).mp (Ne.lt_top h)⟩
  toFun := WithTop.recTopCoe ⊤ Subtype.val
  right_inv := by
    intro x
    dsimp only
    split
    · symm; assumption
    · rfl
  left_inv := by
    have := ne_top_of_le_α _ α hα
    intro y
    induction y using WithTop.recTopCoe <;> simp [this]
  map_rel_iff' := by
    have := ne_top_of_le_α _ α hα
    rintro y y'
    induction y using WithTop.recTopCoe <;> induction y' using WithTop.recTopCoe <;>
      dsimp <;> simp [this]

def succ_oe : γ ≃o WithTop {i // i ≤ α} := (succ_oe' γ α hα).symm

end

def isoPUnit_of_isBot_top {γ : Type v} [PartialOrder γ] [OrderTop γ] (h : IsBot (⊤ : γ)) :
    (γ ≃o PUnit) :=
sorry

def isoWithTop_of_isSucc_top {γ : Type v} [DecidableEq γ] [PartialOrder γ] [OrderTop γ] (α : γ) (h : IsSucc α ⊤) :
  γ ≃o WithTop {i // i ≤ α} :=
succ_oe γ α h

end Order

section WellOrderedLT

class WellOrderedLT (γ : Type v) extends LinearOrder γ, IsWellOrder γ (· < ·)

instance (γ : Type v) [WellOrderedLT γ] (α : γ) : WellOrderedLT {i // i ≤ α} :=
{ (inferInstance : LinearOrder {i // i ≤ α}) with }

def ltType (γ : Type v) [WellOrderedLT γ] : Ordinal.{v} :=
Ordinal.type ((· < ·) : γ → γ → Prop)

class WellOrderedTop (γ : Type v) extends WellOrderedLT γ, OrderTop γ

class WellOrderedNoTop (γ : Type v) extends WellOrderedLT γ, NoTopOrder γ

variable {β γ : Type v}

instance : WellOrderedTop PUnit := {}

instance [WellOrderedLT β] : WellOrderedTop (WithTop β) :=
  { (inferInstance : LinearOrder (WithTop β)) with }

instance [WellOrderedLT γ] (α : γ) : WellOrderedLT {i // i < α} :=
  { (inferInstance : LinearOrder {i // i < α}) with }

def noTop [WellOrderedTop γ] (h : IsLimitStage (⊤ : γ)) : WellOrderedNoTop {i : γ // i < ⊤} :=
  { (inferInstance : WellOrderedLT {i : γ // i < ⊤}) with
    exists_not_le := sorry }

instance [Preorder γ] (α : γ) : OrderTop {i // i ≤ α} where
  top := ⟨α, le_rfl⟩
  le_top i := i.2

instance [WellOrderedLT γ] (α : γ) : WellOrderedTop {i // i ≤ α} :=
  { (inferInstance : LinearOrder {i // i ≤ α}), (inferInstance : OrderTop {i // i ≤ α}) with }

def analyze [WellOrderedLT γ] (j : γ) : AnalyzeType j :=
sorry

theorem isLimit_top [WellOrderedNoTop β] : IsLimitStage (⊤ : WithTop β) :=
sorry

theorem exists_succ [WellOrderedTop γ] (α : γ) (h : α ≠ ⊤) : ∃ β, IsSucc α β :=
sorry

theorem exists_succ' [WellOrderedNoTop γ] (α : γ) : ∃ β, IsSucc α β :=
sorry

theorem ltType_closed_lt [WellOrderedLT γ] (α β : γ) (h : α < β) : ltType {i // i ≤ α} < ltType γ :=
sorry

theorem ltType_closed_le [WellOrderedLT γ] (α : γ) : ltType {i // i ≤ α} ≤ ltType γ :=
sorry

theorem ltType_open_lt [WellOrderedLT γ] (α : γ) : ltType {i // i < α} < ltType γ :=
sorry

end WellOrderedLT

section Prefix

def Prefix (γ δ : Type v) [PartialOrder γ] [PartialOrder δ] : Type v :=
InitialSeg ((· < ·) : γ → γ → Prop) ((· < ·) : δ → δ → Prop)

instance (γ δ : Type v) [PartialOrder γ] [PartialOrder δ] : CoeFun (Prefix γ δ) (fun _ => γ → δ) where
  coe ι := ι.toFun

def Prefix.id (γ : Type v) [PartialOrder γ] : Prefix γ γ :=
InitialSeg.refl _

def Prefix.comp {γ δ ε : Type v} [PartialOrder γ] [PartialOrder δ] [PartialOrder ε] :
  Prefix δ ε → Prefix γ δ → Prefix γ ε :=
fun g f => InitialSeg.trans f g

def Prefix.ofOrderIso {γ δ : Type v} [PartialOrder γ] [PartialOrder δ] (e : γ ≃o δ) : Prefix γ δ :=
InitialSeg.ofIso e.toRelIsoLT

@[simps]
def Prefix.closed {γ : Type v} [PartialOrder γ] (j : γ) : Prefix {i // i ≤ j} γ where
  toFun := Subtype.val
  inj' := Subtype.val_injective
  map_rel_iff' := by intros; rfl
  init' := fun a b h => ⟨⟨b, h.le.trans a.2⟩, rfl⟩

def Prefix.open {γ : Type v} [PartialOrder γ] (j : γ) : Prefix {i // i < j} γ where
  toFun := Subtype.val
  inj' := Subtype.val_injective
  map_rel_iff' := by intros; rfl
  init' := fun a b h => ⟨⟨b, h.trans a.2⟩, rfl⟩

def Prefix.fixme {γ δ : Type v} [PartialOrder γ] [PartialOrder δ] (ι : Prefix γ δ) (j : γ) :
  { i // i < j } ≃o { i // i < ι j } where
  toFun i := ⟨ι i.1, sorry⟩
  invFun := sorry
  left_inv := sorry
  right_inv := sorry
  map_rel_iff' := sorry

instance {γ δ : Type v} [WellOrderedLT γ] [WellOrderedLT δ] : Subsingleton (Prefix γ δ) :=
show Subsingleton (InitialSeg _ _) from inferInstance

def toWithTop {β : Type v} [PartialOrder β] : Prefix β (WithTop β) where
  toFun i := i
  inj' := Option.some_injective _
  map_rel_iff' := by intros; simp
  init' := by
    intro a b h
    induction b using WithTop.recTopCoe
    case top => simp at h
    case coe b => exact ⟨b, rfl⟩

def pref {β : Type v} [PartialOrder β] (α : β) : Prefix {i // i ≤ α} (WithTop β) where
  toFun i := i.val
  inj' := by intro i i' h; ext; simpa using h
  map_rel_iff' := by intros; simp
  init' := by
    intro a b h
    induction b using WithTop.recTopCoe
    case top => simp at h
    case coe b =>
      have h' : b < a := by simpa using h
      refine ⟨⟨b, le_trans h'.le a.2⟩, rfl⟩

def pref' {β : Type v} [PartialOrder β] (α α' : β) (H : α ≤ α') :
    Prefix {i // i ≤ α} {i // i ≤ α'} where
  toFun i := ⟨i.val, le_trans i.property H⟩
  inj' := by intro i i' h; ext; simpa using h
  map_rel_iff' := by intros; simp
  init' := by
    intro a b h
    refine ⟨⟨b.1, le_trans h.le a.2⟩, rfl⟩

end Prefix

namespace CategoryTheory

def _root_.Prefix.functor {γ δ : Type v} [PartialOrder γ] [PartialOrder δ] (ι : Prefix γ δ) : γ ⥤ δ :=
Monotone.functor $ StrictMono.monotone (fun _ _ => ι.map_rel_iff.2)

def equivOfOrderIso {P Q : Type v} [PartialOrder P] [PartialOrder Q] (e : P ≃o Q) : P ≌ Q where
  functor := e.monotone.functor
  inverse := e.symm.monotone.functor
  unitIso := sorry
  counitIso := sorry
  functor_unitIso_comp := sorry

end CategoryTheory

def orderTypeRec {C : (γ : Type v) → [WellOrderedTop γ] → Type w}
  (h : (γ : Type v) → [WellOrderedTop γ] →
       (IH : (β : Type v) → [WellOrderedTop β] → (hβ : ltType β < ltType γ) → C β) → C γ)
  (γ : Type v) [WellOrderedTop γ] : C γ :=
h γ (fun β _ _ => orderTypeRec h β)
termination_by _ γ h => ltType γ
