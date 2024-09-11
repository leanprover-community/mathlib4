import Mathlib.Order.Circular
import Mathlib.Logic.Embedding.Basic

structure CircularOrderHom (α β : Type*) [Btw α] [Btw β] where
  toFun : α → β
  btw_apply' {a b c : α} : btw a b c → btw (toFun a) (toFun b) (toFun c)

/-- Notation for a `CircularOrderHom`. -/
infixr:25 " →co " => CircularOrderHom

class CircularOrderHomClass (F : Type*) (α β : outParam Type*) [Btw α] [Btw β] [FunLike F α β] where
  btw_apply (f : F) {a b c : α} : btw a b c → btw (f a) (f b) (f c)

export CircularOrderHomClass (btw_apply)

instance {α β : Type*} [Btw α] [Btw β] : FunLike (α →co β) α β where
  coe f := f.toFun
  coe_injective' | ⟨_, _⟩, ⟨_, _⟩, rfl => rfl

instance {α β : Type*} [Btw α] [Btw β] : CircularOrderHomClass (α →co β) α β where
  btw_apply f := f.btw_apply'

namespace CircularOrderHom

initialize_simps_projections CircularOrderHom (toFun → coe, as_prefix coe)

variable {α β γ δ : Type*} [Btw α] [Btw β] [Btw γ] [Btw δ]

@[simps (config := .asFn)]
protected def id (α : Type*) [Btw α] : α →co α := ⟨id, id⟩

@[simps (config := .asFn)]
protected def comp (f : β →co γ) (g : α →co β) : α →co γ :=
  ⟨f ∘ g, fun h ↦ by simp [btw_apply, h]⟩

@[simp] theorem comp_id (f : α →co β) : f.comp (.id α) = f := rfl
@[simp] theorem id_comp (f : α →co β) : .comp (.id β) f = f := rfl

theorem comp_assoc (f : γ →co δ) (g : β →co γ) (h : α →co β) :
    (f.comp g).comp h = f.comp (g.comp h) :=
  rfl

end CircularOrderHom

structure CircularOrderEmbedding (α β : Type*) [Btw α] [Btw β] extends α ↪ β where
  btw_apply_iff' {a b c : α} : btw (toFun a) (toFun b) (toFun c) ↔ btw a b c

/-- Notation for a `CircularOrderEmbedding`. -/
infixr:25 " ↪co " => CircularOrderEmbedding

class CircularOrderEmbeddingClass (F : Type*) (α β : outParam (Type*)) [Btw α] [Btw β]
    [FunLike F α β] extends EmbeddingLike F α β where
  btw_apply_iff (f : F) {a b c : α} : btw (f a) (f b) (f c) ↔ btw a b c

export CircularOrderEmbeddingClass (btw_apply_iff)
attribute [simp] btw_apply_iff

instance {α β} [Btw α] [Btw β] : CircularOrderEmbeddingClass (α ↪co β) α β where
  coe f := f.toFun
  coe_injective' | ⟨⟨_, _⟩, _⟩, ⟨⟨_, _⟩, _⟩, rfl => rfl
  injective' f := f.injective
  btw_apply_iff f := f.btw_apply_iff'

instance (priority := low) [Btw α] [Btw β] [CircularOrderEmbeddingClass F α β] :
    CircularOrderHomClass F α β where
  btw_apply _ := (btw_apply_iff _).2

structure CircularOrderIso (α β : Type*) [Btw α] [Btw β] extends α ≃ β where
  btw_apply_iff' {a b c : α} : btw (toEquiv a) (toEquiv b) (toEquiv c) ↔ btw a b c

class CircularOrderIsoClass (F : Type*) (α β : outParam (Type*)) [Btw α] [Btw β]
    extends EquivLike F α β where
  btw_apply_iff (f : F) {a b c : α} : btw (f a) (f b) (f c) ↔ btw a b c

instance (priority := low) [Btw α] [Btw β] [i : CircularOrderIsoClass F α β] :
    CircularOrderEmbeddingClass F α β where
  btw_apply_iff := i.btw_apply_iff

