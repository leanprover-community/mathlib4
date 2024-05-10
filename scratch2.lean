set_option autoImplicit false
set_option relaxedAutoImplicit false

universe w w₁ w₂ w₃ v v₁ v₂ v₃ u u₁ u₂ u₃

class Quiver (V : Type u) where
Hom : V → V → Type v

variable {α : Type w}

set_option trace.Elab.step true in
variable [Quiver α]

infixr:10 " ⟶ " => Quiver.Hom

structure Opposite (α : Type w) :=
  op :: unop : α

notation:max α "ᵒᵖ" => Opposite α

open Opposite

variable {C : Type u₁}

variable [Quiver.{v₁} C]

instance Quiver.opposite {V} [Quiver V] : Quiver Vᵒᵖ :=
  ⟨fun a b => (unop b ⟶ unop a)ᵒᵖ⟩

-- set_option trace.Meta.isDefEq true in
-- set_option trace.Meta.synthInstance true in
#synth Quiver Cᵒᵖ
