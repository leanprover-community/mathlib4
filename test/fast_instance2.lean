import Mathlib

/-! Testing an extrememly deep class -/

variable {α : Type*} [LinearOrderedField α]

structure Wrapped (α : Type*) where
  val : α

theorem val_injective : Function.Injective (Wrapped.val (α := α))
  | ⟨_⟩, ⟨_⟩, rfl => rfl

instance : Zero (Wrapped α) where zero := ⟨0⟩

instance : One (Wrapped α) where one := ⟨1⟩

instance : Add (Wrapped α) where add := fun ⟨m⟩ ⟨n⟩ => ⟨m + n⟩

instance : Mul (Wrapped α) where mul := fun ⟨m⟩ ⟨n⟩ => ⟨m * n⟩

instance : Neg (Wrapped α) where neg m := ⟨Neg.neg m.1⟩

instance : Sub (Wrapped α) where sub m n := ⟨Sub.sub m.1 n.1⟩

instance : Pow (Wrapped α) ℕ where pow m n := ⟨Pow.pow m.1 n⟩

instance : SMul ℕ (Wrapped α) where smul n m := ⟨SMul.smul n m.1⟩

instance : SMul ℤ (Wrapped α) where smul n m := ⟨SMul.smul n m.1⟩

instance : SMul ℚ≥0 (Wrapped α) where smul n m := ⟨SMul.smul n m.1⟩

instance : SMul ℚ (Wrapped α) where smul n m := ⟨SMul.smul n m.1⟩

instance : NatCast (Wrapped α) where natCast n := ⟨NatCast.natCast n⟩

instance : IntCast (Wrapped α) where intCast n := ⟨IntCast.intCast n⟩

instance : NNRatCast (Wrapped α) where nnratCast n := ⟨NNRatCast.nnratCast n⟩

instance : RatCast (Wrapped α) where ratCast n := ⟨RatCast.ratCast n⟩

instance : Inv (Wrapped α) where inv m := ⟨Inv.inv m.1⟩

instance : Div (Wrapped α) where div m n := ⟨Div.div m.1 n.1⟩

instance : Pow (Wrapped α) ℤ where pow m n := ⟨Pow.pow m.1 n⟩

instance : Sup (Wrapped α) where sup s t := ⟨Sup.sup s.1 t.1⟩

instance : Inf (Wrapped α) where inf s t := ⟨Inf.inf s.1 t.1⟩

open Wrapped

instance Wrapped.instField : Field (Wrapped α) :=
  Function.Injective.field (β := α) val val_injective rfl rfl (fun _ _ => rfl)
  (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
  (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
  (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)

def slowInstance : LinearOrderedField (Wrapped α) :=
  Function.Injective.linearOrderedField (α := α) val val_injective rfl rfl (fun _ _ => rfl)
  (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
  (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
  (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)

set_option trace.Elab.fast_instance true in
def fastInstance : LinearOrderedField (Wrapped α) := fast_instance%
  Function.Injective.linearOrderedField (α := α) val val_injective rfl rfl (fun _ _ => rfl)
  (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
  (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
  (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)

/--
info: def slowInstance.{u_1} : {α : Type u_1} → [inst : LinearOrderedField α] → LinearOrderedField (Wrapped α) :=
fun {α} [inst : LinearOrderedField α] =>
  @Function.Injective.linearOrderedField α (Wrapped α) (@instZeroWrapped α inst) (@instOneWrapped α inst)
    (@instAddWrapped α inst) (@instMulWrapped α inst) (@instNegWrapped α inst) (@instSubWrapped α inst)
    (@instPowWrappedNat α inst) (@instSMulNatWrapped α inst) (@instSMulIntWrapped α inst) (@instSMulNNRatWrapped α inst)
    (@instSMulRatWrapped α inst) (@instNatCastWrapped α inst) (@instIntCastWrapped α inst)
    (@instNNRatCastWrapped α inst) (@instRatCastWrapped α inst) (@instInvWrapped α inst) (@instDivWrapped α inst)
    (@instPowWrappedInt α inst) (@instSupWrapped α inst) (@instInfWrapped α inst) (@val α) ⋯ inst ⋯ ⋯ ⋯ ⋯ ⋯ ⋯ ⋯ ⋯ ⋯ ⋯ ⋯
    ⋯ ⋯ ⋯ ⋯ ⋯ ⋯ ⋯ ⋯ ⋯
-/
#guard_msgs in
set_option pp.explicit true in
#print slowInstance

/--
info: def fastInstance.{u_1} : {α : Type u_1} → [inst : LinearOrderedField α] → LinearOrderedField (Wrapped α) :=
fun {α} [inst : LinearOrderedField α] =>
  @LinearOrderedField.mk (Wrapped α)
    (@LinearOrderedCommRing.mk (Wrapped α)
      (@LinearOrderedRing.mk (Wrapped α)
        (@StrictOrderedRing.mk (Wrapped α)
          (@DivisionRing.toRing (Wrapped α) (@Field.toDivisionRing (Wrapped α) (@instField α inst)))
          (@PartialOrder.mk (Wrapped α)
            (@Preorder.mk (Wrapped α)
              (@LE.mk (Wrapped α) fun x y =>
                @LE.le α
                  (@Preorder.toLE α
                    (@PartialOrder.toPreorder α
                      (@OrderedAddCommGroup.toPartialOrder α
                        (@StrictOrderedRing.toOrderedAddCommGroup α
                          (@LinearOrderedRing.toStrictOrderedRing α
                            (@LinearOrderedCommRing.toLinearOrderedRing α
                              (@LinearOrderedField.toLinearOrderedCommRing α inst)))))))
                  (@val α x) (@val α y))
              (@LT.mk (Wrapped α) fun x y =>
                @LT.lt α
                  (@Preorder.toLT α
                    (@PartialOrder.toPreorder α
                      (@OrderedAddCommGroup.toPartialOrder α
                        (@StrictOrderedRing.toOrderedAddCommGroup α
                          (@LinearOrderedRing.toStrictOrderedRing α
                            (@LinearOrderedCommRing.toLinearOrderedRing α
                              (@LinearOrderedField.toLinearOrderedCommRing α inst)))))))
                  (@val α x) (@val α y))
              ⋯ ⋯ ⋯)
            ⋯)
          ⋯ ⋯ ⋯ ⋯)
        (@Min.mk (Wrapped α) fun x x_1 => @Inf.inf (Wrapped α) (@instInfWrapped α inst) x x_1)
        (@Max.mk (Wrapped α) fun x x_1 => @Sup.sup (Wrapped α) (@instSupWrapped α inst) x x_1)
        (@Ord.mk (Wrapped α) fun a b =>
          @compare α
            (@LinearOrder.toOrd α
              (@LinearOrderedRing.toLinearOrder α
                (@LinearOrderedCommRing.toLinearOrderedRing α (@LinearOrderedField.toLinearOrderedCommRing α inst))))
            (@val α a) (@val α b))
        ⋯
        (@LinearOrder.decidableLE (Wrapped α)
          (@LinearOrder.lift (Wrapped α) α
            (@LinearOrderedRing.toLinearOrder α
              (@LinearOrderedCommRing.toLinearOrderedRing α (@LinearOrderedField.toLinearOrderedCommRing α inst)))
            (@instSupWrapped α inst) (@instInfWrapped α inst) (@val α) ⋯ ⋯ ⋯))
        (@LinearOrder.decidableEq (Wrapped α)
          (@LinearOrder.lift (Wrapped α) α
            (@LinearOrderedRing.toLinearOrder α
              (@LinearOrderedCommRing.toLinearOrderedRing α (@LinearOrderedField.toLinearOrderedCommRing α inst)))
            (@instSupWrapped α inst) (@instInfWrapped α inst) (@val α) ⋯ ⋯ ⋯))
        (@LinearOrder.decidableLT (Wrapped α)
          (@LinearOrder.lift (Wrapped α) α
            (@LinearOrderedRing.toLinearOrder α
              (@LinearOrderedCommRing.toLinearOrderedRing α (@LinearOrderedField.toLinearOrderedCommRing α inst)))
            (@instSupWrapped α inst) (@instInfWrapped α inst) (@val α) ⋯ ⋯ ⋯))
        ⋯ ⋯ ⋯)
      ⋯)
    (@instInvWrapped α inst) (@instDivWrapped α inst) ⋯
    (@Field.zpow (Wrapped α) (@instField α inst))
    (@Field.nnqsmul (Wrapped α) (@instField α inst))
    ⋯ ⋯
    (@Field.qsmul (Wrapped α) (@instField α inst))
    ⋯
-/
-- #guard_msgs in
set_option pp.explicit true in
#print fastInstance

#print LinearOrderedField.mk
