import Mathlib.Data.FunLike.Equiv
import Mathlib.Logic.Equiv.Defs

variable {α β :Type*}
structure MyHom (α β :Type*) where
  toFun : α → β

class MyHomClass (T:Type*) (α β: outParam Type*) [FunLike T α β]
namespace MyHom
instance instFunLike : FunLike (MyHom α β) α β where
  coe := MyHom.toFun
  coe_injective' := fun f g h => by cases f; cases g; congr

instance instMyHomClass : MyHomClass (MyHom α β) α β where
end MyHom
structure MyEquiv (α β:Type*) extends α ≃ β, MyHom α β where
  someField : True

class MyEquivClass (T:Type*) (α β: outParam Type*) extends EquivLike T α β, MyHomClass T α β where
  someField' : ∀ (f:T),True

namespace MyEquiv
instance instMyEquivClass : MyEquivClass (MyEquiv α β) α β := {({
  coe := fun f => f.toFun
  inv := fun f => f.invFun
  left_inv := fun f => f.left_inv
  right_inv := fun f => f.right_inv
  coe_injective' := fun f g h => by cases f; cases g; congr; simp_all} : EquivLike (MyEquiv α β) α β) with
  someField' := fun f => f.someField
}

-- -/
end MyEquiv

structure CoolHom (α β :Type*) extends MyHom α β

class CoolHomClass (T:Type*) (α β: outParam Type*) [FunLike T α β] extends MyHomClass T α β

namespace CoolHom
instance instFunLike : FunLike (CoolHom α β) α β where
  coe := fun f => f.toFun
  coe_injective' := fun f g h => by cases f; cases g; congr; apply DFunLike.coe_injective'; exact h

instance instCoolHomClass : CoolHomClass (CoolHom α β) α β where
end CoolHom


structure CoolEquiv (α β :Type*) extends MyEquiv α β, CoolHom α β

class CoolEquivClass (T:Type*) (α β :outParam Type*)
  extends EquivLike T α β, CoolHomClass T α β where
  someField' : ∀ (f:T), True -- copy someField from MyEquivClass, but not via inheritance?


-- tell it later how to get to MyEquiv? i'm guessing?
instance CoolEquivClass.toMyEquivClass {T:Type*} {α β :outParam Type*} [self:CoolEquivClass T α β] : MyEquivClass T α β := {
  CoolEquivClass.toEquivLike with
  someField' := CoolEquivClass.someField'
}
#print CoolEquivClass
#print CoolEquivClass.toCoolHomClass
#print CoolEquivClass.toMyEquivClass

namespace CoolEquiv

instance instCoolEquivClass : CoolEquivClass (CoolEquiv α β) α β := { ({
    coe := fun f => f.toFun
    inv := fun f => f.invFun
    left_inv := fun f => f.left_inv
    right_inv := fun f => f.right_inv
    coe_injective' := fun f g h _ => by
      unhygienic cases f; unhygienic cases g; congr; simp_all;
      cases toMyEquiv; cases toMyEquiv_1; congr
  }:EquivLike (CoolEquiv α β) α β) with
  someField' := fun f => f.someField
}
