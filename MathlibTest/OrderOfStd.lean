module
import Mathlib.Order.Std

namespace PreorderFromLE

def X := Nat deriving LE, Std.IsPreorder
instance h : Preorder X := .ofStd X {}
example : h.toLE = instLEX := rfl
example {a b : X} : h.lt a b ↔ instLEX.le a b ∧ ¬instLEX.le b a := Iff.rfl

end PreorderFromLE

namespace PreorderFromLELT

def X := Nat deriving LE, LT, Std.LawfulOrderLT, Std.IsPreorder
attribute [irreducible] instLEX instLTX
instance h : Preorder X := .ofStd X {}
example : h.toLE = instLEX := rfl
example : h.toLT = instLTX := rfl

end PreorderFromLELT

namespace PreorderFromOrd

def X := Nat deriving Ord, Std.TransOrd
instance h : Preorder X := .ofStd X {}
example {a b} : h.le a b ↔ (instOrdX.compare a b).isLE := Iff.rfl
example {a b} : h.lt a b ↔ (instOrdX.compare a b).isLE ∧ ¬(instOrdX.compare b a).isLE := Iff.rfl

end PreorderFromOrd

namespace PartialOrderFromLE

def X := Nat deriving LE, Std.IsPartialOrder
instance h : PartialOrder X := .ofStd X {}
example : h.toLE = instLEX := rfl

end PartialOrderFromLE

namespace LinearOrderFromLE

def X := Nat deriving LE, Std.IsLinearOrder, DecidableLE
instance h : LinearOrder X := .ofStd X {}
example : h.toLE = instLEX := rfl
example {a b} : h.toOrd.compare a b = compareOfLessAndEq a b := rfl

end LinearOrderFromLE

-- If `DecidableEq`, `DecidableLT`, `Min` and `Max` instances exist, they are preserved.
namespace DecidableMinMaxInstances

def X := Nat
deriving
  LE, LT, Std.LawfulOrderLT, Std.IsLinearOrder,
  DecidableLE, DecidableEq, DecidableLT,
  Min, Max, Std.LawfulOrderLeftLeaningMin, Std.LawfulOrderLeftLeaningMax
attribute [irreducible] instDecidableEqX instDecidableLTX instMinX instMaxX
instance h : LinearOrder X := .ofStd X {}
example : h.toDecidableEq = instDecidableEqX := rfl
example : h.toDecidableLT = instDecidableLTX := rfl
example : h.toMin = instMinX := rfl
example : h.toMax = instMaxX := rfl

end DecidableMinMaxInstances

-- Generate `LE` from `Ord`
namespace FromOrd

def X := Nat deriving Ord, Std.TransOrd, Std.LawfulEqOrd
attribute [irreducible] instOrdX
instance h : LinearOrder X := .ofStd X
example : h.toOrd = instOrdX := rfl
example {a b} : h.le a b ↔ (instOrdX.compare a b).isLE := Iff.rfl
example {a b} : h.lt a b ↔ (instOrdX.compare a b).isLE ∧ ¬(instOrdX.compare b a).isLE := Iff.rfl
example : h.toMin = .leftLeaningOfLE X := rfl
example : h.toMax = .leftLeaningOfLE X := rfl

end FromOrd

-- Transfer the properties of `Ord` over to the properties of `LE`
namespace FromLEOrdViaOrd

def X := Nat deriving LE, Ord, Std.TransOrd, Std.LawfulOrderOrd, Std.LawfulEqOrd
attribute [irreducible] instLEX instOrdX
instance h : LinearOrder X := .ofStd X
example : h.toLE = instLEX := rfl
example : h.toOrd = instOrdX := rfl

end FromLEOrdViaOrd

-- Transfer the properties of `LE` over to the properties of `Ord`
namespace FromLEOrdViaLE

def X := Nat deriving LE, Std.IsLinearOrder, DecidableLE, Ord, Std.LawfulOrderOrd
attribute [irreducible] instLEX instDecidableLEX instOrdX
instance h : LinearOrder X := .ofStd X
example : h.toLE = instLEX := rfl
example : h.toDecidableLE = instDecidableLEX := rfl
example : h.toOrd = instOrdX := rfl

end FromLEOrdViaLE
