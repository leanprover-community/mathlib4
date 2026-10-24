import Mathlib.Data.QuotType

namespace Quot

variable {α} {r : α → α → Prop} (a : α)

/-- info: mkQ : α → Quot r -/
#guard_msgs in #check (((mkQ : _) : _ → _) : _ → Quot r)

/-- info: mkQ : α → Quot r -/
#guard_msgs in #check mkQ (Q := Quot r)

/-- info: ⟦a⟧ : Quot r -/
#guard_msgs in #check ((⟦a⟧ : _) : Quot r)

end Quot

namespace Quotient

variable {α} [s : Setoid α] (a : α) (p : α → Prop) (x : Subtype p)

/-- info: mkQ : α → Quotient s -/
#guard_msgs in #check (((mkQ : _) : _ → _) : _ → Quotient s)

/-- info: mkQ : α → Quotient s -/
#guard_msgs in #check mkQ (Q := Quotient s)

/-- info: ⟦a⟧ : Quotient s -/
#guard_msgs in #check ((⟦a⟧ : _) : Quotient s)

/-- info: mkQ : α → Quotient s -/
#guard_msgs in #check (((mkQ' : _) : _ → _) : α → _)

/-- info: ⟦a⟧ : Quotient s -/
#guard_msgs in #check (⟦a⟧' : _)

/-- info: ⟦x.val⟧ : Quotient s -/
#guard_msgs in #check ((⟦x⟧ : _) : Quotient s)

-- Is there any way to make it work?
-- #check ((mkQ x : _) : Quotient s)

/--
info: have this := Exists.intro ⟦a⟧ rfl;
this : ∃ y, id y = ⟦id a⟧
-/
#guard_msgs in #check show ∃ y, id y = ⟦id a⟧' from ⟨⟦a⟧, rfl⟩

end Quotient

class HintClass (A B : Type*) where
  r : B → B → Prop

variable (A B : Type*) [HintClass A B] (b : B)

def Q := Quot (α := B) (HintClass.r A)

instance : QuotType (Q A B) B (HintClass.r A) where

/--
info: let this := ⋯;
mkQ : B → Q A B
-/
#guard_msgs in #check let : QuotTypeOut (Q A B) B (HintClass.r A) := ⟨⟩; (mkQ' : B → _)
