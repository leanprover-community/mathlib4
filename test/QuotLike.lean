import Mathlib.Data.QuotLike

namespace Quot

variable {α} {r : α → α → Prop} (a : α)

/-- info: mkQ : α → Quot r -/
#guard_msgs in #check (((mkQ : _) : _ → _) : _ → Quot r)

/-- info: mkQ : α → Quot r -/
#guard_msgs in #check mkQ (Q := Quot r)

/-- info: ⟦a⟧ : Quot r -/
#guard_msgs in #check ((⟦a⟧ : _) : Quot r)

/-- info: mkQ : α → Quot r -/
#guard_msgs in #check (mkQ_ r : _)

/-- info: ⟦a⟧ : Quot r -/
#guard_msgs in #check (⟦a⟧_ r : _)

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

/--
info: let_fun this := Exists.intro ⟦a⟧ rfl;
this : ∃ y, id y = ⟦id a⟧
-/
#guard_msgs in #check show ∃ y, id y = ⟦id a⟧' from ⟨⟦a⟧, rfl⟩

-- Is there any way to make it work?
-- #check ((mkQ x : _) : Quotient s)

end Quotient
