module

public import Mathlib.Tactic.Inclusion.Core.ToSet

set_option linter.style.header false

@[expose] public section

namespace Inclusion

/-- A procedure for covering a represented set by sufficiently many refinements. -/
class Splitter (Iα α : Type*) [ToSet Iα α] where
  /-- The cover obtained by refining a represented set to depth `n`. -/
  cover (n : ℕ) : Cover.{0} Iα α

end Inclusion
