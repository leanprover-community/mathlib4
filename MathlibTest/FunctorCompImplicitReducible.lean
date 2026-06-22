/-
Regression test for the `[instance_reducible]` / `[implicit_reducible]` tier split
introduced in https://github.com/leanprover/lean4/pull/13637.

Adapted from Sébastien Gouëzel's MWE:
  https://leanprover.zulipchat.com/#narrow/channel/113488-general/topic/backward.2EisDefEq.2ErespectTransparency/near/592439262

The invariant: tagging `Functor.comp` `[implicit_reducible]` must NOT corrupt
type class search. The two instances `SGMonoidal (F ⋙ (G ⋙ H))` and
`SGMonoidal ((F ⋙ G) ⋙ H)` are mathematically distinct and must remain so.

Pre-split, the unified `[implicit_reducible]` would have collapsed them at
`.instances` transparency, breaking instance synthesis. Post-split,
`[implicit_reducible]` is the narrower (value-defeq-only) tier and is safe;
`[instance_reducible]` is the TC tier and would (correctly, by design)
reproduce the corruption.
-/

import Mathlib.CategoryTheory.Monoidal.Functor

open CategoryTheory

namespace MathlibTest.SGMonoidal_DefEq

variable {A : Type*} [Category A] {B : Type*} [Category B]
  {C : Type*} [Category C] {D : Type*} [Category D]
  (F : A ⥤ B) (G : B ⥤ C) (H : C ⥤ D)

-- Sanity check: associativity of `⋙` itself holds by `rfl`.
example : F ⋙ (G ⋙ H) = (F ⋙ G) ⋙ H := rfl

class SGMonoidal (F : A ⥤ B) where
  n : ℕ

instance [hF : SGMonoidal F] [hG : SGMonoidal G] : SGMonoidal (F ⋙ G) where
  n := 2 ^ hF.n + hG.n

variable [hF : SGMonoidal F] [hG : SGMonoidal G] [hH : SGMonoidal H]

/-! ### Variant 1: no extra attribute on `Functor.comp`

TC search distinguishes the two instances; `rfl` rightfully fails. -/

set_option pp.mvars.anonymous false in
/--
error: Type mismatch
  rfl
has type
  ?_ = ?_
but is expected to have type
  SGMonoidal.n (F ⋙ G ⋙ H) = SGMonoidal.n ((F ⋙ G) ⋙ H)
-/
#guard_msgs in
example :
    letI : SGMonoidal ((F ⋙ G) ⋙ H) := inferInstance
    SGMonoidal.n (F ⋙ (G ⋙ H)) = SGMonoidal.n ((F ⋙ G) ⋙ H) := rfl

/-! ### Variant 2: `[implicit_reducible]` on `Functor.comp` (narrower tier)

Still safe: the narrower tier does not feed into TC-search defeq, so the two
instances remain distinct. -/

section ImplicitReducible

set_option pp.mvars.anonymous false in
/--
error: Type mismatch
  rfl
has type
  ?_ = ?_
but is expected to have type
  SGMonoidal.n (F ⋙ G ⋙ H) = SGMonoidal.n ((F ⋙ G) ⋙ H)
-/
#guard_msgs in
example :
    letI : SGMonoidal ((F ⋙ G) ⋙ H) := inferInstance
    SGMonoidal.n (F ⋙ (G ⋙ H)) = SGMonoidal.n ((F ⋙ G) ⋙ H) := rfl

end ImplicitReducible

/-! ### Variant 3: `[instance_reducible]` on `Functor.comp` (TC tier)

If `Functor.comp` is instance-reducible, type class synthesis will accept the locally
defined `SGMonoidal` instance because its type is definitionally equal to the expected type at
instance transparency.

If a future change accidentally made `[instance_reducible]` even narrower, this test would
notice.

-/

section InstanceReducible

set_option allowUnsafeReducibility true
attribute [local instance_reducible] Functor.comp

example :
    letI : SGMonoidal ((F ⋙ G) ⋙ H) := inferInstance
    SGMonoidal.n (F ⋙ (G ⋙ H)) = SGMonoidal.n ((F ⋙ G) ⋙ H) := by
  rfl

end InstanceReducible

end MathlibTest.SGMonoidal_DefEq
