import Mathlib.GroupTheory.Generators

/-!
# Scratch: the hom argument of `Generators.map` — EXPLICIT vs IMPLICIT

Should `map` take `(f : G →* H)` explicitly, or `{f : G →* H}` implicitly,
pinned by `hf : Function.Surjective f`?

The question is fair: `hf` mentions `f`, so Lean can in principle recover
`f` and the caller never types it. Test 1 shows that working. Tests 2 and 3
show where it stops working, and why.
-/

open Function

namespace Group.Generators

variable {G H K α : Type*} [Group G] [Group H] [Group K]

/-! ## The twins

Identical bodies. The only difference is the bracket on `f`. -/

/-- EXPLICIT: the caller names the hom. -/
def mapExpl (P : Group.Generators G α) (f : G →* H) (hf : Surjective f) :
    Group.Generators H α where
  val := f ∘ P.val
  closure_eq_top := by
    rw [Set.range_comp, ← MonoidHom.map_closure, P.closure_eq_top,
      Subgroup.map_top_of_surjective f hf]

/-- IMPLICIT: the caller supplies only the proof, and `f` is read off its type. -/
def mapImpl (P : Group.Generators G α) {f : G →* H} (hf : Surjective f) :
    Group.Generators H α where
  val := f ∘ P.val
  closure_eq_top := by
    rw [Set.range_comp, ← MonoidHom.map_closure, P.closure_eq_top,
      Subgroup.map_top_of_surjective f hf]

/-! ## Test 1 — the hypothesis is already in context, stated about the bundled hom

Both work. This is the case that makes IMPLICIT look free: `hf`'s type is
literally `Surjective ⇑f`, so unifying `Surjective ⇑?f` against it assigns
`?f := f` on the spot. -/

example (P : Group.Generators G α) (f : G →* H) (hf : Surjective f) :
    Group.Generators H α :=
  P.mapExpl f hf

example (P : Group.Generators G α) (f : G →* H) (hf : Surjective f) :
    Group.Generators H α :=
  P.mapImpl hf

/-! ## Test 2 — the hom is a composite, the proof is about the underlying functions

`Surjective.comp` concludes about `⇑g ∘ ⇑f`, a bare function composition.
The hom you want to transport along is `g.comp f`, a bundled `G →* K`.
Those two are definitionally equal but not syntactically equal.

EXPLICIT: the caller writes the hom, so the only thing left to check is
`Surjective ⇑(g.comp f) =?= Surjective (⇑g ∘ ⇑f)`, and defeq checking
unfolds the coercion. Works. -/

example (P : Group.Generators G α) (f : G →* H) (hf : Surjective f)
    (g : H →* K) (hg : Surjective g) :
    Group.Generators K α :=
  P.mapExpl (g.comp f) (hg.comp hf)

/-! IMPLICIT has no hom to check against. It must SOLVE `⇑?f` from
`⇑g ∘ ⇑f` by unification, and a coercion applied to an unknown is not a
pattern unification can invert.

EXPECTED ERROR below. -/

example (P : Group.Generators G α) (f : G →* H) (hf : Surjective f)
    (g : H →* K) (hg : Surjective g) :
    Group.Generators K α :=
  P.mapImpl (hg.comp hf)

/-! ## Test 3 — the escape hatch, priced

IMPLICIT is recoverable: name the argument. The cost is that the caller
types the hom anyway, plus `(f := )`, at exactly the sites where the
proof did not arrive pre-shaped. -/

example (P : Group.Generators G α) (f : G →* H) (hf : Surjective f)
    (g : H →* K) (hg : Surjective g) :
    Group.Generators K α :=
  P.mapImpl (f := g.comp f) (hg.comp hf)

end Group.Generators
