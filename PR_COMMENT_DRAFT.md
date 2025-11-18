# Draft PR Comment for Sperner's Lemma

---

## Comment for GitHub PR Thread:

### ⚠️ Work in Progress - Blocking Dependencies

Hi reviewers,

This PR implements Sperner's lemma but is **intentionally incomplete** due to missing infrastructure in mathlib4. I'm converting this to a **Draft PR** to signal the WIP status clearly.

#### Blocking Issue

The proof requires **`SimplicialComplex.boundary` API** which doesn't currently exist. Specifically:
- Construction of the boundary complex of a simplicial complex
- Relationship between faces of a complex and faces of its boundary  
- Dimensional reduction lemmas for boundary traversal

Without this, the inductive step of `strong_sperner` cannot be completed.

#### Current Status

**✅ Complete:**
- All definitions (`IsSpernerColoring`, `IsPanchromatic`, `IsAlmostPanchromatic`)
- Basic helper lemmas (`panchromatic_unique_color`, `boundary_almost_is_lower_dim_panchromatic`)
- Base case of `strong_sperner` (dimension 0)
- Final theorem `sperner` (follows from `strong_sperner`)

**⚠️ Blocked with `sorry` placeholders:**
- `almost_panchromatic_card`: Needs stronger cardinality/injectivity lemmas
- `almost_panchromatic_containment`: **Requires boundary API**
- `strong_sperner` inductive step: **Requires boundary API**

All `sorry` statements include detailed inline comments explaining what's needed.

#### Purpose of This PR

1. **Document** the exact structure needed for Sperner's lemma
2. **Identify** precisely what infrastructure is missing
3. **Provide** a roadmap for completion once dependencies are resolved
4. **Request feedback** on the proof approach and strategy

#### Questions for Reviewers

1. Does the overall approach make sense given mathlib4's current SimplicialComplex API?
2. Should I first work on adding the `boundary` construction before continuing this proof?
3. Are there alternative approaches that don't require boundary complex operations?
4. Would it be valuable to split this into: (a) boundary API PR, (b) Sperner lemma PR?

#### Next Steps

Once I get feedback on the approach, I can either:
- Build the required `SimplicialComplex.boundary` infrastructure first
- Adjust the proof strategy if there's a better approach
- Keep this as documentation until someone else can tackle the boundary API

Thanks for reviewing! Let me know what you think.

---

**Files modified:**
- `Mathlib/Combinatorics/Sperner.lean`: Main file with definitions and proofs
- `Mathlib/Analysis/Convex/SimplicialComplex/Boundary.lean`: Placeholder for boundary API

**Related Issue:** #25231 (Sperner's lemma)

