# Geometry work — parking notes (resume-cold handoff)

Purpose: enough context to pick this up months later without re-deriving the reasoning.
Branch: `idontgetoutmuch/mathlib4`, `smooth-exp-Lie-V`. Toolchain seen this session:
Lean `v4.30.0-rc2` (an rc — relevant; see flow-axiom / kernel notes below).

--------------------------------------------------------------------------------
## 1. What got done this session (status of each artifact)

PATCHES (apply with `git apply` from repo root; verified to apply cleanly to branch HEAD
at time of creation — if local files drifted, hand-merge rather than overwrite):

- `0001-principal-bundle-smooth-equivariant-triv.patch`  (FakeFormIII.lean)
  Generalizes `equivariant_localTriv` to the whole trivialization source, adds
  `smooth_localTriv` field, threads membership through `is_transitive`, and replaces the
  `contMDiffAt_gaugeMap` sorry with a full proof.  STATUS: drafted, NOT compile-verified.

- `0002-frame-bundle-instance-smooth-localTriv.patch`  (FrameBundle.lean)
  Adds `intertwining_reverse_at`, a `UnitsTransfer` section with `ContMDiffAt.units_of_val`,
  generalizes the instance's `equivariant_localTriv`, adds the `smooth_localTriv` field proof.
  STATUS: drafted. Top compile risk: the name of the lemma that an atlas trivialization of a
  `ContMDiffVectorBundle` is `ContMDiffOn` on its source (written `e'.contMDiffOn` — verify
  with `exact?`), and the `units_of_val` final `rfl` (fallback `simp [extChartAt,...]` noted
  inline).

- `0003-fix-kernel-letI-tangent-instances.patch`  (FrameBundle.lean)
  Fixes a KERNEL error in the pre-existing `FrameBundle` Opens definition (lines ~150–250):
  `haveI : NormedAddCommGroup (TangentSpace I _.proj) := by change ...; infer_instance`
  was getting opaquely abstracted into `_aux` definitions, so the kernel saw
  `NormedSpace ℝ E` vs `NormedSpace ℝ (TangentSpace I _.proj)` and rejected it.
  Fix: `letI ... := inferInstanceAs ...` + explicit pinning of the `NormedSpace` instance.
  NOTE: this region predates my patches; it broke on the rc toolchain. If `git apply` fails
  it's because local file drifted — make the 2 edits by hand (both bullets of `is_open'`).
  STATUS: the user reported `letI` ALONE still failed (binder still named `this`); see §4.

- `0004-fix-false-flow-axiom-explie.patch`  (ExpLie.lean)
  IMPORTANT: the axiom `contMDiff_flow_like` as originally stated was FALSE (vacuous) — it
  dropped the initial-condition pinning `Φ 0 x = x`, so for X=0 any discontinuous Φ with
  constant curves satisfied the hypotheses, letting it prove the flow is ContMDiff hence
  continuous → contradiction. Patch adds `hΦ₀ : ∀ x, Φ 0 x = x` plus `[T2Space M]
  [BoundarylessManifold IG M]`, rewrites the doc with the counterexample, moves `expLie_zero`
  above `contMDiff_expLie`, and fixes `contMDiff_expLie` to use the corrected flow
  `Φ t (g,v) = (g * expLie (t•v), v)`. STATUS: drafted, NOT verified.

- `*.patched.lean` — full post-patch copies of ExpLie / FakeFormIII / FrameBundle, as
  fallback if patches don't apply.

NEW FILE:
- `GradedDiffLieAlg.lean` — the abstract graded-differential-Lie-algebra layer + Bianchi.
  See §2. This is the cleanest, most self-contained thing produced and the best resume point.

--------------------------------------------------------------------------------
## 2. The fake-Bianchi layer (`GradedDiffLieAlg.lean`) — the main deliverable

Strategy ("fake forms", per the Lie-algebra-valued 1-form precedent): assume the algebraic
laws genuine 𝔤-valued forms satisfy, as a typeclass interface, and prove Bianchi against it.
The concrete `Ω* ⊗ 𝔤` construction becomes a deferred INSTANCE.

Class `GradedDiffLieAlg (A : ℕ → Type*)` over ℝ. Fields (= Tu's theorems, used as interface):
- `d` / `d_comp_d`  — exterior derivative, d²=0.
- `wb (h : p+q=n)`  — bracket-wedge, SMART CONSTRUCTOR taking a degree proof (avoids dependent
  transport: every law states both sides in one `A n`, no `cast`).
- `d_wb`        — graded Leibniz.            (Tu Prop 21.6)
- `wb_antisymm` — graded antisymmetry.       (Tu Prop 21.5)
- `wb_wb_self`  — `[[ω∧ω]∧ω]=0` for deg-1 ω. (Tu Problem 21.5)
Then `curvature ω = dω + ½[ω∧ω]` and `theorem bianchi : dΩ = [Ω∧ω]`. (Tu §30 part iii / (30.2))

Extension `GradedDiffAssocAlg extends GradedDiffLieAlg`: adds associative product `mw`
(matrix-wedge) and `wb_eq_graded_comm` ([α∧β] = α⌣β − (−1)^{pq} β⌣α, Tu Prop 21.7).
Then `bianchi_matrix : dΩ = Ω⌣ω − ω⌣Ω` (Tu (30.3)) — the frame-bundle / matrix form.

KEY DESIGN DECISIONS (and WHY — this is the part that evaporates):
- Coefficients are ℝ, not an abstract field. The objects are real; abstract 𝕜 buys nothing
  for GR. Resolved a 𝕜-vs-ℝ mess: keep the abstract algebra layer field-agnostic in spirit,
  but the manifold/forms layer is ℝ. (Complex/Riemann-surface geometry is a SEPARATE later
  extension via `ModelWithCorners ℂ` + bidegree (∂,∂̄); 𝕜-genericity in the base layer does
  NOT buy it, so don't carry 𝕜 for that reason.)
- NO abstract graded-Jacobi field. Originally had one; feeding 3 equal ω's into it forces
  −3X=0, hence a spurious `CharZero`/`3≠0` hypothesis. That factor-3 is an ARTIFACT of the
  abstract route. The honest fact lives one level down: in `Ω*⊗𝔤`, `[[ω∧ω]∧ω]=0` comes
  pointwise from ordinary Lie Jacobi (the factor 2 from `[ω∧ω]=2[ω,ω]` multiplies a quantity
  that is identically zero), DIVISION-FREE, any characteristic. So `wb_wb_self` is the single
  Jacobi consequence Bianchi needs, taken as a field, discharged in the instance.

OPEN compile-risk in `GradedDiffLieAlg.lean` (uncompiled):
- `bianchi` step `hdW`: the `module` call must unify two `wb _ (dω) ω` atoms carrying
  different `by omega` proofs of `2+1=3` (defeq by proof irrelevance, maybe not syntactic).
  Fallback: `show _ = _; congr 1` or `convert ... using 2` + `rfl` on degree goals.
- Same proof-irrelevance issue in `hRHS` and in `bianchi_matrix`.

--------------------------------------------------------------------------------
## 2b. CONVENTION (unified across Bleecker / Tu / Schuller) — decided this session

The three authors write ONE curvature identity; they differ only in (a) the factor of 2
(bracket vs matrix product) and (b) "altitude" (global object on P vs local representative on
a patch). Dictionary, confirmed against photographed pages of all three:

CURVATURE, three equivalent forms of the same object:
  Ω = dω + ½[ω,ω]        general group, bracket form   (Tu; Bleecker 2.2.4; KN)
  Ω = dω + ω 𝔸 ω         Schuller's bracket-wedge 𝔸, NO ½  (𝔸 bakes in the antisymmetrization)
  Ω = dω + ω ∧ ω         matrix group only, NO ½        (Bleecker 2.2.13)
Reconciliation (Bleecker 2.2.13, verbatim):  ω 𝔸 ω = ½[ω,ω] = ω ∧ ω  (last = matrix only).
The factor 2 lives in [ω∧ω](X,Y) = 2[ω(X),ω(Y)]; the ½ compensates. Schuller's 𝔸 and the
matrix ∧ omit it by definition.

BRACKET-AS-GRADED-COMMUTATOR (matrix Lie algebra), = the file's `wb_eq_graded_comm` field,
= Tu Prop 21.7, = Bleecker 2.2.12. CORRECT NOTATION (replaces the earlier bogus cup-product
glyph "⌣" I mistakenly used — that was the algebraic-topology cup product, WRONG here):
  [φ,ψ] = φ ∧ ψ − (−1)^{ij} ψ ∧ φ     (φ ∈ Λ^i, ψ ∈ Λ^j; ∧ = wedge forms, multiply matrices)
So in `GradedDiffAssocAlg`, `mw` = this matrix wedge ∧, NOT "⌣". Fix the docstring.

ALTITUDE distinction (Bleecker's suffices — this maps onto the Lean class/instance split!):
  Ω^ω  (superscript ω) = curvature OF the connection ω, the GLOBAL object on total space P,
        Λ²(P,𝔤). Bleecker keeps the ω explicit because he varies the connection (variational
        functionals). ←→ the ABSTRACT `GradedDiffLieAlg` layer / `bianchi`.
  Ω_u  (subscript u)  = LOCAL representative on patch U_u, = σ_u^*Ω^ω (pullback by local
        section σ_u). Physicists' field strength F. Carries a patch/gauge index.
        Transition law (Bleecker 2.2.14): Ω_v = Ad_{g_uv^{-1}} Ω_u, matrix: Ω_v = g_uv^{-1} Ω_u g_uv.
        ←→ the CONCRETE frame-bundle INSTANCE; and the gauge-transformation law already in
        FakeFormII (A' = g^{-1}Ag + g^{-1}dg) IS Bleecker's potential transition rule (1.2.3),
        with Ω_v = g^{-1}Ω_u g its field-strength version.

So: the file's two classes already mirror Bleecker exactly —
  `GradedDiffLieAlg`   (general, has the ½ in `curvature`)        = Bleecker 2.2.4 / Tu
  `GradedDiffAssocAlg` (matrix, uses ∧, no ½, via wb_eq_graded_comm) = Bleecker 2.2.13
BIANCHI: Bleecker 2.2.8 proof is line-for-line the file's `bianchi` (uses 2.1.3(1)=`wb_antisymm`
and 2.1.3(2)=`wb_wb_self`, the latter a CITED separate fact — matches our design). Stated both
ways: D^ω Ω^ω = 0  AND  dΩ^ω = [Ω^ω, ω]. Sign matches the file (positive).

RECOMMENDED naming when resuming: Schuller's 𝔸 glyph for the bracket-wedge operation if a
single clean symbol is wanted, BUT adopt Bleecker's Ω^ω / Ω_u altitude discipline because it
documents the class/instance boundary. Cite all three authors' numbers in docstrings.

--------------------------------------------------------------------------------
## 3. The big picture / roadmap (CORRECTED FRAMING — read this carefully)

GOAL CORRECTION (supersedes any earlier "upstreaming" framing in this doc): the aim is NOT to
contribute to Mathlib. Contribution is incidental, only if it happens to coincide. The actual
goals are two NEARLY-INDEPENDENT tracks (they share physics, not code):

- TRACK A — rewrite the Einstein equations in DIFFERENTIAL FORMS, for personal understanding
  and use. Concretely: take the standard index/component formulation (Levi-Civita Γ, Riemann,
  Ricci, Einstein tensor G_αβ, Bianchi, G_αβ = 8π T_αβ, signature +2 — the "page 7" of the
  user's GW lecture notes, Appendix A) and re-express it via coframe e^a, connection 1-forms
  ω^a_b, curvature 2-forms Ω^a_b, and the Einstein 3-form ε_abcd e^b ∧ Ω^{cd}.
  * `GradedDiffLieAlg.bianchi` IS the forms version of their Bianchi (A.2). Already done.
  * The coframe e^a IS the SOLDER FORM on the orthonormal frame bundle (see §3b). 
  * Vacuum (Ric=0, black holes) needs NO Lagrangian, NO stress-energy. Matter (white dwarfs/
    neutron stars) would add variational T_μν + relativistic hydro + equation of state — a
    whole extra theory; avoid unless wanted.

- TRACK B — use Carroll's Ch. 7 (Perturbation Theory & Gravitational Radiation) to DERIVE the
  PDEs and SOLVE them numerically (binary BH / NS). Does NOT depend on Track A being
  formalized — the PDEs come from Carroll's weak-field analysis directly.
  * Carroll Ch. 7 covers PRODUCTION too: linearized wave eqn → quadrupole formula
    (h ∝ Q̈_ij, pp.300-307) → energy loss (Ė ∝ ⟨Q⃛ Q⃛⟩) → inspiral chirp.
  * ACHIEVABLE end-to-end slice: forms/standard Einstein → linearize → wave eqn with source →
    quadrupole → energy-loss ODE → integrate → CHIRP WAVEFORM, validated vs the known chirp.
    This is an ODE integration, one-person-with-AI scale. (A working chirp visualizer was
    built this session, parameterized by m1,m2, leading-order Newtonian/quadrupole.)
  * MERGER + ringdown is the full-NR EPILOGUE: needs 3+1 (ADM→BSSN/Z4c), horizons, gauge,
    constraint damping. Carroll does NOT cover it. Reach it via an EXISTING code (GRChombo /
    Einstein Toolkit), don't rebuild. (Engrenage = spherical symmetry only, cannot do binaries;
    refs Alcubierre, Baumgarte–Shapiro, Gourgoulhon, LeVeque on page 1 of the GW notes.)
  * WENO reconnects here for the MATTER (NS) case (relativistic hydro shocks); NOT load-bearing
    for vacuum BBH. [WENO is a separate break-project, intentionally not detailed here.]

The full arc the user wants to traverse with AI help:
  abstract geometry → forms Einstein eqns → linearize → PDEs → solver → a SOLUTION.
  Achievable solo+AI up to the inspiral chirp; merger via existing code.

EINSTEIN exp shortcut (still valid, Track A plumbing): for G = (E→L[ℝ]E)ˣ the Lie exponential
IS NormedSpace.exp, which Mathlib has fully (`contDiff_exp`, `hasDerivAt_exp_smul_const`). So
the concrete frame-bundle exp does NOT need the general flow theorem (the C^k-dependence
analysis mountain; Winston Yin's FunSpace has only continuity/Lipschitz). Quarantined like the
(corrected) flow axiom.

--------------------------------------------------------------------------------
## 3a. MATHLIB UPSTREAM LANDSCAPE (investigated this session — affects what's worth building)

Since the goal is NOT upstreaming, this does not block anything — but it tells you which parts
are already being built upstream (don't duplicate) vs genuinely empty (your contribution).

CONNECTIONS / RIEMANNIAN — being built RIGHT NOW by the core DG team (Massot, Macbeth,
grunweg, Rothgang):
- PR #36279 MERGED (12 Mar 2026): `Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.
  Basic`. Koszul-style covariant derivative on bundle sections (operator ∇ X σ, classes
  `CovariantDerivative` / `ContMDiffCovariantDerivative`). NOT built via a tensor-derivation
  abstraction. Affine/torsor structure shows up as `difference` of two connections being
  tensorial (`differenceAux_tensorial`). Connection-1-form (D + A) picture DEFERRED to a later
  PR (Massot, in review comments).
- PR #36036 (open WIP, "poor man's blueprint," 708 commits): Levi-Civita NEARLY DONE
  ("last sorry in lc file"): `IsLeviCivitaConnection`, `.uniqueness`, `leviCivitaConnection`,
  compatibility, torsion-free. Plus Curvature.lean (curvatureTensorAux, traceCurvature),
  ChristoffelSymbols, OrthonormalFrame, Geodesics, Ehresmann, ExistsRiemannianMetric.
  Built via `tensoriality` / `TensorialAt`, NOT a tensor-derivation genus. Introduced
  `mvfderiv` to hide the TangentSpace≡E defeq pain (SAME trap as our §4.2 kernel errors).
- PRs #36285 (torsion, merged), #36299 (metric connections, open).
- VERDICT on the long tensor-derivation debate: O'Neill front-loads tensor derivations
  (genus-first); Mathlib does NOT — it builds the specific tensors and proves tensoriality
  per-construction (concrete-first), matching the `mlieBracket` precedent. So "tensor
  derivations are the Mathlib way" turned out FALSE for this corner.

LIE DERIVATIVE / FORMS — the genuinely empty gap (where Track A lives):
- Lie BRACKET of vector fields EXISTS (`VectorField.mlieBracket`, built concretely via
  extChartAt pullback; `GroupLieAlgebra I G` sits on top of it). Lie DERIVATIVE (general
  tensor) does NOT. Interior product ι_X and Cartan's formula L = dι+ιd: NOT present.
- DIFFERENTIAL FORMS: `Mathlib/Analysis/Calculus/DifferentialForm/Basic.lean` has `extDeriv`
  BUT ONLY ON NORMED SPACES (E → E[⋀^n]→L F), NOT manifolds. Manifold forms (bundled,
  chart-glued), bundle-valued / Lie-algebra-valued forms, integration of forms on manifolds,
  Stokes — ALL ABSENT (confirmed by an Apr-2026 Stokes paper + a Zulip thread of someone
  wanting Lie-algebra-valued forms for principal-bundle connections, no progress).
- SO: the FakeFormII forms work + the bundle-valued exterior algebra + the Einstein 3-form are
  in a REAL GAP. That is where personal effort is best spent — NOT on connections/Levi-Civita
  (upstream is closing those), but on the forms/gauge/Einstein-3-form side nobody is building.

--------------------------------------------------------------------------------
## 3b. SOLDER FORM = the coframe e^a (structural anchor for Track A)

The canonical (tautological / fundamental) vector-valued 1-form θ on the frame bundle FM:
at a point p = a frame (linear iso ℝ^n ≅ T_xM), θ_p(v) = e_p^{-1}(dπ(v)) — project down, read
components in the frame you're sitting at. As a TM-valued form on M it IS the identity on TM.
Horizontal + GL(n)-equivariant (basic/tensorial), so it descends to M.

Why it matters for Track A:
- On full FM with associated bundle TM, θ is CANONICAL (tautological). After the LORENTZIAN
  orthonormal reduction (P = F_O(M), structure group O(1,3), reference metric η), it is NO
  LONGER canonical — the different soldering choices ARE the different TETRADS / vierbeins.
  So the coframe e^a in ε_abcd e^b ∧ Ω^{cd} IS the solder form on the orthonormal frame bundle.
- Cartan structure equations are D applied to the two canonical 1-forms:
    torsion  Θ = Dθ   (θ = solder form, canonical — given for free by FM)
    curvature Ω = Dω  (ω = connection form, a CHOICE)
  This is the structural reason torsion & curvature are siblings, and ties the coframe side of
  Track A to the FrameBundle.lean work.
- (Aside, same tautology: on T*Q the tautological/Liouville 1-form θ_m = m ∘ d_m π — point m
  IS a covector, apply it after projecting down. Frame-bundle θ and cotangent θ are the same
  recipe.)

--------------------------------------------------------------------------------
## 4. Unfinished threads / TODO when resuming geometry

1. COMPILE the patches. None of 0001–0004 nor `GradedDiffLieAlg.lean` is compile-verified.
   Do this while the friction points are fresh-ish (notes above). Stopping line should have
   been "Bianchi compiles green" — it is NOT there yet.

2. The `0003` kernel fix may be INSUFFICIENT. User reported `letI ... := inferInstanceAs ...`
   STILL produced a kernel error with the binder named `this` — i.e. even `letI` got
   closure-converted to an opaque lambda in the `_aux` abstraction on the rc toolchain. The
   proposed stronger fix (NOT yet tried by user): make the result independent of any LOCAL
   tangent-space instance — restate the lemma `isUnit_comp_iff_of_isUnit` at full generality
   over a plain associative/monoid structure (`isUnit_comp_iff_of_isUnit_weak`, no Normed
   anything) so the call site needs NO local `NormedSpace (TangentSpace ...)` instance at all.
   This was sketched but not written into a patch. ← LIKELY THE REAL FIX.

3. `GradedDiffLieAlg` instance (the deferred honest core): build `Ω* ⊗ 𝔤` from
   `GroupLieAlgebra IG G` (carries real LieRing), define `wb` fibrewise via Lie bracket,
   discharge `wb_wb_self` from `lie_jacobi` (pointwise computation, see §2). This retires the
   last assumption of the layer. Pure Lie-algebra identity-chasing — writable with confidence.

4. Tu reference numbers (21.5 / 21.6 / Problem 21.5 / 21.7 / 30.2 / 30.3): 21.5, 21.6,
   Problem 21.5, (30.3) are CONFIRMED from the photographed page. Prop 21.7 and the curvature
   "definition" label are RECONSTRUCTED from memory — verify against the book before blueprint.

5. Sign convention: Bianchi came out `dΩ = [Ω∧ω]` (positive), MATCHES Tu's photographed page.
   But the file is uncompiled — let the eventual proof be the arbiter; `−` or `[ω∧Ω]` would be
   convention reconciliation, not error.

6. BLUEPRINT (the leanblueprint artifact) discussed repeatedly but NEVER produced. If wanted:
   the graded layer as proved nodes; bundle-valued forms-instance + flow theorem as open nodes.
   Frame as Track A (forms rewrite of page 7), NOT as a Mathlib contribution. Since the goal is
   not upstreaming, a personal blueprint is optional — its value is organizing the Track-A arc
   (graded algebra → bundle-valued d → orthonormal reduction → solder form / coframe → Einstein
   3-form), not coordinating contributors.

7a. DON'T DUPLICATE UPSTREAM (see §3a): connections / Levi-Civita / curvature / geodesics are
   being closed now by the core team (#36279 merged, #36036 nearly sorry-free). Personal effort
   is best on the EMPTY gap: bundle-valued / Lie-algebra-valued forms on manifolds, the exterior
   covariant derivative D on them, the orthonormal reduction, and the Einstein 3-form. If a
   forms layer is ever wanted upstream, the Zulip thread (someone wanting Lie-algebra-valued
   forms for principal-bundle connections) is the natural home — but that's incidental.

7. Other open sorries mentioned but not addressed: `Ad_units_eq` / `maurerCartan_units_eq`
   (Task 3, needs the `toOpenPartialHomeomorph` machinery — same machinery as a HasMFDerivAt-
   through-open-embedding transfer lemma, shared with the exp shortcut in §3);
   `W_lee_neg_time` in MaximalFlow.lean.

--------------------------------------------------------------------------------
## 5. Recurring lesson (carry forward)

Every "confident fix shipped uncompiled" this session needed user-reported errors to correct
(omit-wrongly-added, haveI→letI→still-failed, etc). On frontier formalization with no
training-data precedent, the user's compiler feedback IS the correctness mechanism. Ship
small, flag friction explicitly, expect iteration. Don't trust a green-looking patch.
