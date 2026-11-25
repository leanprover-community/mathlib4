# FormalStudies — pure-Init Lean 4 formal theories

Ten Lean 4 modules under `Archive/FormalStudies/`, wired into `Archive.lean` via
`public import`. **75 theorems** in total, all pure `Init` (zero imports, zero
Mathlib): no `sorry`, no custom axioms, no `native_decide`/`unsafe`/`partial`;
`#print axioms` reports only the standard `propext` / `Quot.sound` /
`Classical.choice` (several exact witnesses depend on no axioms at all).

## Modules

| Module | Theorems | Topic |
|---|---|---|
| `Archive.FormalStudies.E8VsA16HadamardLaw` | 12 | Exact E8 vs A16 opposite-sign Hadamard law |
| `Archive.FormalStudies.S70FormalTheory.CrossLayerNonAdditivity` | 7 | Cross-layer non-additivity of quantization error |
| `Archive.FormalStudies.S70FormalTheory.RegimeTriangleMinimax` | 7 | Regime-triangle minimax |
| `Archive.FormalStudies.S70FormalTheory.SortedBlockH4Optimality` | 7 | Sorted Block-H4 SwiGLU invariance/optimality |
| `Archive.FormalStudies.S72bFormalTheory.BallBudgetCannibalization` | 7 | Two-level saddle point: ball-budget cannibalization |
| `Archive.FormalStudies.S72bFormalTheory.CrossLayerInterferenceAndFloatObstruction` | 7 | Cross-layer interference & BF16 obstruction |
| `Archive.FormalStudies.S72bFormalTheory.TwoLevelSaddlePoint` | 7 | Two-level saddle-point theory |
| `Archive.FormalStudies.S73bFormalTheory.HeavyTailLPTStarvation` | 7 | Heavy-tail greedy-LPT starvation |
| `Archive.FormalStudies.S73bFormalTheory.LoadPowerCompressionPhase` | 7 | Load-power compression phase trichotomy |
| `Archive.FormalStudies.S73bFormalTheory.LowBitrateAmplificationAndPareto` | 7 | Low-bitrate amplification & Pareto dominance |

## Build / verify

From the mathlib4 repo root (toolchain pinned by the root `lean-toolchain`):

```bash
lake build Archive.FormalStudies.E8VsA16HadamardLaw   # a single module
lake build Archive                                    # the whole archive, incl. these
```

Each theorem is accompanied by `#print axioms <name>` at the end of its module.

## Provenance

Extracted verbatim (no edits) from the merged study bundles of an independent
research program on weight quantization, where each study also ships a pure-Z/Q
Python oracle, an adversarial test suite, and a SHA-256-pinned certificate.
