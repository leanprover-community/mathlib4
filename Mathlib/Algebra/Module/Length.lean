import Mathlib.Order.KrullDimension
import Mathlib.Order.TrimmedLength
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Data.ENat.Lattice
import Mathlib.Algebra.Homology.ShortComplex.Basic
import Mathlib.Order.Hom.Basic
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Data.ENat.Lattice

/-!
# The length of a module

`TODO`: add APIs with `IsFiniteLength`.
-/

variable {R : Type*} [Ring R] {M M' : Type*} [AddCommGroup M] [AddCommGroup M']
variable [Module R M] [Module R M']

open Order

noncomputable def Submodule.length (p : Submodule R M) : ℕ∞ := Order.height p

variable (R M) in
/--
The length of a module M is defined to be the supremum of lengths of chains of submodules of M. We
define this using the existing krull dimension api, and as a result this takes values in
WithBot ℕ∞ in spite of the fact that there is no module with length equal to ⊥.
-/
noncomputable def Module.length : WithBot ℕ∞ := krullDim (α := Submodule R M)

variable (R M) in
lemma Submodule.length_top_eq : (⊤ : Submodule R M).length = Module.length R M := sorry

lemma Submodule.length_eq (p : Submodule R M) : p.length = Module.length R p := sorry

lemma Submodule.sup_lt_length_succ (p : Submodule R M) : (⨆ q < p, q.length) + 1 = p.length := sorry

@[simp]
lemma Submodule.length_bot : (⊥ : Submodule R M).length = 0 := sorry

@[gcongr]
lemma Submodule.length_mono {p q : Submodule R M} (h : p ≤ q) : p.length ≤ q.length := sorry

open Classical in
/--
The length of a module is greater than or equal to the trimmedLength of any
rs : RelSeries (α := Submodule R M) (· ≤ ·).
-/
theorem RelSeries.moduleLength_ge_trimmedLength (rs : RelSeries (α := Submodule R M) (· ≤ ·)) :
    RelSeries.trimmedLength rs ≤ Module.length R M := by
  rw [← rs.trim_length, Module.length, krullDim]
  exact le_iSup_iff.mpr fun b a ↦ a rs.trim


open Classical in
/-- The module length is additive in short exact sequences. -/
theorem Module.length_additive {S : CategoryTheory.ShortComplex (ModuleCat R)} (hS : S.ShortExact) :
    Module.length R S.X₂ = Module.length R S.X₁ + Module.length R S.X₃ := by
  simp only [length, krullDim, le_antisymm_iff, iSup_le_iff]
  constructor
  · intro rs
    trans ((RelSeries.submoduleComap rs S.f.hom).trimmedLength +
            (RelSeries.submoduleMap rs S.g.hom).trimmedLength)
    · apply Nat.mono_cast
      have trimmedProof := RelSeries.trimmedLength_additive hS rs
      rwa [Nat.add_comm] at trimmedProof
    · have trimleft :=
        RelSeries.moduleLength_ge_trimmedLength (RelSeries.submoduleComap rs S.f.hom)
      have trimright :=
        RelSeries.moduleLength_ge_trimmedLength (RelSeries.submoduleMap rs S.g.hom)
      exact add_le_add trimleft trimright
  · rw [WithBot.iSup_le_add]
    intro rstemp rstemp'
    obtain ⟨rs, hrs⟩ := RelSeries.exists_ltSeries_ge_head_bot_last_top rstemp
    obtain ⟨rs', hrs'⟩ := RelSeries.exists_ltSeries_ge_head_bot_last_top rstemp'

    let gInv : RelSeries (fun (a : Submodule R S.X₂) (b : Submodule R S.X₂) => a < b) :=
      LTSeries.map rs' (Submodule.comap S.g.hom)
      (Submodule.comap_strictMono_of_surjective hS.moduleCat_surjective_g)

    let fIm : RelSeries (fun (a : Submodule R S.X₂) (b : Submodule R S.X₂) => a < b) :=
      LTSeries.map rs (Submodule.map S.f.hom)
      (Submodule.map_strictMono_of_injective hS.moduleCat_injective_f)

    have connect : fIm.last = gInv.head := by
      convert CategoryTheory.ShortComplex.Exact.moduleCat_range_eq_ker hS.exact
      · simp only [RelSeries.last, LTSeries.map_length, LTSeries.map_toFun, fIm]
        have obv : (rs.toFun (Fin.last rs.length)) = ⊤ := hrs.2.2
        rw [obv]; exact Submodule.map_top S.f.hom
      · simp only [RelSeries.head, LTSeries.map_toFun, gInv]
        have obv : rs'.toFun 0 = ⊥ := hrs'.2.1
        rw [obv]; exact rfl

    let smashfg := RelSeries.smash fIm gInv connect
    trans ↑smashfg.length
    · have this' : smashfg.length = rs.length + rs'.length := rfl
      rw [this']
      simp only [Nat.cast_add, ge_iff_le]
      apply add_le_add
      all_goals simp only [Nat.cast_le, hrs.1, hrs'.1]
    · exact le_iSup_iff.mpr fun b a ↦ a smashfg
