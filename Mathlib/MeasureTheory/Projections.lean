/-
Copyright (c) 2024 Etienne Marion. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Etienne Marion
-/
import Mathlib.MeasureTheory.MeasurableSpace.Basic
import Mathlib.Topology.Constructions

open MeasureTheory

section Generality

variable {ι : Type*} {X : ι → Type*}

/-- Given a dependent function, restrict it to a function of variables in `s`. -/
@[simp]
def proj (s : Set ι) (x : (i : ι) → X i) (i : s) : X i := x i

/-- Given a dependent function of variables in `t`, restrict it to a function of variables in `s`
when `s ⊆ t`. -/
@[simp]
def proj₂ {s t : Set ι} (hst : s ⊆ t) (x : (i : t) → X i) (i : s) : X i := x ⟨i.1, hst i.2⟩

/-- Given a dependent function of variables in `t`, restrict it to a function of variables in `s`
when `s ⊆ t`.

This is a `Finset` version of `proj₂`, because otherwise the type of `s ⊆ t`
is not correctly inferred. -/
@[simp]
def fproj₂ {s t : Finset ι} (hst : s ⊆ t) (x : (i : t) → X i) (i : s) : X i :=
  proj₂ (Finset.coe_subset.2 hst) x i

theorem proj₂_comp_proj {s t : Set ι} (hst : s ⊆ t) :
    (proj₂ hst) ∘ (@proj ι X t) = proj s := rfl

theorem fproj₂_comp_proj {s t : Finset ι} (hst : s ⊆ t) :
    (fproj₂ hst) ∘ (@proj ι X t) = proj s.toSet := rfl

theorem proj₂_comp_proj₂ {s t u : Set ι} (hst : s ⊆ t) (htu : t ⊆ u) :
    (proj₂ (X := X) hst) ∘ (proj₂ htu) = proj₂ (hst.trans htu) := rfl

theorem fproj₂_comp_fproj₂ {s t u : Finset ι} (hst : s ⊆ t) (htu : t ⊆ u) :
    (fproj₂ (X := X) hst) ∘ (fproj₂ htu) = fproj₂ (hst.trans htu) := rfl

section measurability

variable [∀ i, MeasurableSpace (X i)]

theorem measurable_proj (s : Set ι) : Measurable (@proj ι X s) :=
  measurable_pi_lambda _ fun _ ↦ measurable_pi_apply _

theorem measurable_proj₂ {s t : Set ι} (hst : s ⊆ t) :
    Measurable (proj₂ (X := X) hst) :=
  measurable_pi_lambda _ fun _ ↦ measurable_pi_apply _

theorem measurable_fproj₂ {s t : Finset ι} (hst : s ⊆ t) :
    Measurable (fproj₂ (X := X) hst) :=
  measurable_pi_lambda _ fun _ ↦ measurable_pi_apply _

end measurability

section continuity

variable [∀ i, TopologicalSpace (X i)]

theorem continuous_proj (s : Set ι) : Continuous (@proj ι X s) :=
  continuous_pi fun _ ↦ continuous_apply _

theorem continuous_proj₂ {s t : Set ι} (hst : s ⊆ t) :
    Continuous (proj₂ (X := X) hst) :=
  continuous_pi fun _ ↦ continuous_apply _

theorem continuous_fproj₂ {s t : Finset ι} (hst : s ⊆ t) :
    Continuous (fproj₂ (X := X) hst) :=
  continuous_pi fun _ ↦ continuous_apply _

end continuity

end Generality

-- section Nat

-- variable {X : ℕ → Type*}

-- /-- Given a dependent function indexed by `ℕ`, specialize it as a function on `Iic n`. -/
-- @[simp]
-- def projNat (n : ℕ) := @proj ℕ X (Set.Iic n)

-- /-- Given a dependent function indexed by `Iic n`, specialize it as a function on `Iic m` when
-- `m ≤ n`. -/
-- @[simp]
-- def projNat_le {m n : ℕ} (hmn : m ≤ n) := proj₂ (X := X) (Set.Iic_subset_Iic.2 hmn)

-- theorem projNat_le_comp_projNat {m n : ℕ} (hmn : m ≤ n) :
--     (projNat_le hmn) ∘ (@projNat X n) = projNat m := rfl

-- /-- Given a dependent function indexed by `Iic n`, specialize it as a function on `Iic m` when
-- `m ≤ n`, `Finset` version. -/
-- @[simp]
-- abbrev fprojNat_le {m n : ℕ} (hmn : m ≤ n) := fproj₂ (X := X) (Finset.Iic_subset_Iic.2 hmn)

-- theorem fprojNat_le_comp_fprojNat {m n : ℕ} (hmn : m ≤ n) :
--     (fprojNat_le hmn) ∘ (@fprojNat X n) = fprojNat m := rfl

-- section measurability

-- variable [∀ n, MeasurableSpace (X n)]

-- theorem measurable_projNat (n : ℕ) : Measurable (@projNat X n) := measurable_proj _

-- theorem measurable_projNat_le {m n : ℕ} (hmn : m ≤ n) : Measurable (projNat_le (X := X) hmn) :=
--   measurable_proj₂ _

-- theorem measurable_fprojNat (n : ℕ) : Measurable (@fprojNat X n) := measurable_fproj _

-- theorem measurable_fprojNat_le {m n : ℕ} (hmn : m ≤ n) : Measurable (fprojNat_le (X := X) hmn) :=
--   measurable_fproj₂ _

-- end measurability

-- section continuity

-- variable [∀ n, TopologicalSpace (X n)]

-- theorem continuous_projNat (n : ℕ) : Continuous (@projNat X n) := continuous_proj _

-- theorem continuous_projNat_le {m n : ℕ} (hmn : m ≤ n) : Continuous (projNat_le (X := X) hmn) :=
--   continuous_proj₂ _

-- theorem continuous_fprojNat (n : ℕ) : Continuous (@fprojNat X n) := continuous_fproj _

-- theorem continuous_fprojNat_le {m n : ℕ} (hmn : m ≤ n) : Continuous (fprojNat_le (X := X) hmn) :=
--   continuous_fproj₂ _

-- end continuity
