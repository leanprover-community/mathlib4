/-
Copyright (c) 2021 Jordan Brown, Thomas Browning, Patrick Lutz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jordan Brown, Thomas Browning, Patrick Lutz
-/
import Mathlib.GroupTheory.Abelianization
import Mathlib.GroupTheory.Perm.ViaEmbedding
import Mathlib.GroupTheory.Subgroup.Simple

/-!
# Solvable Groups

In this file we introduce the notion of a solvable group. We define a solvable group as one whose
derived series is eventually trivial. This requires defining the commutator of two subgroups and
the derived series of a group.

## Main definitions

* `derivedSeries G n` : the `n`th term in the derived series of `G`, defined by iterating
    `general_commutator` starting with the top subgroup
* `IsSolvable G` : the group `G` is solvable
-/


open Subgroup

variable {G G' : Type*} [Group G] [Group G'] {f : G →* G'}

section derivedSeries

variable (G)

/-- The derived series of the group `G`, obtained by starting from the subgroup `⊤` and repeatedly
  taking the commutator of the previous subgroup with itself for `n` times. -/
def derivedSeries : ℕ → Subgroup G
  | 0 => ⊤
  | n + 1 => ⁅derivedSeries n, derivedSeries n⁆

@[simp]
theorem derivedSeries_zero : derivedSeries G 0 = ⊤ :=
  rfl

@[simp]
theorem derivedSeries_succ (n : ℕ) :
    derivedSeries G (n + 1) = ⁅derivedSeries G n, derivedSeries G n⁆ :=
  rfl

theorem derivedSeries_normal (n : ℕ) : (derivedSeries G n).Normal := by
  induction n with
  | zero => exact (⊤ : Subgroup G).normal_of_characteristic
  | succ n ih => exact Subgroup.commutator_normal (derivedSeries G n) (derivedSeries G n)

@[simp 1100]
theorem derivedSeries_one : derivedSeries G 1 = commutator G :=
  rfl

theorem derivedSeries_antitone : Antitone (derivedSeries G) :=
  antitone_nat_of_succ_le fun n => (derivedSeries G n).commutator_le_self

instance derivedSeries_characteristic (n : ℕ) : (derivedSeries G n).Characteristic := by
  induction n with
  | zero => exact Subgroup.topCharacteristic
  | succ n _ => exact Subgroup.commutator_characteristic _ _

end derivedSeries

section CommutatorMap

section DerivedSeriesMap

variable (f) in
theorem map_derivedSeries_le_derivedSeries (n : ℕ) :
    (derivedSeries G n).map f ≤ derivedSeries G' n := by
  induction n with
  | zero => exact le_top
  | succ n ih => simp only [derivedSeries_succ, map_commutator, commutator_mono, ih]

theorem derivedSeries_le_map_derivedSeries (hf : Function.Surjective f) (n : ℕ) :
    derivedSeries G' n ≤ (derivedSeries G n).map f := by
  induction n with
  | zero => exact (map_top_of_surjective f hf).ge
  | succ n ih => exact commutator_le_map_commutator ih ih

theorem map_derivedSeries_eq (hf : Function.Surjective f) (n : ℕ) :
    (derivedSeries G n).map f = derivedSeries G' n :=
  le_antisymm (map_derivedSeries_le_derivedSeries f n) (derivedSeries_le_map_derivedSeries hf n)

end DerivedSeriesMap

end CommutatorMap

section Solvable

variable (G)

/-- A group `G` is solvable if its derived series is eventually trivial. We use this definition
  because it's the most convenient one to work with. -/
@[mk_iff isSolvable_def]
class IsSolvable : Prop where
  /-- A group `G` is solvable if its derived series is eventually trivial. -/
  solvable : ∃ n : ℕ, derivedSeries G n = ⊥

instance (priority := 100) CommGroup.isSolvable {G : Type*} [CommGroup G] : IsSolvable G :=
  ⟨⟨1, le_bot_iff.mp (Abelianization.commutator_subset_ker (MonoidHom.id G))⟩⟩

theorem isSolvable_of_comm {G : Type*} [hG : Group G] (h : ∀ a b : G, a * b = b * a) :
    IsSolvable G := by
  letI hG' : CommGroup G := { hG with mul_comm := h }
  cases hG
  exact CommGroup.isSolvable

theorem isSolvable_of_top_eq_bot (h : (⊤ : Subgroup G) = ⊥) : IsSolvable G :=
  ⟨⟨0, h⟩⟩

instance (priority := 100) isSolvable_of_subsingleton [Subsingleton G] : IsSolvable G :=
  isSolvable_of_top_eq_bot G (by simp [eq_iff_true_of_subsingleton])

variable {G}

theorem solvable_of_ker_le_range {G' G'' : Type*} [Group G'] [Group G''] (f : G' →* G)
    (g : G →* G'') (hfg : g.ker ≤ f.range) [hG' : IsSolvable G'] [hG'' : IsSolvable G''] :
    IsSolvable G := by
  obtain ⟨n, hn⟩ := id hG''
  obtain ⟨m, hm⟩ := id hG'
  refine ⟨⟨n + m, le_bot_iff.mp (Subgroup.map_bot f ▸ hm ▸ ?_)⟩⟩
  clear hm
  induction m with
  | zero =>
    exact f.range_eq_map ▸ ((derivedSeries G n).map_eq_bot_iff.mp
      (le_bot_iff.mp ((map_derivedSeries_le_derivedSeries g n).trans hn.le))).trans hfg
  | succ m hm => exact commutator_le_map_commutator hm hm

theorem solvable_of_solvable_injective (hf : Function.Injective f) [IsSolvable G'] :
    IsSolvable G :=
  solvable_of_ker_le_range (1 : G' →* G) f ((f.ker_eq_bot_iff.mpr hf).symm ▸ bot_le)

instance subgroup_solvable_of_solvable (H : Subgroup G) [IsSolvable G] : IsSolvable H :=
  solvable_of_solvable_injective H.subtype_injective

theorem solvable_of_surjective (hf : Function.Surjective f) [IsSolvable G] : IsSolvable G' :=
  solvable_of_ker_le_range f (1 : G' →* G) (f.range_eq_top_of_surjective hf ▸ le_top)

instance solvable_quotient_of_solvable (H : Subgroup G) [H.Normal] [IsSolvable G] :
    IsSolvable (G ⧸ H) :=
  solvable_of_surjective (QuotientGroup.mk'_surjective H)

instance solvable_prod {G' : Type*} [Group G'] [IsSolvable G] [IsSolvable G'] :
    IsSolvable (G × G') :=
  solvable_of_ker_le_range (MonoidHom.inl G G') (MonoidHom.snd G G') fun x hx =>
    ⟨x.1, Prod.ext rfl hx.symm⟩

variable (G) in
theorem IsSolvable.commutator_lt_top_of_nontrivial [hG : IsSolvable G] [Nontrivial G] :
    commutator G < ⊤ := by
  rw [lt_top_iff_ne_top]
  obtain ⟨n, hn⟩ := hG
  contrapose! hn
  refine ne_of_eq_of_ne ?_ top_ne_bot
  induction n with
  | zero => exact derivedSeries_zero G
  | succ n h => rwa [derivedSeries_succ, h]

theorem IsSolvable.commutator_lt_of_ne_bot [IsSolvable G] {H : Subgroup G} (hH : H ≠ ⊥) :
    ⁅H, H⁆ < H := by
  rw [← nontrivial_iff_ne_bot] at hH
  rw [← H.range_subtype, MonoidHom.range_eq_map, ← map_commutator, map_subtype_lt_map_subtype]
  exact commutator_lt_top_of_nontrivial H

theorem isSolvable_iff_commutator_lt [WellFoundedLT (Subgroup G)] :
    IsSolvable G ↔ ∀ H : Subgroup G, H ≠ ⊥ → ⁅H, H⁆ < H := by
  refine ⟨fun _ _ ↦ IsSolvable.commutator_lt_of_ne_bot, fun h ↦ ?_⟩
  suffices h : IsSolvable (⊤ : Subgroup G) from
    solvable_of_surjective (MonoidHom.range_eq_top.mp (range_subtype ⊤))
  refine WellFoundedLT.induction (C := fun (H : Subgroup G) ↦ IsSolvable H) ⊤ fun H hH ↦ ?_
  rcases eq_or_ne H ⊥ with rfl | h'
  · infer_instance
  · obtain ⟨n, hn⟩ := hH ⁅H, H⁆ (h H h')
    use n + 1
    rw [← (map_injective (subtype_injective _)).eq_iff, Subgroup.map_bot] at hn ⊢
    rw [← hn]
    clear hn
    induction n with
    | zero =>
      rw [derivedSeries_succ, derivedSeries_zero, derivedSeries_zero, map_commutator,
        ← MonoidHom.range_eq_map, ← MonoidHom.range_eq_map, range_subtype, range_subtype]
    | succ n ih => rw [derivedSeries_succ, map_commutator, ih, derivedSeries_succ, map_commutator]

end Solvable

section IsSimpleGroup

variable [IsSimpleGroup G]

theorem IsSimpleGroup.derivedSeries_succ {n : ℕ} : derivedSeries G n.succ = commutator G := by
  induction n with
  | zero => exact derivedSeries_one G
  | succ n ih =>
    rw [_root_.derivedSeries_succ, ih, _root_.commutator]
    rcases (commutator_normal (⊤ : Subgroup G) (⊤ : Subgroup G)).eq_bot_or_eq_top with h | h
    · rw [h, commutator_bot_left]
    · rwa [h]

theorem IsSimpleGroup.comm_iff_isSolvable : (∀ a b : G, a * b = b * a) ↔ IsSolvable G :=
  ⟨isSolvable_of_comm, fun ⟨⟨n, hn⟩⟩ => by
    cases n
    · intro a b
      refine (mem_bot.1 ?_).trans (mem_bot.1 ?_).symm <;>
        · rw [← hn]
          exact mem_top _
    · rw [IsSimpleGroup.derivedSeries_succ] at hn
      intro a b
      rw [← mul_inv_eq_one, mul_inv_rev, ← mul_assoc, ← mem_bot, ← hn, commutator_eq_closure]
      exact subset_closure ⟨a, b, rfl⟩⟩

end IsSimpleGroup

section PermNotSolvable

theorem not_solvable_of_mem_derivedSeries {g : G} (h1 : g ≠ 1)
    (h2 : ∀ n : ℕ, g ∈ derivedSeries G n) : ¬IsSolvable G :=
  mt (isSolvable_def _).mp
    (not_exists_of_forall_not fun n h =>
      h1 (Subgroup.mem_bot.mp ((congr_arg (g ∈ ·) h).mp (h2 n))))

theorem Equiv.Perm.fin_5_not_solvable : ¬IsSolvable (Equiv.Perm (Fin 5)) := by
  let x : Equiv.Perm (Fin 5) := ⟨![1, 2, 0, 3, 4], ![2, 0, 1, 3, 4], by decide, by decide⟩
  let y : Equiv.Perm (Fin 5) := ⟨![3, 4, 2, 0, 1], ![3, 4, 2, 0, 1], by decide, by decide⟩
  let z : Equiv.Perm (Fin 5) := ⟨![0, 3, 2, 1, 4], ![0, 3, 2, 1, 4], by decide, by decide⟩
  have key : x = z * ⁅x, y * x * y⁻¹⁆ * z⁻¹ := by unfold x y z; decide
  refine not_solvable_of_mem_derivedSeries (show x ≠ 1 by decide) fun n => ?_
  induction n with
  | zero => exact mem_top x
  | succ n ih =>
    rw [key, (derivedSeries_normal _ _).mem_comm_iff, inv_mul_cancel_left]
    exact commutator_mem_commutator ih ((derivedSeries_normal _ _).conj_mem _ ih _)

theorem Equiv.Perm.not_solvable (X : Type*) (hX : 5 ≤ Cardinal.mk X) :
    ¬IsSolvable (Equiv.Perm X) := by
  intro h
  have key : Nonempty (Fin 5 ↪ X) := by
    rwa [← Cardinal.lift_mk_le, Cardinal.mk_fin, Cardinal.lift_natCast, Cardinal.lift_id]
  exact
    Equiv.Perm.fin_5_not_solvable
      (solvable_of_solvable_injective (Equiv.Perm.viaEmbeddingHom_injective (Nonempty.some key)))

end PermNotSolvable
