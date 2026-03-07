import Mathlib.Tactic.ToSubgroupOf
import Mathlib.Algebra.Group.Subgroup.Finite

open Subgroup

section

variable {G : Type*} [Group G]

@[to_subgroupOf]
theorem subgroupCardCongr (H1 H2 : Subgroup G) :
    H1 = H2 → Nat.card H1 = Nat.card H2 := by
  intro h
  subst h
  rfl

/-- info: subgroupCardCongr_subgroupOf.{u_1} {G : Type u_1} [Group G] (K H1 H2 : Subgroup G) :
  H1.subgroupOf K = H2.subgroupOf K → Nat.card ↥(H1.subgroupOf K) = Nat.card ↥(H2.subgroupOf K) -/
#guard_msgs in
#check subgroupCardCongr_subgroupOf

@[to_subgroupOf]
theorem subgroupElemTrivial (H : Subgroup G) (x : H) : True := by
  let _ := x
  trivial

/-- info: subgroupElemTrivial_subgroupOf.{u_1} {G : Type u_1} [Group G] (K H : Subgroup G) (x : ↥(H.subgroupOf K)) : True -/
#guard_msgs in
#check subgroupElemTrivial_subgroupOf

@[to_subgroupOf]
theorem subgroupCarrierWitness (x : G) (H : Subgroup G) : x ∈ H → True := by
  intro _
  trivial

/-- info: subgroupCarrierWitness_subgroupOf.{u_1} {G : Type u_1} [Group G] (K : Subgroup G) (x : ↥K) (H : Subgroup G) :
  x ∈ H.subgroupOf K → True -/
#guard_msgs in
#check subgroupCarrierWitness_subgroupOf

@[to_subgroupOf]
theorem subgroupNormalWitness (H : Subgroup G) [H.Normal] : H.Normal := inferInstance

/-- info: subgroupNormalWitness_subgroupOf.{u_1} {G : Type u_1} [Group G] (K H : Subgroup G) [(H.subgroupOf K).Normal] :
  (H.subgroupOf K).Normal -/
#guard_msgs in
#check subgroupNormalWitness_subgroupOf

@[to_subgroupOf subgroupCardCongr_manual]
theorem subgroupCardCongr' (H1 H2 : Subgroup G) :
    H1 = H2 → Nat.card H1 = Nat.card H2 := subgroupCardCongr H1 H2

/-- info: subgroupCardCongr_manual.{u_1} {G : Type u_1} [Group G] (K H1 H2 : Subgroup G) :
  H1.subgroupOf K = H2.subgroupOf K → Nat.card ↥(H1.subgroupOf K) = Nat.card ↥(H2.subgroupOf K) -/
#guard_msgs in
#check subgroupCardCongr_manual

/-- A subgroup cardinality congruence. -/
@[to_subgroupOf]
theorem subgroupCardCongrDoc (H1 H2 : Subgroup G) :
    H1 = H2 → Nat.card H1 = Nat.card H2 := subgroupCardCongr H1 H2

open Lean in
/--
info: `subgroupOf` form of `subgroupCardCongrDoc`

---

A subgroup cardinality congruence.
-/
#guard_msgs in
run_meta do
  let some doc ← findDocString? (← getEnv) ``subgroupCardCongrDoc_subgroupOf |
    throwError "no docstring found"
  logInfo doc

end
