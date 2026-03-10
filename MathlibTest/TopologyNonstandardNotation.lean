import Mathlib.Topology.Order
import Mathlib.Topology.Instances.Nat

def tNat : TopologicalSpace Nat := ⊤

section

  local instance : TopologicalSpace Nat := tNat

  /-- info: Continuous fun x => x : Prop -/
  #guard_msgs in
  #check (@Continuous Nat Nat (by infer_instance) (by infer_instance) (fun x : Nat => x))

  /-- info: IsOpen Set.univ : Prop -/
  #guard_msgs in
  #check (@IsOpen Nat (by infer_instance) (Set.univ : Set Nat))

  /-- info: IsOpen : Set ℕ → Prop -/
  #guard_msgs in
  #check (@IsOpen Nat (by infer_instance))

  /-- info: IsClosed Set.univ : Prop -/
  #guard_msgs in
  #check (@IsClosed Nat (by infer_instance) (Set.univ : Set Nat))

  /-- info: closure {0} : Set ℕ -/
  #guard_msgs in
  #check (@closure Nat (by infer_instance) ({0} : Set Nat))

  /-- info: closure : Set ℕ → Set ℕ -/
  #guard_msgs in
  #check (@closure Nat (by infer_instance))

end

section

  local instance : TopologicalSpace Nat := ⊥

  /-- info: Continuous[_, tNat] fun x => x : Prop -/
  #guard_msgs in
  #check (@Continuous Nat Nat (by infer_instance) tNat (fun x : Nat => x))

  /-- info: Continuous[tNat, _] fun x => x : Prop -/
  #guard_msgs in
  #check (@Continuous Nat Nat tNat (by infer_instance) (fun x : Nat => x))

  /-- info: Continuous[tNat, tNat] fun x => x : Prop -/
  #guard_msgs in
  #check (@Continuous Nat Nat tNat tNat (fun x : Nat => x))

end

/-- info: IsOpen[tNat] Set.univ : Prop -/
#guard_msgs in
#check (@IsOpen Nat tNat (Set.univ : Set Nat))

/-- info: IsOpen[tNat] : Set ℕ → Prop -/
#guard_msgs in
#check (@IsOpen Nat tNat)

/-- info: IsClosed[tNat] Set.univ : Prop -/
#guard_msgs in
#check (@IsClosed Nat tNat (Set.univ : Set Nat))

/-- info: closure[tNat] {0} : Set ℕ -/
#guard_msgs in
#check (@closure Nat tNat ({0} : Set Nat))

/-- info: closure[tNat] : Set ℕ → Set ℕ -/
#guard_msgs in
#check (@closure Nat tNat)
