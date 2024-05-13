import Mathlib.Tactic.GeneralizeProofs

set_option autoImplicit true

inductive Dyck : Nat → Nat → Nat → Type
| nil : Dyck 0 0 0
| up {k l n} : Dyck k l n → Dyck k (l + 1) (n + 1)
| down {k l n} : Dyck k l (n + 1) → Dyck k (l + 1) n
| thru {k l} : Dyck k l 0 → Dyck (k + 1) (l + 1) 0

namespace Dyck

example : Dyck 0 2 0 := nil.up.down
example : Dyck 1 5 0 := nil.up.down.thru.up.down
example : Dyck 2 6 2 := nil.thru.up.down.thru.up.up

def cast (hk : k₁ = k₂) (hl : l₁ = l₂) (hn : n₁ = n₂) : Dyck k₁ l₁ n₁ → Dyck k₂ l₂ n₂ := by
  cases hk
  cases hl
  cases hn
  exact id

notation "♮" d => cast (by omega) (by omega) (by omega) d

@[simp] theorem cast_refl {k l n} (d : Dyck k l n) : cast rfl rfl rfl d = d := by
  induction d <;> simp_all [cast]

@[simp] theorem cast_cast {k₁ k₂ k₃ l₁ l₂ l₃ n₁ n₂ n₃}
    (h₁ : k₁ = k₂) (h₂ : k₂ = k₃) (h₃ : l₁ = l₂) (h₄ : l₂ = l₃) (h₅ : n₁ = n₂) (h₆ : n₂ = n₃) (d : Dyck k₁ l₁ n₁) :
    cast h₂ h₄ h₆ (cast h₁ h₃ h₅ d) = ♮d := by
  cases h₁
  cases h₂
  cases h₃
  cases h₄
  cases h₅
  cases h₆
  rfl

@[simp] theorem up_cast {hk : k₁ = k₂} {hl : l₁ = l₂} {hn : n₁ = n₂} :
    up (cast hk hl hn d) = ♮(up d) := by
  subst hk; subst hl; subst hn; rfl

@[simp] theorem down_cast {hk : k₁ = k₂} {hl : l₁ = l₂} {hn : n₁ + 1 = n₂ + 1} :
    down (cast hk hl hn d) = ♮(down d) := by
  subst hk; subst hl; cases hn; rfl

@[simp] theorem thru_cast {hk : k₁ = k₂} {hl : l₁ = l₂} :
    thru (cast hk hl rfl d) = ♮(thru d) := by
  subst hk; subst hl; rfl

def juxta (d : Dyck k₁ l₁ 0) (d' : Dyck k₂ l₂ n) : Dyck (k₁ + k₂) (l₁ + l₂) n :=
  match d' with
  | nil     => d
  | up d'   => (juxta d d').up
  | down d' => (juxta d d').down
  | thru d' => (juxta d d').thru

@[simp] theorem nil_juxta {k l n} (d : Dyck k l n) :
    juxta nil d = ♮d := by
  induction d <;> simp_all [juxta]

@[simp] theorem juxta_cast {k₁ k₂ l₁ l₂ n} {hk : k₁ = k₁'} {hl : l₁ = l₁'} (d : Dyck k₁ l₁ 0) (d' : Dyck k₂ l₂ n) :
    juxta (cast hk hl rfl d) d' = ♮(juxta d d') := by
  cases hk; cases hl; rfl

@[simp] theorem cast_juxta {k₁ k₂ l₁ l₂ n} {hk : k₂ = k₂'} {hl : l₂ = l₂'} {hn : n = n'} (d : Dyck k₁ l₁ 0) (d' : Dyck k₂ l₂ n) :
    juxta d (cast hk hl hn d') = ♮(juxta d d') := by
  cases hk; cases hl; cases hn; rfl

theorem juxta_assoc {k₁ k₂ k₃ l₁ l₂ l₃ n} (d₁ : Dyck k₁ l₁ 0) (d₂ : Dyck k₂ l₂ 0) (d₃ : Dyck k₃ l₃ n) :
    juxta (juxta d₁ d₂) d₃ = ♮(juxta d₁ (juxta d₂ d₃)) := by
  induction d₃ <;> simp_all [juxta]

example : nil.up.down.juxta nil.up.down = nil.up.down.up.down := rfl

def comp {k₁ k₂ l₁ n₁ n₂} (d₁ : Dyck k₁ l₁ n₁) (d₂ : Dyck k₂ k₁ n₂) : Dyck k₂ l₁ (n₁ + n₂) :=
  match d₁, d₂ with
  | nil, nil => nil
  | up d₁, d₂ => ♮(up (comp d₁ d₂))
  | down d₁, d₂ => down (♮(comp d₁ d₂))
  | thru d₁, up d₂ => up (comp d₁ d₂)
  | thru d₁, down d₂ => down (♮(comp d₁ d₂))
  | thru d₁, thru d₂ => thru (comp d₁ d₂)

example : nil.thru.up.down.thru.comp nil.up.down = nil.up.up.down.down := rfl

@[simp] theorem cast_comp {hl : l₁ = l₁'} {hn : n₁ = n₁'} {d₁ : Dyck k₁ l₁ n₁} {d₂ : Dyck k₂ k₁ n₂} :
    comp (cast rfl hl hn d₁) d₂ = ♮ comp d₁ d₂ := by
  cases hl; cases hn; rfl

@[simp] theorem comp_cast {hk : k₂ = k₂'} {hn : n₂ = n₂'} {d₁ : Dyck k₁ l₁ n₁} {d₂ : Dyck k₂ k₁ n₂} :
    comp d₁ (cast hk rfl hn d₂) = ♮ comp d₁ d₂ := by
  cases hk; cases hn; rfl

@[simp] theorem cast_comp_cast {hk₁ : k₁ = k₁'} {hl : l₁ = l₁'} {hn₁ : n₁ = n₁'} {hk₂ : k₂ = k₂'} {hn₂ : n₂ = n₂'} {d₁ : Dyck k₁ l₁ n₁} {d₂ : Dyck k₂ k₁ n₂} :
    comp (cast hk₁ hl hn₁ d₁) (cast hk₂ hk₁ hn₂ d₂) = ♮ comp d₁ d₂ := by
  cases hk₁; cases hl; cases hn₁; cases hk₂; cases hn₂; rfl

theorem comp_assoc {d₁ : Dyck k₁ l₂ n₁} {d₂ : Dyck k₂ k₁ n₂} {d₃ : Dyck k₃ k₂ n₃} :
    (d₁.comp d₂).comp d₃ = ♮ d₁.comp (d₂.comp d₃) :=
  match d₁, d₂, d₃ with
  | nil, nil, nil => rfl
  | up _, _, _
  | down _, _, _
  | thru _, up _, _
  | thru _, down _, _
  | thru _, thru _, up _
  | thru _, thru _, down _
  | thru _, thru _, thru _ => by cases n₃ <;> simp [comp, comp_assoc]

theorem juxta_comp {d₁ : Dyck k₁ l₁ 0} {d₂ : Dyck k₂ k₁ 0} {d₃ : Dyck k₃ l₃ n₃} {d₄ : Dyck k₄ k₃ n₄} :
    juxta (comp d₁ d₂) (comp d₃ d₄) = comp (juxta d₁ d₃) (juxta d₂ d₄) :=
  match d₃, d₄ with
  | nil, nil => rfl
  | up _, _ => by simp [juxta, comp, juxta_comp]
  | down _, _ => by simp [juxta, comp, juxta_comp]
  | thru _, up _ => by simp [juxta, comp, juxta_comp]
  | thru _, down _ => by simp [juxta, comp, juxta_comp]
  | thru _, thru _ => by simp [juxta, comp, juxta_comp]


-- def compRev (d₁ : Dyck k₁ l n₁) (d₂ : Dyck k₂ l n₂) : Σ k', Σ n₁', Σ n₂', Σ' w : n₁' + n₂' = n₁ + n₂,  Nat × Dyck k' k₁ n₁' × Dyck k' k₂ n₂' :=
--   match k₁, k₂, d₁, d₂ with
--   | _, _, nil, nil => ⟨0, 0, 0, rfl, 0, nil, nil⟩
--   | _, _, up d₁, up d₂ => sorry
--   | _, _, up d₁, down d₂ => match compRev d₁ d₂ with
--     | ⟨_, _, _, w, δ, d₁', d₂'⟩ => ⟨_, _, _, by omega, δ, d₁', d₂'⟩
--   | _, _, up d₁, thru d₂ => match compRev d₁ d₂ with
--     | ⟨_, _, _, w, δ, d₁', d₂'⟩ => ⟨_, _, _, sorry, δ, d₁', up d₂'⟩
--   | _, _, down d₁, up d₂ => match compRev d₁ d₂ with
--     | ⟨_, _, _, w, δ, d₁', d₂'⟩ => ⟨_, _, _, by omega, δ, d₁', d₂'⟩
--   | _, _, down d₁, down d₂ => sorry
--   | _, k₂ + 2, down d₁, thru d₂ => match compRev d₁ d₂ with
--     | ⟨_, n₁', n₂' + 1, w, δ, d₁', up d₂'⟩ => ⟨_, _, n₂', by omega, δ, thru (♮ d₁'), thru (♮ d₂')⟩
--     | ⟨_, n₁', 0, w, δ, d₁', d₂'⟩ => ⟨_, _, _, by omega, δ, d₁', down (♮ d₂')⟩

end Dyck
