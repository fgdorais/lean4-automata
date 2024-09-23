import Automata.NFA.Basic

namespace NFA
variable (m₁ m₂ : NFA α)

protected def alt : NFA α where
  State := Sum m₁.State m₂.State
  instDecEq := inferInstance
  instFind := inferInstance
  start
  | .inl s₁ => m₁.start s₁
  | .inr s₂ => m₂.start s₂
  final
  | .inl s₁ => m₁.final s₁
  | .inr s₂ => m₂.final s₂
  trans
  | x, .inl s₁, .inl t₁ => m₁.trans x s₁ t₁
  | x, .inr s₂, .inr t₂ => m₂.trans x s₂ t₂
  | _, _, _ => false

instance : HOr (NFA α) (NFA α) (NFA α) := ⟨NFA.alt⟩

@[simp] theorem alt_start_inl (s₁) : (m₁ ||| m₂).start (.inl s₁) = m₁.start s₁ := rfl

@[simp] theorem alt_start_inr (s₂) : (m₁ ||| m₂).start (.inr s₂) = m₂.start s₂ := rfl

@[simp] theorem alt_final_inl (s₁) : (m₁ ||| m₂).final (.inl s₁) = m₁.final s₁ := rfl

@[simp] theorem alt_final_inr (s₂) : (m₁ ||| m₂).final (.inr s₂) = m₂.final s₂ := rfl

@[simp] theorem alt_trans_inl_inl (x s₁ t₁) : (m₁ ||| m₂).trans x (.inl s₁) (.inl t₁) = m₁.trans x s₁ t₁ := rfl

@[simp] theorem alt_trans_inl_inr (x s₁ t₂) : (m₁ ||| m₂).trans x (.inl s₁) (.inr t₂) = false := rfl

@[simp] theorem alt_trans_inr_inl (x s₂ t₁) : (m₁ ||| m₂).trans x (.inr s₂) (.inl t₁) = false := rfl

@[simp] theorem alt_trans_inr_inr (x s₂ t₂) : (m₁ ||| m₂).trans x (.inr s₂) (.inr t₂) = m₂.trans x s₂ t₂ := rfl

@[simp] theorem alt_run_inl_inl (xs : List α) (s₁ t₁) : (m₁ ||| m₂).run xs (.inl s₁) (.inl t₁) ↔ m₁.run xs s₁ t₁ := by
  induction xs generalizing s₁ t₁ with
  | nil =>
    rw [(m₁ ||| m₂).run_nil]
    rw [m₁.run_nil]
    constructor
    · intro | rfl => rfl
    · intro | rfl => rfl
  | cons x xs ih =>
    rw [(m₁ ||| m₂).run_cons]
    rw [m₁.run_cons]
    constructor
    · intro ⟨u₁, htrans, hrun⟩
      cases u₁ with
      | inr => contradiction
      | inl u₁ =>
        rw [alt_trans_inl_inl] at htrans
        rw [ih] at hrun
        exists u₁
    · intro ⟨u₁, htrans, hrun⟩
      rw [←alt_trans_inl_inl] at htrans
      rw [←ih] at hrun
      exists Sum.inl u₁

@[simp] theorem alt_run_inl_inr (xs : List α) (s₁ t₂) : ¬(m₁ ||| m₂).run xs (.inl s₁) (.inr t₂) := by
  induction xs generalizing s₁ t₂ with
  | nil =>
    rw [(m₁ ||| m₂).run_nil]
    intro
    contradiction
  | cons x xs ih =>
    rw [(m₁ ||| m₂).run_cons]
    intro ⟨u, htrans, hrun⟩
    cases u with
    | inr u₂ => contradiction
    | inl u₁ => exact ih u₁ t₂ hrun

@[simp] theorem alt_run_inr_inl (xs : List α) (s₂ t₁) : ¬(m₁ ||| m₂).run xs (.inr s₂) (.inl t₁) := by
  induction xs generalizing s₂ t₁ with
  | nil =>
    rw [(m₁ ||| m₂).run_nil]
    intro
    contradiction
  | cons x xs ih =>
    rw [(m₁ ||| m₂).run_cons]
    intro ⟨u, htrans, hrun⟩
    cases u with
    | inl u₁ => contradiction
    | inr u₂ => exact ih u₂ t₁ hrun

@[simp] theorem alt_run_inr_inr (xs : List α) (s₂ t₂) : (m₁ ||| m₂).run xs (.inr s₂) (.inr t₂) ↔ m₂.run xs s₂ t₂ := by
  induction xs generalizing s₂ t₂ with
  | nil =>
    rw [(m₁ ||| m₂).run_nil]
    rw [m₂.run_nil]
    constructor
    · intro | rfl => rfl
    · intro | rfl => rfl
  | cons x xs ih =>
    rw [(m₁ ||| m₂).run_cons]
    rw [m₂.run_cons]
    constructor
    · intro ⟨u₂, htrans, hrun⟩
      cases u₂ with
      | inl => contradiction
      | inr u₂ =>
        rw [alt_trans_inr_inr] at htrans
        rw [ih] at hrun
        exists u₂
    · intro ⟨u₂, htrans, hrun⟩
      rw [←alt_trans_inr_inr] at htrans
      rw [←ih] at hrun
      exists Sum.inr u₂

@[simp] theorem alt_correct (xs : List α) : (m₁ ||| m₂).accept xs = (m₁.accept xs || m₂.accept xs) := by
  simp only [accept]
  rw [Bool.eq_iff_iff]
  simp
  constructor
  · intro
    | ⟨Sum.inl s₁, Sum.inl t₁, hrun, hstart, hfinal⟩  =>
      left
      simp at hrun hstart hfinal
      exists s₁, t₁
    | ⟨Sum.inl s₁, Sum.inr t₂, hrun, _, _⟩ =>
      absurd hrun
      apply alt_run_inl_inr
    | ⟨Sum.inr s₂, Sum.inl t₁, hrun, _, _⟩ =>
      absurd hrun
      apply alt_run_inr_inl
    | ⟨Sum.inr s₂, Sum.inr t₂, hrun, hstart, hfinal⟩ =>
      right
      simp at hrun hstart hfinal
      exists s₂,t₂
  · intro
    | Or.inl ⟨s₁, t₁, hrun, hstart, hfinal⟩ =>
      rw [←alt_run_inl_inl] at hrun
      rw [←alt_start_inl] at hstart
      rw [←alt_final_inl] at hfinal
      exists Sum.inl s₁, Sum.inl t₁
    | Or.inr ⟨s₂, t₂, hrun, hstart, hfinal⟩ =>
      rw [←alt_run_inr_inr] at hrun
      rw [←alt_start_inr] at hstart
      rw [←alt_final_inr] at hfinal
      exists Sum.inr s₂, Sum.inr t₂


theorem alt_sound_left {xs : List α} : m₁.accept xs → (m₁ ||| m₂).accept xs := by
  intro h
  simp [h]

theorem alt_sound_right {xs : List α} : m₂.accept xs → (m₁ ||| m₂).accept xs := by
  intro h
  simp [h]

theorem alt_sound {xs : List α} : m₁.accept xs ∨ m₂.accept xs → (m₁ ||| m₂).accept xs
  | .inl h => alt_sound_left m₁ m₂ h
  | .inr h => alt_sound_right m₁ m₂ h

theorem alt_exact {xs : List α} : (m₁ ||| m₂).accept xs → m₁.accept xs ∨ m₂.accept xs := by
  intro h
  simp_all

end NFA
