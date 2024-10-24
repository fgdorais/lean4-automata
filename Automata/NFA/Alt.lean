import Automata.NFA.Basic

namespace NFA

protected def alt (m₁ m₂ : NFA α) : NFA α where
  State := Sum m₁.State m₂.State
  instEnum := inferInstance
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

variable {m₁ : NFA.{u_1} α} {m₂ : NFA.{u_2} α}

@[simp] theorem alt_start_inl (s₁) : (m₁ ||| m₂).start (.inl s₁) = m₁.start s₁ := rfl

@[simp] theorem alt_start_inr (s₂) : (m₁ ||| m₂).start (.inr s₂) = m₂.start s₂ := rfl

@[simp] theorem alt_final_inl (s₁) : (m₁ ||| m₂).final (.inl s₁) = m₁.final s₁ := rfl

@[simp] theorem alt_final_inr (s₂) : (m₁ ||| m₂).final (.inr s₂) = m₂.final s₂ := rfl

@[simp] theorem alt_trans_inl_inl (x s₁ t₁) : (m₁ ||| m₂).trans x (.inl s₁) (.inl t₁) = m₁.trans x s₁ t₁ := rfl

@[simp] theorem alt_trans_inl_inr (x s₁ t₂) : (m₁ ||| m₂).trans x (.inl s₁) (.inr t₂) = false := rfl

@[simp] theorem alt_trans_inr_inl (x s₂ t₁) : (m₁ ||| m₂).trans x (.inr s₂) (.inl t₁) = false := rfl

@[simp] theorem alt_trans_inr_inr (x s₂ t₂) : (m₁ ||| m₂).trans x (.inr s₂) (.inr t₂) = m₂.trans x s₂ t₂ := rfl

@[simp] theorem alt_run_inl_inl (xs s₁ t₁) : (m₁ ||| m₂).run xs (.inl s₁) (.inl t₁) ↔ m₁.run xs s₁ t₁ := by
  induction xs generalizing s₁ t₁ with
  | nil => simp; exact Sum.inl.inj_iff
  | cons x xs ih =>
    simp only [run_cons]
    constructor
    · intro
      | ⟨.inl u₁, htrans, hrun⟩ =>
        simp [ih] at htrans hrun
        exists u₁
    · intro ⟨u₁, htrans, hrun⟩
      exists Sum.inl u₁
      simp [ih, htrans, hrun]

@[simp] theorem alt_run_inl_inr (xs s₁ t₂) : ¬(m₁ ||| m₂).run xs (.inl s₁) (.inr t₂) := by
  induction xs generalizing s₁ t₂ with
  | nil => simp
  | cons x xs ih =>
    simp only [run_cons]
    intro | ⟨.inl u, _, hrun⟩ => simp [ih] at hrun

@[simp] theorem alt_run_inr_inl (xs s₂ t₁) : ¬(m₁ ||| m₂).run xs (.inr s₂) (.inl t₁) := by
  induction xs generalizing s₂ t₁ with
  | nil => simp
  | cons x xs ih =>
    rw [(m₁ ||| m₂).run_cons]
    intro ⟨u, htrans, hrun⟩
    cases u with
    | inl u₁ => contradiction
    | inr u₂ => exact ih u₂ t₁ hrun

@[simp] theorem alt_run_inr_inr (xs s₂ t₂) : (m₁ ||| m₂).run xs (.inr s₂) (.inr t₂) ↔ m₂.run xs s₂ t₂ := by
  induction xs generalizing s₂ t₂ with
  | nil =>
    rw [(m₁ ||| m₂).run_nil]
    rw [m₂.run_nil]
    constructor
    · intro | rfl => rfl
    · intro | rfl => rfl
  | cons x xs ih =>
    simp only [run_cons]
    constructor
    · intro
      | ⟨.inr u₂, htrans, hrun⟩ =>
        simp [ih] at htrans hrun
        exists u₂
    · intro ⟨u₂, htrans, hrun⟩
      exists .inr u₂
      simp [ih, htrans, hrun]

@[simp] theorem alt_correct (m₁ : NFA.{u_1} α) (m₂ : NFA.{u_2} α) (xs) :
    (m₁ ||| m₂).accept xs = (m₁.accept xs || m₂.accept xs) := by
  rw [Bool.eq_iff_iff]
  simp
  constructor
  · intro
    | ⟨.inl s₁, .inl t₁, hrun, hstart, hfinal⟩ =>
      left
      simp at hrun hstart hfinal
      exists s₁, t₁
    | ⟨.inr s₂, .inr t₂, hrun, hstart, hfinal⟩ =>
      right
      simp at hrun hstart hfinal
      exists s₂,t₂
    | ⟨.inl s₁, .inr t₂, hrun, _, _⟩ | ⟨.inr s₂, .inl t₁, hrun, _, _⟩ =>
      simp at hrun
  · intro
    | .inl ⟨s₁, t₁, hrun, hstart, hfinal⟩ =>
      exists Sum.inl s₁, Sum.inl t₁
      simp [hrun, hstart, hfinal]
    | .inr ⟨s₂, t₂, hrun, hstart, hfinal⟩ =>
      exists Sum.inr s₂, Sum.inr t₂
      simp [hrun, hstart, hfinal]

theorem alt_sound_left (h : m₁.accept xs) : (m₁ ||| m₂).accept xs := by simp [h]

theorem alt_sound_right (h : m₂.accept xs) : (m₁ ||| m₂).accept xs := by simp [h]

theorem alt_sound : m₁.accept xs ∨ m₂.accept xs → (m₁ ||| m₂).accept xs
  | .inl h => alt_sound_left h
  | .inr h => alt_sound_right h

theorem alt_exact : (m₁ ||| m₂).accept xs → m₁.accept xs ∨ m₂.accept xs := by simp

end NFA
