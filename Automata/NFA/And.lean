import Automata.NFA.Basic

namespace NFA

protected def and (m₁ m₂ : NFA α) : NFA α where
  State := m₁.State × m₂.State
  start s := m₁.start s.fst && m₂.start s.snd
  trans x t s := m₁.trans x t.fst s.fst && m₂.trans x t.snd s.snd
  final s := m₁.final s.fst && m₂.final s.snd

instance : HAnd (NFA α) (NFA α) (NFA α) := ⟨NFA.and⟩

variable {m₁ : NFA.{u_1} α} {m₂ : NFA.{u_2} α}

@[simp] theorem and_start (s₁ : m₁.State) (s₂ : m₂.State) :
    (m₁ &&& m₂).start (s₁,s₂) = (m₁.start s₁ && m₂.start s₂) := rfl

@[simp] theorem and_final (s₁ : m₁.State) (s₂ : m₂.State) :
    (m₁ &&& m₂).final (s₁,s₂) = (m₁.final s₁ && m₂.final s₂) := rfl

@[simp] theorem and_trans (x : α) (t₁ s₁ : m₁.State) (t₂ s₂ : m₂.State) :
    (m₁ &&& m₂).trans x (t₁,t₂) (s₁,s₂) = (m₁.trans x t₁ s₁ && m₂.trans x t₂ s₂) := rfl

@[simp] theorem and_run (xs : List α) (t₁ s₁ : m₁.State) (t₂ s₂ : m₂.State) :
    (m₁ &&& m₂).run xs (t₁, t₂) (s₁, s₂) = (m₁.run xs t₁ s₁ && m₂.run xs t₂ s₂) := by
  induction xs generalizing t₁ t₂ s₁ s₂ with
  | nil =>
    rw [Bool.eq_iff_iff]
    simp only [run_nil, Bool.and_eq_true]
    constructor
    · intro h
      cases h
      simp
    · intro | ⟨rfl, rfl⟩ => rfl
  | cons x xs ih =>
    rw [Bool.eq_iff_iff]
    simp only [run_cons, Bool.and_eq_true]
    constructor
    · intro ⟨(u₁, u₂), htrans, hrun⟩
      simp [ih] at htrans hrun
      cases htrans; cases hrun
      constructor
      · exists u₁
      · exists u₂
    · intro ⟨⟨u₁, htrans₁, hrun₁⟩, ⟨u₂, htrans₂, hrun₂⟩⟩
      exists (u₁, u₂)
      simp [*]

@[simp] theorem and_correct (m₁ : NFA.{u_1} α) (m₂ : NFA.{u_2} α) (xs : List α) : (m₁ &&& m₂).accept xs = (m₁.accept xs && m₂.accept xs) := by
  rw [Bool.eq_iff_iff]
  simp only [accept_eq_true_iff, Bool.and_eq_true]
  constructor
  · intro h
    match h with
    | ⟨(s₁₁, s₁₂), (s₂₁, s₂₂), hrun, hstart, hfinal⟩  =>
      simp at hstart hfinal hrun
      cases hstart; cases hfinal; cases hrun
      constructor
      · exists s₁₁, s₂₁
      · exists s₁₂, s₂₂
  · intro ⟨⟨s₁₁, s₁₂, hrun₁, hstart₁, hfinal₁⟩, ⟨s₂₁, s₂₂, hrun₂, hstart₂, hfinal₂⟩⟩
    exists (s₁₁, s₂₁), (s₁₂, s₂₂)
    simp [*]

theorem and_sound : m₁.accept xs → m₂.accept xs → (m₁ &&& m₂).accept xs := by
  intros; simp [*]

theorem and_exact_left (h : (m₁ &&& m₂).accept xs) : m₁.accept xs := by
  simp only [and_correct, Bool.and_eq_true] at h
  exact h.left

theorem and_exact_right (h : (m₁ &&& m₂).accept xs) : m₂.accept xs := by
  simp only [and_correct, Bool.and_eq_true] at h
  exact h.right

theorem and_exact (h : (m₁ &&& m₂).accept xs) : m₁.accept xs ∧ m₂.accept xs := by
  simp only [and_correct, Bool.and_eq_true] at h
  exact h

end NFA
