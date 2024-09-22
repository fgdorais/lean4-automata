import Automata.NFA.Basic

namespace NFA
universe u₁ u₂
variable (m₁ : NFA.{u₁} α) (m₂ : NFA.{u₂} α)

protected def and : NFA α where
  State := m₁.State × m₂.State
  start s := m₁.start s.fst && m₂.start s.snd
  trans x t s := m₁.trans x t.fst s.fst && m₂.trans x t.snd s.snd
  final s := m₁.final s.fst && m₂.final s.snd

instance : HAnd (NFA α) (NFA α) (NFA α) := ⟨NFA.and⟩

@[scoped simp] theorem and_start (s₁ : m₁.State) (s₂ : m₂.State) :
(m₁ &&& m₂).start (s₁,s₂) = (m₁.start s₁ && m₂.start s₂) := rfl

@[scoped simp] theorem and_final (s₁ : m₁.State) (s₂ : m₂.State) :
(m₁ &&& m₂).final (s₁,s₂) = (m₁.final s₁ && m₂.final s₂) := rfl

@[scoped simp] theorem and_trans (x : α) (t₁ s₁ : m₁.State) (t₂ s₂ : m₂.State) :
(m₁ &&& m₂).trans x (t₁,t₂) (s₁,s₂) = (m₁.trans x t₁ s₁ && m₂.trans x t₂ s₂) := rfl

@[scoped simp] theorem and_run (xs : List α) (t₁ s₁ : m₁.State) (t₂ s₂ : m₂.State) :
(m₁ &&& m₂).run xs (t₁, t₂) (s₁, s₂) = (m₁.run xs t₁ s₁ && m₂.run xs t₂ s₂) := by
  induction xs generalizing t₁ t₂ s₁ s₂ with
  | nil =>
    rw [Bool.eq_iff_iff]
    simp
    constructor
    · intro h
      cases h
      constructor
      · rfl
      · rfl
    · intro ⟨h₁, h₂⟩
      rw [h₁, h₂]
  | cons x xs ih =>
    simp only [run]
    rw [Bool.eq_iff_iff]
    simp
    constructor
    · intro ⟨(u₁, u₂), htrans, hrun⟩
      rw [ih] at hrun
      rw [and_trans] at htrans
      simp at hrun htrans
      constructor
      · exists u₁
        constructor
        · exact htrans.1
        · exact hrun.1
      · exists u₂
        constructor
        · exact htrans.2
        · exact hrun.2
    · intro ⟨⟨u₁, htrans₁, hrun₁⟩, ⟨u₂, htrans₂, hrun₂⟩⟩
      exists (u₁, u₂)
      constructor
      · rw [and_trans]
        simp
        constructor
        · exact htrans₁
        · exact htrans₂
      · rw [ih]
        simp
        constructor
        · exact hrun₁
        · exact hrun₂

theorem and_correct (xs : List α) : (m₁ &&& m₂).accept xs = (m₁.accept xs && m₂.accept xs) := by
  unfold accept
  rw [Bool.eq_iff_iff]
  simp
  constructor
  · intro h
    match h with
    | ⟨(s₁₁, s₁₂), (s₂₁, s₂₂), hrun, hstart, hfinal⟩  =>
      rw [and_start] at hstart
      rw [and_final] at hfinal
      rw [and_run] at hrun
      simp at hstart hfinal hrun
      constructor
      · exists s₁₁, s₂₁
        constructor
        · exact hrun.1
        · constructor
          · exact hstart.1
          · exact hfinal.1
      · exists s₁₂, s₂₂
        constructor
        · exact hrun.2
        · constructor
          · exact hstart.2
          · exact hfinal.2
  · intro ⟨⟨s₁₁, s₁₂, hrun₁, hstart₁, hfinal₁⟩, ⟨s₂₁, s₂₂, hrun₂, hstart₂, hfinal₂⟩⟩
    exists (s₁₁, s₂₁), (s₁₂, s₂₂)
    constructor
    · rw [and_run]
      simp
      constructor
      · exact hrun₁
      · exact hrun₂
    · rw [and_start]
      constructor
      · simp
        constructor
        · exact hstart₁
        · exact hstart₂
      · rw [and_final]
        simp
        constructor
        · exact hfinal₁
        · exact hfinal₂


theorem and_sound {xs : List α} : m₁.accept xs → m₂.accept xs → (m₁ &&& m₂).accept xs := by
  intro hleft hright
  rw [and_correct]
  simp
  constructor
  · exact hleft
  · exact hright

theorem and_exact_left {xs : List α} : (m₁ &&& m₂).accept xs → m₁.accept xs := by
  intro h
  rw [and_correct] at h
  simp at h
  exact h.left

theorem and_exact_right {xs : List α} : (m₁ &&& m₂).accept xs → m₂.accept xs := by
  intro h
  rw [and_correct] at h
  simp at h
  exact h.right

end NFA
