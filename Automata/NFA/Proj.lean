import Automata.NFA.Basic

namespace NFA
variable [Find α] [Find β] (f : α → β) (m : NFA α)

def proj : NFA β where
  State := m.State
  start s := m.start s
  trans y s t := Find.any (λ x : α => f x = y && m.trans x s t)
  final s := m.final s

@[scoped simp] theorem proj_start (s : m.State) :
(m.proj f).start s = m.start s := rfl

@[scoped simp] theorem proj_final (s : m.State) :
(m.proj f).final s = m.final s := rfl

@[scoped simp] theorem proj_trans (s t : m.State) :
(m.proj f).trans y s t = Find.any (λ x : α => f x = y && m.trans x s t) := rfl

@[simp] theorem proj_run (xs : List α) (s t : m.State) :
m.run xs s t = true → (m.proj f).run (xs.map f) s t = true := by
  induction xs generalizing s t with
  | nil =>
    simp only [NFA.run]
    intro
    decide
  | cons x xs ih =>
    simp only [NFA.run]
    intro h
    simp at h ⊢
    match h with
    | ⟨u, htrans, hrun⟩ =>
      decide

@[simp] theorem proj_nur (ys : List β) (s t : m.State) :
(m.proj f).run ys s t = true → ∃ (xs : List α), ys = xs.map f ∧ m.run xs s t = true := by
  induction ys generalizing s t with
  | nil =>
    intro h
    unfold proj at h
    unfold run at h
    simp at h
    exists []
    constructor
    · rfl
    · unfold run
      simp
      exact h
  | cons y ys ih =>
    intro h
    unfold run at h ⊢
    simp at h
    match h with
    | ⟨u, htrans, hrun⟩ =>
      match ih u t hrun with
      | ⟨xs, hfxs, hrun₁⟩ =>
        simp only [proj] at htrans
        simp at htrans
        match htrans with
        | ⟨x, hfx, htrans₁⟩ =>
          exists x::xs
          constructor
          · unfold List.map
            rw [hfxs, hfx]
          · simp
            exists u

@[simp] theorem proj_exact (ys : List β) : (m.proj f).accept ys → ∃ (xs : List α), xs.map f = ys ∧ m.accept xs := by
  intro h
  unfold accept at h
  simp at h
  match h with
  | ⟨⟨s₁, s₂⟩, hsrun, hsfinal⟩ =>
    unfold proj at hsfinal
    match hsfinal with
    | ⟨hsrstart, hsrfinal⟩ =>
      match proj_nur f m ys s₁ s₂ hsrun with
      | ⟨xs, hxsmap, hxsrun⟩ =>
      exists xs
      constructor
      · rw [hxsmap]
      · unfold accept
        simp
        exists (s₁, s₂)

theorem proj_sound (xs : List α) : m.accept xs → (m.proj f).accept (xs.map f) := by
  intro h
  unfold accept at h
  simp at h ⊢
  match h with
  | ⟨s,hrun,hfinal⟩ =>
    unfold accept
    simp
    exists s
    rw [proj_start]
    rw [proj_final]
    constructor
    · rw [proj_run]
      exact hrun
    · exact hfinal

end NFA
