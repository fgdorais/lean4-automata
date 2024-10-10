import Automata.NFA.Basic

namespace NFA
variable [Find α] [DecidableEq β] (f : α → β) (m : NFA α)

def proj : NFA β where
  State := m.State
  start s := m.start s
  trans y s t := Find.any fun x => f x = y && m.trans x s t
  final s := m.final s

@[scoped simp] theorem proj_start :
  (m.proj f).start s = m.start s := rfl

@[scoped simp] theorem proj_final :
  (m.proj f).final s = m.final s := rfl

@[scoped simp] theorem proj_trans :
  (m.proj f).trans y s t = Find.any (λ x : α => f x = y && m.trans x s t) := rfl

@[simp] theorem proj_run :
  m.run xs s t = true → (m.proj f).run (xs.map f) s t = true := by
  induction xs generalizing s t with
  | nil => simp
  | cons x xs ih =>
    intro h
    simp at h ⊢
    match h with
    | ⟨u, htrans, hrun⟩ =>
      exists u
      constructor
      · exists x
      · apply ih
        exact hrun

@[simp] theorem proj_nur (s t : m.State) :
  (m.proj f).run ys s t = true → ∃ (xs : List α), ys = xs.map f ∧ m.run xs s t = true := by
  induction ys generalizing s t with
  | nil =>
    intro h
    simp at h
    exists []
    constructor
    · rfl
    · simp
      exact h
  | cons y ys ih =>
    intro h
    simp at h
    match h with
    | ⟨u, htrans, hrun⟩ =>
      match ih u t hrun with
      | ⟨xs, hfxs, hrun₁⟩ =>
        match htrans with
        | ⟨x, hfx, htrans₁⟩ =>
          exists x::xs
          constructor
          · simp [hfxs, hfx]
          · simp
            exists u

@[simp] theorem proj_exact : (m.proj f).accept ys → ∃ (xs : List α), xs.map f = ys ∧ m.accept xs := by
  intro h
  simp at h
  match h with
  | ⟨s₁, s₂, hsrun, hsfinal⟩ =>
    match hsfinal with
    | ⟨hsrstart, hsrfinal⟩ =>
      match proj_nur f m s₁ s₂ hsrun with
      | ⟨xs, hxsmap, hxsrun⟩ =>
      exists xs
      constructor
      · rw [hxsmap]
      · simp
        exists s₁, s₂

theorem proj_sound : m.accept xs → (m.proj f).accept (xs.map f) := by
  intro h
  simp at h ⊢
  match h with
  | ⟨s, t, hrun, hfinal⟩ =>
    exists s, t
    constructor
    · apply proj_run
      exact hrun
    · exact hfinal

end NFA
