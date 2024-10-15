import Automata.NFA.Basic

namespace NFA
variable [Find α] [DecidableEq β] (f : α → β) (m : NFA α)

def map : NFA β where
  State := m.State
  start s := m.start s
  trans y s t := Find.any fun x => f x = y && m.trans x s t
  final s := m.final s

@[scoped simp] theorem map_start : (m.map f).start s = m.start s := rfl

@[scoped simp] theorem map_final : (m.map f).final s = m.final s := rfl

@[scoped simp] theorem map_trans : (m.map f).trans y s t = Find.any (λ x : α => f x = y && m.trans x s t) := rfl

@[simp] theorem map_run : m.run xs s t = true → (m.map f).run (xs.map f) s t = true := by
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

@[simp] theorem map_nur : (m.map f).run ys s t = true → ∃ (xs : List α), ys = xs.map f ∧ m.run xs s t = true := by
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
      match ih hrun with
      | ⟨xs, hfxs, hrun₁⟩ =>
        match htrans with
        | ⟨x, hfx, htrans₁⟩ =>
          exists x::xs
          constructor
          · simp [hfxs, hfx]
          · simp
            exists u

@[simp] theorem map_exact : (m.map f).accept ys → ∃ (xs : List α), xs.map f = ys ∧ m.accept xs := by
  intro h
  simp at h
  match h with
  | ⟨s₁, s₂, hsrun, hsfinal⟩ =>
    match hsfinal with
    | ⟨hsrstart, hsrfinal⟩ =>
      match map_nur f m hsrun with
      | ⟨xs, hxsmap, hxsrun⟩ =>
      exists xs
      constructor
      · rw [hxsmap]
      · simp
        exists s₁, s₂

theorem map_sound : m.accept xs → (m.map f).accept (xs.map f) := by
  intro h
  simp at h ⊢
  match h with
  | ⟨s, t, hrun, hfinal⟩ =>
    exists s, t
    constructor
    · apply map_run
      exact hrun
    · exact hfinal

end NFA
