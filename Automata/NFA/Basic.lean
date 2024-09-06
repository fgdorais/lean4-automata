import Automata.Basic

structure NFA.{u,v} (α : Type v) extends StateType.{u} where
  start : State → Bool
  final : State → Bool
  trans : α → State → State → Bool

namespace NFA

section
variable {α} (m : NFA α)

def run : List α → m.State → m.State → Bool
| [], s, t => decide (s = t)
| x::xs, s, t => Find.any fun u => m.trans x s u && run xs u t

theorem run_nil (s t) : m.run [] s t ↔ s = t := by
  unfold run
  constr
  · intro h
    dec_lift at h
    exact h
  · intro h
    dec_lift
    exact h

theorem run_cons (x : α) (xs : List α) (s t) : m.run (x :: xs) s t ↔ ∃ u, m.trans x s u ∧ m.run xs u t := by
  simp only [run]
  constr
  · intro h
    dec_lift at h
    exact h
  · intro h
    dec_lift
    exact h

theorem run_append {xs ys : List α} {s t} : m.run (xs ++ ys) s t ↔ ∃ u, m.run xs s u ∧ m.run ys u t := by
  induction xs generalizing s t with
  | nil =>
    rw [List.nil_append]
    constr
    · intro
      exists s
      constr
      · rw [run_nil]
      · assumption
    · intro ⟨u, h, hrun⟩
      rw [run_nil] at h
      rw [h]
      assumption
  | cons x xs ih =>
    rw [List.cons_append]
    rw [run_cons]
    constr
    · intro ⟨v, htrans, hrun⟩
      match (ih).mp hrun with
      | ⟨u, hrunxs, hrunys⟩ =>
        exists u
        constr
        · rw [run_cons]
          exists v
        · assumption
    · intro ⟨u, hrunxxs, hrunys⟩
      rw [run_cons] at hrunxxs
      match hrunxxs with
      | ⟨v, htrans, hrunxs⟩ =>
        exists v
        constr
        · assumption
        · apply (ih).mpr
          exists u

def accept (xs : List α) : Bool := Find.any fun (s,t) => m.run xs s t && (m.start s && m.final t)

theorem accept_def (xs : List α) : m.accept xs ↔ ∃ s t, m.run xs s t ∧ m.start s ∧ m.final t := by
  constr
  · intro h
    unfold accept at h
    dec_lift at h
    match h with
    | ⟨⟨s,t⟩,⟨_,_,_⟩⟩ =>
      exists s, t
  · intro
    | ⟨s,t,_,_,_⟩ =>
      unfold accept
      dec_lift
      exists (s,t)

end

end NFA
