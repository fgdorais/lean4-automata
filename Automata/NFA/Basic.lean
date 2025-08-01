import Automata.Basic

structure NFA.{u,v} (α : Type v) extends StateType.{u} where
  start : State → Bool
  final : State → Bool
  trans : α → State → State → Bool

namespace NFA
variable (m : NFA α)

protected abbrev size : Nat := Fin.Enum.size m.State

def run : List α → m.State → m.State → Bool
  | [], s, t => decide (s = t)
  | x::xs, s, t => Find.any fun u => m.trans x s u && run xs u t

@[simp] theorem run_nil : m.run [] s t ↔ s = t := by
  simp [run]

@[scoped simp] theorem run_cons : m.run (x :: xs) s t ↔ ∃ u, m.trans x s u ∧ m.run xs u t := by
  simp [run]

theorem run_append : m.run (xs ++ ys) s t ↔ ∃ u, m.run xs s u ∧ m.run ys u t := by
  induction xs generalizing s t with
  | nil => simp
  | cons x xs ih =>
    simp only [List.cons_append, run_cons, ih]
    constructor
    · intro ⟨u, htransx, v, hrunxs, hrunys⟩
      exact ⟨v, ⟨u, htransx, hrunxs⟩, hrunys⟩
    · intro ⟨v, ⟨u, htransx, hrunxs⟩, hrunys⟩
      exact ⟨u, htransx, v, hrunxs, hrunys⟩

def accept (xs : List α) : Bool := Find.any fun (s,t) => m.run xs s t && (m.start s && m.final t)

@[scoped simp] theorem accept_eq_true_iff :
    m.accept xs = true ↔ ∃ s t, m.run xs s t ∧ m.start s ∧ m.final t := by
  simp [accept]

@[scoped simp] theorem accept_eq_false_iff :
    m.accept xs = false ↔ ∀ s t, ¬ m.run xs s t ∨ ¬ m.start s ∨ ¬ m.final t := by
  simp only [Bool.eq_false_iff, ne_eq, accept_eq_true_iff, not_exists, Decidable.not_and_iff_or_not]

end NFA
