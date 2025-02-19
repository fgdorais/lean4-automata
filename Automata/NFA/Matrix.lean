import Automata.Basic

structure MFA (α : Type _) where
  size : Nat
  start : Vector size Bool
  final : Vector size Bool
  trans : α → Matrix size size Bool

namespace MFA
variable {α} (m : MFA α)

protected theorem eq : {m₁ m₂ : MFA α} → m₁.size = m₂.size → m₁.start ≅ m₂.start → m₁.final ≅ m₂.final → m₁.trans ≅ m₂.trans → m₁ = m₂
| ⟨_,_,_,_⟩, ⟨_,_,_,_⟩, rfl, HEq.rfl, HEq.rfl, HEq.rfl => rfl

abbrev State := Fin m.size

def run : List α → (start : Vector m.size Bool := m.start) → Vector m.size Bool
| [], start => start
| x::xs, start => run xs (start := (m.trans x).mulVecBool start)

theorem run_nil {start : Vector m.size Bool} : m.run [] start = start := rfl

theorem run_cons (x : α) (xs : List α) {start : Vector m.size Bool} : m.run (x :: xs) start = m.run xs ((m.trans x).mulVecBool start) := rfl

theorem run_append (xs ys : List α) {start : Vector m.size Bool} : m.run (xs ++ ys) start = m.run ys (m.run xs start) := by
  induction xs generalizing start with
  | nil => rfl
  | cons x xs ih =>
    rw [List.cons_append]
    rw [run_cons]
    rw [run_cons]
    rw [ih]

abbrev accept (xs : List α) (start : Vector m.size Bool := m.start) : Bool := m.final.dotBool (m.run xs start)

theorem accept_def (xs : List α) {start : Vector m.size Bool} : m.accept xs start = m.final.dotBool (m.run xs start) := rfl

end MFA
