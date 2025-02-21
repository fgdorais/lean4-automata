import Automata.Basic

namespace NFA

@[ext] structure Matrix (α : Type _) where
  size : Nat
  start : BitVec size
  final : BitVec size
  trans (x : α) : BitMat size size

namespace Matrix
variable (m : Matrix α)

abbrev State := Fin m.size

def run : List α → (start : BitVec m.size := m.start) → BitVec m.size
| [], start => start
| x::xs, start => run xs (start := (m.trans x).combo start)

theorem run_nil {start : BitVec m.size} : m.run [] start = start := rfl

theorem run_cons (x : α) (xs : List α) {start : BitVec m.size} : m.run (x :: xs) start = m.run xs ((m.trans x).combo start) := rfl

theorem run_append (xs ys : List α) {start : BitVec m.size} : m.run (xs ++ ys) start = m.run ys (m.run xs start) := by
  induction xs generalizing start with
  | nil => rfl
  | cons x xs ih =>
    rw [List.cons_append]
    rw [run_cons]
    rw [run_cons]
    rw [ih]

abbrev accept (xs : List α) (start : BitVec m.size := m.start) : Bool := m.final.dot (m.run xs start)

theorem accept_def (xs : List α) {start : BitVec m.size} : m.accept xs start = m.final.dot (m.run xs start) := rfl
