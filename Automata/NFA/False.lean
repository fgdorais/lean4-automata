import Automata.NFA.Basic

namespace NFA

protected def false : NFA α where
  instEnum := inferInstance
  State := Empty
  start := (nomatch .)
  final := (nomatch .)
  trans _ := (nomatch .)

@[simp] theorem false_correct (xs : List α) : NFA.false.accept xs = false := by
  rw [Bool.eq_false_iff]
  simp
  intros
  contradiction

theorem false_sound {xs : List α} : False → NFA.false.accept xs := by simp

theorem false_exact {xs : List α} : NFA.false.accept xs → False := by simp

end NFA
