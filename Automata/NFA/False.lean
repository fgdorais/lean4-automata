import Automata.NFA.Basic

namespace NFA

protected def false : NFA α where
  instDecEq := inferInstance
  instFind := inferInstance
  State := Empty
  start := (nomatch .)
  final := (nomatch .)
  trans _ := (nomatch .)

@[simp] theorem false_correct (xs : List α) : NFA.false.accept xs = false := by
  simp only [accept]
  rw[Bool.eq_iff_iff]
  simp
  intro
  contradiction

@[simp] theorem false_sound {xs : List α} : False → NFA.false.accept xs := by
  intro
  contradiction

@[simp] theorem false_exact {xs : List α} : NFA.false.accept xs → False := by
  intro h
  rw [false_correct] at h
  contradiction

end NFA
