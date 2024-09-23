import Automata.NFA.Basic

namespace NFA

protected def true : NFA α where
  State := Unit
  start _ := true
  trans _ _ _ := true
  final _ := true

@[simp] theorem true_start (s : (NFA.true (α:=α)).State) : NFA.true.start s = true := rfl

@[simp] theorem true_final (s : (NFA.true (α:=α)).State) : NFA.true.final s = true := rfl

@[simp] theorem true_trans (x : α) (t s : (NFA.true (α:=α)).State) : NFA.true.trans x t s = true := rfl

@[simp] theorem true_run (xs : List α) (t s : (NFA.true (α:=α)).State) : NFA.true.run xs t s = true := by
  induction xs generalizing t s with
  | nil => rfl
  | cons x xs ih =>
    simp [ih, -exists_prop']
    exists ()

@[simp] theorem true_correct (xs : List α) : NFA.true.accept xs = true := by
  simp [-exists_prop']
  exists (), ()

theorem true_sound {xs : List α} : True → NFA.true.accept xs := by simp

theorem true_exact {xs : List α} : NFA.true.accept xs → True := by simp

end NFA
