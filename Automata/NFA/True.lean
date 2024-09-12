import Automata.NFA.Basic

namespace NFA
variable {α}

protected def true : NFA α where
  State := Unit
  start _ := true
  trans _ _ _ := true
  final _ := true

theorem true_start (s : (NFA.true (α:=α)).State) : NFA.true.start s = true := rfl

theorem true_final (s : (NFA.true (α:=α)).State) : NFA.true.final s = true := rfl

theorem true_trans (x : α) (t s : (NFA.true (α:=α)).State) : NFA.true.trans x t s = true := rfl

theorem true_run (xs : List α) (t s : (NFA.true (α:=α)).State) : NFA.true.run xs t s = true := by
  induction xs generalizing t s with
  | nil => rfl
  | cons x xs ih =>
    unfold run
    simp
    exists ()
    constructor
    · exact true_trans ..
    · exact ih ..

theorem true_correct (xs : List α) : NFA.true.accept xs = true := by
  unfold accept
  simp
  exists ()
  exists ()
  constructor
  · exact true_run ..
  · constructor
    · exact true_start ..
    · exact true_final ..



theorem true_sound {xs : List α} : True → NFA.true.accept xs := by
  intro
  rw [true_correct]

theorem true_exact {xs : List α} : NFA.true.accept xs → True := by
  intro
  trivial

end NFA
