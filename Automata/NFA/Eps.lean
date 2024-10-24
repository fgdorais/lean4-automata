import Automata.NFA.Basic

namespace NFA

protected def eps : NFA α where
  State := Unit
  start _ := true
  final _ := true
  trans _ _ _ := false

-- Not used
-- @[scoped simp] theorem eps_start (s : NFA.eps.State) :
-- (NFA.eps (α:=α)).start s = true := rfl

-- Not used
-- @[scoped simp] theorem eps_final (s : NFA.eps.State) :
-- (NFA.eps (α:=α)).final s = true := rfl

@[scoped simp] theorem eps_trans (x : α) (s t : NFA.eps.State) : NFA.eps.trans x s t = false := rfl

/-- Proof of correctness for `eps` machine -/
@[simp] theorem eps_correct (xs : List α) : NFA.eps.accept xs = match xs with | [] => true | _ => false := by
  unfold accept
  split
  next =>
    simp
    exists ()
  next h =>
    rw [Bool.eq_iff_iff]
    simp
    apply h
    cases xs with
    | nil => rfl
    | cons x xs =>
      unfold NFA.run at hrun
      simp at hrun
      match hrun with
      | ⟨_, h, _⟩ =>
        rw [eps_trans] at h
        contradiction

@[simp] theorem eps_sound : xs = [] → NFA.eps.accept xs := by
  intro h
  rw [eps_correct, h]

@[simp] theorem eps_exact : NFA.eps.accept xs → xs = [] := by
  intro h
  rw [eps_correct] at h
  split at h
  next => rfl
  next => contradiction

end NFA
