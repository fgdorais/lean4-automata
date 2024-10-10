import Automata.NFA.Basic

namespace NFA
variable (m : NFA α)

protected def star : NFA α where
  State := Option m.State
  instDecEq := inferInstance
  instFind := inferInstance
  start
  | some _ => false
  | none => true
  final
  | some _ => false
  | none => true
  trans
  | x, some s, some t => m.trans x s t
  | x, some s, none => Find.any fun t => m.trans x s t && m.final t
  | x, none, some t => Find.any fun s => m.trans x s t && m.start s
  | x, none, none => Find.any fun (s, t) => m.trans x s t && (m.start s && m.final t)

@[simp] theorem star_start_none : m.star.start none = true := rfl

@[simp] theorem star_start_some (s) : m.star.start (some s) = false := rfl

@[simp] theorem star_final_none : m.star.final none = true := rfl

@[simp] theorem star_final_some (s) : m.star.final (some s) = false := rfl

@[simp] theorem star_trans_some_some (x s t) : m.star.trans x (some s) (some t) ↔ m.trans x s t := Iff.rfl

@[simp] theorem star_trans_some_none (x s) : m.star.trans x (some s) none ↔ ∃ t, m.trans x s t ∧ m.final t := by
  simp [NFA.star]

@[simp] theorem star_trans_none_some (x t) : m.star.trans x none (some t) ↔ ∃ s, m.trans x s t ∧ m.start s := by
  simp [NFA.star]


@[simp] theorem star_trans_none_none (x) : m.star.trans x none none ↔ ∃ s t, m.trans x s t ∧ m.start s ∧ m.final t:= by
  simp [NFA.star]


@[simp] theorem star_restart : xs ≠ [] → m.start s → m.star.run xs (some s) t → m.star.run xs none t := by
  intro hxs hstart hrun
  match xs with
  | [] => contradiction
  | x::xs =>
    simp at hrun ⊢
    match hrun with
    | ⟨some u, htrans, hrun⟩ =>
      simp at htrans
      exists some u
      constructor
      · simp
        exists s
      · exact hrun
    | ⟨none, htrans, hrun⟩ =>
      simp at htrans
      match htrans with
      | ⟨u, htrans, hfinal⟩ =>
        exists none
        constructor
        · simp
          exists s, u
        · exact hrun

@[simp] theorem star_accept (xs) : m.star.accept xs ↔ m.star.run xs none none := by
  constructor
  · intro h
    simp at h
    match h with
    | ⟨none, none, h, _, _⟩ =>
      exact h
  · intro h
    simp
    exists none, none

@[simp] theorem star_unstart (xs) : xs ≠ [] → m.star.run xs none none → ∃ s, m.start s ∧ m.star.run xs (some s) none := by
  intro hnone h
  cases xs with
  | nil => contradiction
  | cons x xs =>
    simp at h
    match h with
    | ⟨some x₁, htrans, hrun⟩ =>
      simp at htrans
      match htrans with
      | ⟨s, htrans, hfinal⟩ =>
        exists s
        constructor
        · exact hfinal
        · simp
          exists some x₁
    | ⟨none, htrans, hrun⟩ =>
      simp at htrans
      match htrans with
      | ⟨t, s, htrans, hstart, hfinal⟩ =>
        exists t
        constructor
        · apply hstart
        · simp
          exists none
          constructor
          · simp
            exists s
          · exact hrun

@[simp] theorem star_run_one : m.run xs s t → m.final t → xs ≠ [] → m.star.run xs (some s) none := by
  intro hrun hfinal hxs
  induction xs generalizing s with
  | nil => contradiction
  | cons x xs H =>
    simp at hrun ⊢
    match hrun with
    | ⟨u, htrans, hrun⟩ =>
      if hxs: xs = [] then
        cases hxs
        simp at hrun
        cases hrun
        exists none
        constructor
        · simp
          exists t
        · simp
      else
        exists some u
        constructor
        · exact htrans
        · apply H
          · exact hrun
          · exact hxs

@[simp] theorem star_run_append : m.star.accept ys → m.star.run xs s none → m.star.run (xs ++ ys) s none := by
  intro hys hrun
  induction xs generalizing s with
  | nil =>
    rw [List.nil_append]
    simp at hrun
    rw [hrun, ←star_accept, hys]
  | cons x xs H =>
    rw [List.cons_append]
    simp at hrun ⊢
    match hrun with
    | ⟨t, htrans, hrun⟩ =>
      exists t
      constructor
      · exact htrans
      · apply H
        exact hrun

@[simp] theorem star_one : m.accept xs → m.star.accept xs := by
  intro h
  simp at h ⊢
  exists none,none
  by_cases hx: xs = []
  · cases hx
    match h with
    | ⟨_, _, ⟨_, _⟩⟩ =>
      constructor
      · simp
      · constructor
        · apply star_start_none
        · apply star_final_none
  · constructor
    · match h with
      | ⟨s, xs, hrun, hstart, hfinal⟩ =>
        apply star_restart
        · exact hx
        · exact hstart
        · apply star_run_one
          · exact hrun
          · exact hfinal
          · exact hx
    · constructor <;> rfl

@[simp] theorem star_append : m.star.accept xs → m.star.accept ys → m.star.accept (xs ++ ys) := by
  intro h h₁
  simp at h h₁ ⊢
  exists none, none
  match h with
  | ⟨t₁, t₂, hfinal, hstart⟩ =>
    match h₁ with
    | ⟨s₁, s₂, hfinal₁, hstart₁₁, hfinal₁₂⟩ =>
      match hstart with
      | ⟨hs₁₁, hs₁₂⟩ =>
        constructor
        · apply star_run_append
          · simp [accept]
            exists s₁, s₂
          · match t₁, t₂ with
            | some _, _ => simp at hs₁₁
            | _, some _ => simp at hs₁₂
            | none, none => exact hfinal
        · constructor <;> rfl

@[simp] theorem star_sound_nil : m.star.accept [] := by simp only [accept]; simp; exists none

@[simp] theorem star_sound_append : m.accept xs → m.star.accept ys → m.star.accept (xs ++ ys) := by
  intro h₁ h₂
  apply star_append
  · apply star_one
    exact h₁
  · exact h₂

@[simp] theorem star_sound : {zs : List α} →  zs = [] ∨ (∃ xs ys, zs = xs ++ ys ∧ m.accept xs ∧ m.star.accept ys) → m.star.accept zs
| _, Or.inl rfl => m.star_sound_nil
| _, Or.inr ⟨_, _, rfl, hxs, hys⟩ => m.star_sound_append hxs hys

@[simp] theorem star_nur_append (zs s) : m.star.run zs (some s) none → ∃ xs ys t, xs ≠ [] ∧ zs = xs ++ ys ∧ m.final t ∧ m.run xs s t ∧ m.star.run ys none none := by
  intro hrun
  induction zs generalizing s with
  | nil =>
    simp at hrun
  | cons z zs H =>
    simp at hrun
    match hrun with
    | ⟨some s, htrans, hrun⟩ =>
      match H s hrun with
      | ⟨xs, ys, t, _, hz, hstart, hxrun, hyrun⟩ =>
        exists z::xs
        exists ys
        exists t
        constructor
        · intro
          contradiction
        · constructor
          · rw [hz, List.cons_append]
          · constructor
            · exact hstart
            · constructor
              · simp
                exists s
              · exact hyrun
    | ⟨none, htrans, hrun⟩ =>
      exists [z]
      exists zs
      simp at htrans
      match htrans with
      | ⟨t, htrans, hstart⟩ =>
        exists t
        constructor
        · intro
          contradiction
        · constructor
          · rw [List.cons_append, List.nil_append]
          · constructor
            · exact hstart
            · constructor
              · simp
                exact htrans
              · exact hrun

@[simp] theorem star_exact {zs} : m.star.accept zs → zs ≠ [] → ∃ xs ys, xs ≠ [] ∧ zs = xs ++ ys ∧ m.accept xs ∧ m.star.accept ys := by
  intro h hz
  rw [star_accept] at h
  match star_unstart m zs hz h with
  | ⟨s, hsfinal, hsrun⟩ =>
    match star_nur_append m zs s hsrun with
    | ⟨xs, ys, t, hx, hxy, hstart, hfinal, hrun⟩ =>
      exists xs
      exists ys
      constructor
      · exact hx
      · constructor
        · exact hxy
        · constructor
          · simp
            exists s, t
          · rw [star_accept]
            exact hrun

end NFA
