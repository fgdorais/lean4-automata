import Automata.NFA.Basic

namespace NFA
universe u₁ u₂
variable (m₁ : NFA.{u₁} α) (m₂ : NFA.{u₂} α)

protected def cat : NFA α where
  State := Sum m₁.State m₂.State
  instDecEq := inferInstance
  instFind := inferInstance
  start
  | .inl s₁ => m₁.start s₁
  | .inr s₂ => m₂.start s₂ && Find.any fun s₁ => m₁.start s₁ && m₁.final s₁
  final
  | .inl s₁ => m₁.final s₁ && Find.any fun s₂ => m₂.start s₂ && m₂.final s₂
  | .inr s₂ => m₂.final s₂
  trans
  | x, .inl s₁, .inl t₁ => m₁.trans x s₁ t₁
  | x, .inl s₁, .inr t₂ => m₁.final s₁ && Find.any fun s₂ => m₂.start s₂ && m₂.trans x s₂ t₂
  | _, .inr _, .inl _ => false
  | x, .inr s₂, .inr t₂ => m₂.trans x s₂ t₂

instance : HAppend (NFA α) (NFA α) (NFA α) := ⟨NFA.cat⟩

@[simp] theorem cat_start_inl : (m₁ ++ m₂).start (.inl s₁) ↔ m₁.start s₁ := Iff.rfl

@[simp] theorem cat_start_inr : (m₁ ++ m₂).start (.inr s₂) ↔ m₂.start s₂ ∧ ∃ s₁, m₁.start s₁ ∧ m₁.final s₁ := by
  simp only [HAppend.hAppend, NFA.cat]
  constructor
  · intro h
    simp at h
    exact h
  · intro h
    simp
    exact h

@[simp] theorem cat_final_inl : (m₁ ++ m₂).final (.inl s₁) ↔ m₁.final s₁ ∧ ∃ s₂, m₂.start s₂ ∧ m₂.final s₂ := by
  simp only [HAppend.hAppend, NFA.cat]
  constructor
  · intro h
    simp at h
    exact h
  · intro h
    simp
    exact h

@[simp] theorem cat_final_inr : (m₁ ++ m₂).final (.inr s₂) ↔ m₂.final s₂ := Iff.rfl

@[simp] theorem cat_trans_inl_inl : (m₁ ++ m₂).trans x (.inl s₁) (.inl t₁) ↔ m₁.trans x s₁ t₁ := by
  simp only [HAppend.hAppend, NFA.cat]

@[simp] theorem cat_trans_inl_inr : (m₁ ++ m₂).trans x (.inl s₁) (.inr t₂) ↔ m₁.final s₁ ∧ (∃ s₂, m₂.start s₂ ∧ m₂.trans x s₂ t₂) := by
  simp only [HAppend.hAppend, NFA.cat]
  constructor
  · intro h
    simp at h
    exact h
  · intro h
    simp
    exact h

@[simp] theorem cat_trans_inr_inl : ¬ (m₁ ++ m₂).trans x (.inr s₂) (.inl t₁) := by
  simp only [HAppend.hAppend, NFA.cat]; trivial

@[simp] theorem cat_trans_inr_inr : (m₁ ++ m₂).trans x (.inr s₂) (.inr t₂) ↔ m₂.trans x s₂ t₂ := Iff.rfl

@[simp] theorem cat_run_inr_inl : ¬(m₁ ++ m₂).run xs (.inr s₂) (.inl t₁) := by
  induction xs generalizing s₂ t₁ with
  | nil =>
    simp
  | cons x xs ih =>
    simp only [run_cons]
    intro
    | ⟨Sum.inl u₁, htrans, _⟩ => exact cat_trans_inr_inl m₁ m₂ htrans
    | ⟨Sum.inr u₂, _, hrun⟩ => exact ih hrun

@[simp] theorem cat_run_inr_inr (xs : List α) (s₂ t₂) : (m₁ ++ m₂).run xs (.inr s₂) (.inr t₂) ↔ m₂.run xs s₂ t₂ := by
  induction xs generalizing s₂ t₂ with
  | nil =>
    simp
    constructor <;> intro | rfl => rfl
  | cons x xs ih =>
    simp
    constructor
    · intro
      | ⟨Sum.inl u₁, htrans, _⟩ =>
        absurd htrans
        exact cat_trans_inr_inl m₁ m₂
      | ⟨Sum.inr u₂, htrans, hrun⟩ =>
        simp at htrans
        rw [ih] at hrun
        exists u₂
    · intro
      | ⟨u₂, htrans, hrun⟩ =>
        rw [←cat_trans_inr_inr] at htrans
        rw [←ih] at hrun
        exists Sum.inr u₂

@[simp] theorem cat_run_inl_inl : (m₁ ++ m₂).run xs (.inl s₁) (.inl t₁) ↔ m₁.run xs s₁ t₁ := by
  induction xs generalizing s₁ t₁ with
  | nil =>
    simp
    constructor <;> intro | rfl => rfl
  | cons x xs ih =>
    simp
    constructor
    · intro
      | ⟨Sum.inl u₁, htrans, hrun⟩ =>
        simp at htrans
        rw [ih] at hrun
        exists u₁
      | ⟨Sum.inr u₂, _, hrun⟩ =>
        absurd hrun
        exact cat_run_inr_inl m₁ m₂
    · intro ⟨u₁, htrans, hrun⟩
      rw [←cat_trans_inl_inl] at htrans
      rw [←ih] at hrun
      exists Sum.inl u₁

@[simp] theorem cat_run_inl_inr : ys ≠ [] → m₁.run xs s₁ t₁ → m₂.run ys s₂ t₂ → m₁.final t₁ → m₂.start s₂ → (m₁ ++ m₂).run (xs ++ ys) (.inl s₁) (.inr t₂) := by
  intro hxs hrun₁ hrun₂ hfinal hstart
  induction xs generalizing s₁ t₂ with
  | nil =>
    simp only [List.nil_append]
    simp at hrun₁
    cases ys with
    | nil => contradiction
    | cons y ys =>
      rw [NFA.run_cons] at hrun₂ ⊢
      match hrun₂ with
      | ⟨r₂, htrans, hrun⟩ =>
        exists (.inr r₂)
        constructor
        · simp
          constructor
          · rw [hrun₁]
            exact hfinal
          · exists s₂
        · simp
          exact hrun
  | cons x xs ih =>
    rw [List.cons_append]
    rw [NFA.run_cons] at hrun₁ ⊢
    match hrun₁ with
    | ⟨u₁, htrans, hrun⟩ =>
      exists (.inl u₁)
      constructor
      · simp
        exact htrans
      · apply ih
        · exact hrun
        · exact hrun₂

@[simp] theorem cat_sound : m₁.accept xs → m₂.accept ys → NFA.accept (m₁ ++ m₂) (xs ++ ys) := by
  unfold accept
  intro h₁ h₂
  simp at h₁ h₂ ⊢
  match h₁, h₂ with
  | ⟨s₁, t₁, hrun₁, hstart₁, hfinal₁⟩, ⟨s₂, t₂, hrun₂, hstart₂, hfinal₂⟩ =>
    if hxs: xs = [] then
      cases hxs
      rw [List.nil_append]
      exists .inr s₂, .inr t₂
      constructor
      · rw [cat_run_inr_inr]
        exact hrun₂
      · constructor
        · rw [cat_start_inr]
          constructor
          · exact hstart₂
          · exists s₁
            · constructor
              · exact hstart₁
              · simp at hrun₁
                rw [hrun₁]
                exact hfinal₁
        · rw [cat_final_inr]
          exact hfinal₂
    else
      if hys: ys = [] then
        cases hys
        simp at hrun₂
        cases hrun₂
        rw [List.append_nil]
        exists .inl s₁, .inl t₁
        constructor
        · simp
          exact hrun₁
        · constructor
          · simp
            exact hstart₁
          · simp
            constructor
            · exact hfinal₁
            · exists s₂
      else
        exists .inl s₁, .inr t₂
        constructor
        · apply cat_run_inl_inr
          · assumption
          · exact hrun₁
          · exact hrun₂
          · exact hfinal₁
          · exact hstart₂
        · constructor
          · simp
            exact hstart₁
          · simp
            exact hfinal₂

@[simp] theorem concat_nurLR : (m₁ ++ m₂).run zs (.inl s₁) (.inr s₂) = true → ∃ xs ys t₁ t₂, zs = xs ++ ys ∧ m₁.final t₁ ∧ m₁.run xs s₁ t₁ ∧ m₂.start t₂ ∧ m₂.run ys t₂ s₂ := by
  intro h
  induction zs generalizing s₁ s₂ with
  | nil =>
    rw [NFA.run_nil] at h
    contradiction
  | cons z zs ih =>
    simp at h
    match h with
    | ⟨.inr t₂, htrans, hrun⟩ =>
      rw [cat_run_inr_inr] at hrun
      rw [cat_trans_inl_inr] at htrans
      match htrans with
      | ⟨hfinal, t, hstart, htrans⟩ =>
        exists [], z::zs, s₁, t
        constructor
        · rfl
        · constructor
          · exact hfinal
          · constructor
            · simp
            · constructor
              · exact hstart
              · simp
                exists t₂
    | ⟨.inl t, htrans, hrun⟩ =>
      match ih hrun with
      | ⟨xs,ys,t₁,t₂,heq,hfinal,hxrun,hstart,hyrun⟩ =>
        exists z::xs, ys, t₁, t₂
        constructor
        · rw [List.cons_append, heq]
        · constructor
          · exact hfinal
          · constructor
            · simp
              exists t
            · constructor
              · exact hstart
              · exact hyrun

theorem cat_exact : (m₁ ++ m₂).accept zs → ∃ xs ys, zs = xs ++ ys ∧ m₁.accept xs ∧ m₂.accept ys := by
  intro hz
  simp at hz
  match hz with
  | ⟨.inl s₁, .inl s₂, hrun ,⟨hstart,hfinal⟩⟩ =>
    rw [cat_start_inl] at hstart
    rw [cat_final_inl] at hfinal
    rw [cat_run_inl_inl] at hrun
    match hfinal with
    |⟨hfinal, t, hstart, htfinal⟩ =>
      exists zs, []
      rw [List.append_nil]
      constructor
      · rfl
      · constructor
        · simp
          exists s₁, s₂
        · simp
          exists t
  | ⟨.inl s₁, .inr s₂, hrun, ⟨hstart₁,hfinal₂⟩⟩ =>
    rw [cat_start_inl] at hstart₁
    rw [cat_final_inr] at hfinal₂
    match concat_nurLR m₁ m₂ hrun with
    | ⟨xs,ys,t₁,t₂,heq,hfinal₁,hxrun,hstart₂,hyrun⟩ =>
      exists xs, ys
      constructor
      · exact heq
      · constructor
        · simp
          exists s₁, t₁
        · simp
          exists t₂, s₂
  | ⟨.inr s₁, .inl s₂, hrun, _⟩ =>
    absurd hrun
    apply cat_run_inr_inl
  | ⟨.inr s₁, .inr s₂, hrun, ⟨hstart,hfinal⟩⟩ =>
    rw [cat_start_inr] at hstart
    rw [cat_final_inr] at hfinal
    rw [cat_run_inr_inr] at hrun
    match hstart with
    | ⟨hstart,t,htstart,htfinal⟩ =>
      exists [], zs
      rw [List.nil_append]
      constructor
      · rfl
      · constructor
        · simp
          exists t
        · simp
          exists s₁, s₂

end NFA
