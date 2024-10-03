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

theorem cat_start_inl (s₁) : (m₁ ++ m₂).start (.inl s₁) ↔ m₁.start s₁ := Iff.rfl

theorem cat_start_inr (s₂) : (m₁ ++ m₂).start (.inr s₂) ↔ m₂.start s₂ ∧ ∃ s₁, m₁.start s₁ ∧ m₁.final s₁ := by
  simp only [HAppend.hAppend, NFA.cat]
  constr
  · intro h
    dec_lift at h
    exact h
  · intro h
    dec_lift
    exact h

theorem cat_final_inl (s₁) : (m₁ ++ m₂).final (.inl s₁) ↔ m₁.final s₁ ∧ ∃ s₂, m₂.start s₂ ∧ m₂.final s₂ := by
  simp only [HAppend.hAppend, NFA.cat]
  constr
  · intro h
    dec_lift at h
    exact h
  · intro h
    dec_lift
    exact h

theorem cat_final_inr (s₂) : (m₁ ++ m₂).final (.inr s₂) ↔ m₂.final s₂ := Iff.rfl

theorem cat_trans_inl_inl (x s₁ t₁) : (m₁ ++ m₂).trans x (.inl s₁) (.inl t₁) ↔ m₁.trans x s₁ t₁ := by
  simp only [HAppend.hAppend, NFA.cat]

theorem cat_trans_inl_inr (x s₁ t₂) : (m₁ ++ m₂).trans x (.inl s₁) (.inr t₂) ↔ m₁.final s₁ ∧ (∃ s₂, m₂.start s₂ ∧ m₂.trans x s₂ t₂) := by
  simp only [HAppend.hAppend, NFA.cat]
  constr
  · intro h
    dec_lift at h
    exact h
  · intro h
    dec_lift
    exact h

theorem cat_trans_inr_inl (x s₂ t₁) : ¬ (m₁ ++ m₂).trans x (.inr s₂) (.inl t₁) := by
  simp only [HAppend.hAppend, NFA.cat]; trivial

theorem cat_trans_inr_inr (x s₂ t₂) : (m₁ ++ m₂).trans x (.inr s₂) (.inr t₂) ↔ m₂.trans x s₂ t₂ := Iff.rfl

theorem cat_run_inr_inl (xs : List α) (s₂ t₁) : ¬(m₁ ++ m₂).run xs (.inr s₂) (.inl t₁) := by
  induction xs generalizing s₂ t₁ with
  | nil =>
    rw [run_nil]
    intro
    contradiction
  | cons x xs ih =>
    rw [run_cons]
    intro
    | ⟨Sum.inl u₁, htrans, _⟩ => exact cat_trans_inr_inl m₁ m₂ x s₂ u₁ htrans
    | ⟨Sum.inr u₂, _, hrun⟩ => exact ih u₂ t₁ hrun

theorem cat_run_inr_inr (xs : List α) (s₂ t₂) : (m₁ ++ m₂).run xs (.inr s₂) (.inr t₂) ↔ m₂.run xs s₂ t₂ := by
  induction xs generalizing s₂ t₂ with
  | nil =>
    rw [(m₁ ++ m₂).run_nil]
    rw [m₂.run_nil]
    constr
    · intro | rfl => rfl
    · intro | rfl => rfl
  | cons x xs ih =>
    rw [(m₁ ++ m₂).run_cons]
    rw [m₂.run_cons]
    constr
    · intro
      | ⟨Sum.inl u₁, htrans, _⟩ =>
        absurd htrans
        exact cat_trans_inr_inl m₁ m₂ x s₂ u₁
      | ⟨Sum.inr u₂, htrans, hrun⟩ =>
        rw [cat_trans_inr_inr] at htrans
        rw [ih] at hrun
        exists u₂
    · intro
      | ⟨u₂, htrans, hrun⟩ =>
        rw [←cat_trans_inr_inr] at htrans
        rw [←ih] at hrun
        exists Sum.inr u₂

theorem cat_run_inl_inl (xs : List α) (s₁ t₁) : (m₁ ++ m₂).run xs (.inl s₁) (.inl t₁) ↔ m₁.run xs s₁ t₁ := by
  induction xs generalizing s₁ t₁ with
  | nil =>
    rw [(m₁ ++ m₂).run_nil]
    rw [m₁.run_nil]
    constr
    · intro | rfl => rfl
    · intro | rfl => rfl
  | cons x xs ih =>
    rw [(m₁ ++ m₂).run_cons]
    rw [m₁.run_cons]
    constr
    · intro
      | ⟨Sum.inl u₁, htrans, hrun⟩ =>
        rw [cat_trans_inl_inl] at htrans
        rw [ih] at hrun
        exists u₁
      | ⟨Sum.inr u₂, _, hrun⟩ =>
        absurd hrun
        exact cat_run_inr_inl m₁ m₂ xs u₂ t₁
    · intro ⟨u₁, htrans, hrun⟩
      rw [←cat_trans_inl_inl] at htrans
      rw [←ih] at hrun
      exists Sum.inl u₁

theorem cat_run_inl_inr {xs ys : List α} {s₁ t₁ s₂ t₂} : ys ≠ [] → m₁.run xs s₁ t₁ → m₂.run ys s₂ t₂ → m₁.final t₁ → m₂.start s₂ → (m₁ ++ m₂).run (xs ++ ys) (.inl s₁) (.inr t₂) := by
  intro hxs hrun₁ hrun₂ hfinal hstart
  induction xs generalizing s₁ t₂ with
  | nil =>
    rw [List.nil_append]
    rw [NFA.run_nil] at hrun₁
    cases hrun₁
    cases ys with
    | nil => contradiction
    | cons y ys =>
      rw [NFA.run_cons] at hrun₂ ⊢
      match hrun₂ with
      | ⟨r₂, htrans, hrun⟩ =>
        exists (.inr r₂)
        constr
        · rw [cat_trans_inl_inr]
          constr
          · exact hfinal
          · exists s₂
        · rw [cat_run_inr_inr]
          exact hrun
  | cons x xs ih =>
    rw [List.cons_append]
    rw [NFA.run_cons] at hrun₁ ⊢
    match hrun₁ with
    | ⟨u₁, htrans, hrun⟩ =>
      exists (.inl u₁)
      constr
      · rw [cat_trans_inl_inl]
        exact htrans
      · apply ih
        · exact hrun
        · exact hrun₂

theorem cat_sound {xs ys : List α} : m₁.accept xs → m₂.accept ys → NFA.accept (m₁ ++ m₂) (xs ++ ys) := by
  unfold accept
  intro h₁ h₂
  dec_lift at h₁ h₂ ⊢
  match h₁, h₂ with
  | ⟨(s₁,t₁), hrun₁, ⟨hstart₁, hfinal₁⟩⟩, ⟨(s₂,t₂), hrun₂, ⟨hstart₂, hfinal₂⟩⟩ =>
    by_cases xs = [], ys = [] with
    | isTrue hxs, _ =>
      cases hxs
      rw [List.nil_append]
      exists (.inr s₂, .inr t₂)
      constr
      · rw [cat_run_inr_inr]
        exact hrun₂
      · constr
        · rw [cat_start_inr]
          constr
          · exact hstart₂
          · exists s₁
            · constr
              · exact hstart₁
              · simp [run_nil] at hrun₁
                rw [hrun₁]
                exact hfinal₁
        · rw [cat_final_inr]
          exact hfinal₂
    | _, isTrue hys =>
      cases hys
      unfold run at hrun₂
      dec_lift at hrun₂
      cases hrun₂
      rw [List.append_nil]
      exists (.inl s₁, .inl t₁)
      constr
      · rw [cat_run_inl_inl]
        exact hrun₁
      · constr
        · rw [cat_start_inl]
          exact hstart₁
        · rw [cat_final_inl]
          constr
          · exact hfinal₁
          · exists s₂
    | isFalse _, isFalse _ =>
      exists (.inl s₁, .inr t₂)
      constr
      · apply cat_run_inl_inr
        · assumption
        · exact hrun₁
        · exact hrun₂
        · exact hfinal₁
        · exact hstart₂
      · constr
        · rw [cat_start_inl]
          exact hstart₁
        · rw [cat_final_inr]
          exact hfinal₂

theorem concat_nurLR {zs : List α} {s₁ : m₁.State} {s₂ : m₂.State} : (m₁ ++ m₂).run zs (.inl s₁) (.inr s₂) = true → ∃ xs ys t₁ t₂, zs = xs ++ ys ∧ m₁.final t₁ ∧ m₁.run xs s₁ t₁ ∧ m₂.start t₂ ∧ m₂.run ys t₂ s₂ := by
  intro h
  induction zs generalizing s₁ s₂ with
  | nil =>
    rw [NFA.run_nil] at h
    contradiction
  | cons z zs ih =>
    unfold run at h
    dec_lift at h
    match h with
    | ⟨.inr t₂, htrans, hrun⟩ =>
      rw [cat_run_inr_inr] at hrun
      rw [cat_trans_inl_inr] at htrans
      match htrans with
      | ⟨hfinal, t, hstart, htrans⟩ =>
        exists []
        exists z::zs
        exists s₁
        exists t
        constr
        · rfl
        · constr
          · exact hfinal
          · constr
            · unfold run
              dec_lift
            · constr
              · exact hstart
              · unfold run
                dec_lift
                exists t₂
    | ⟨.inl t, htrans, hrun⟩ =>
      match ih hrun with
      | ⟨xs,ys,t₁,t₂,heq,hfinal,hxrun,hstart,hyrun⟩ =>
        exists z::xs
        exists ys
        exists t₁
        exists t₂
        constr
        · rw [List.cons_append, heq]
        · constr
          · exact hfinal
          · constr
            · unfold run
              dec_lift
              exists t
            · constr
              · exact hstart
              · exact hyrun

theorem cat_exact {zs : List α} : (m₁ ++ m₂).accept zs → ∃ xs ys, zs = xs ++ ys ∧ m₁.accept xs ∧ m₂.accept ys := by
  intro hz
  unfold accept at hz
  dec_lift at hz
  match hz with
  | ⟨⟨.inl s₁, .inl s₂⟩, hrun ,⟨hstart,hfinal⟩⟩ =>
    rw [cat_start_inl] at hstart
    rw [cat_final_inl] at hfinal
    rw [cat_run_inl_inl] at hrun
    match hfinal with
    |⟨hfinal, t, hstart, htfinal⟩ =>
      exists zs
      exists []
      rw [List.append_nil]
      constr
      · rfl
      · constr
        · unfold accept
          dec_lift
          exists (s₁, s₂)
        · unfold accept
          dec_lift
          exists (t, t)
          constr
          · simp only [NFA.run]; rfl
          · constr
            · exact hstart
            · exact htfinal
  | ⟨⟨.inl s₁, .inr s₂⟩, hrun, ⟨hstart₁,hfinal₂⟩⟩ =>
    rw [cat_start_inl] at hstart₁
    rw [cat_final_inr] at hfinal₂
    match concat_nurLR m₁ m₂ hrun with
    | ⟨xs,ys,t₁,t₂,heq,hfinal₁,hxrun,hstart₂,hyrun⟩ =>
      exists xs
      exists ys
      constr
      · exact heq
      · constr
        · unfold accept
          dec_lift
          exists (s₁,t₁)
        · unfold accept
          dec_lift
          exists (t₂,s₂)
  | ⟨⟨.inr s₁, .inl s₂⟩, hrun, _⟩ =>
    absurd hrun
    apply cat_run_inr_inl
  | ⟨⟨.inr s₁, .inr s₂⟩, hrun, ⟨hstart,hfinal⟩⟩ =>
    rw [cat_start_inr] at hstart
    rw [cat_final_inr] at hfinal
    rw [cat_run_inr_inr] at hrun
    match hstart with
    | ⟨hstart,t,htstart,htfinal⟩ =>
      exists []
      exists zs
      rw [List.nil_append]
      constr
      · rfl
      · constr
        · unfold accept
          dec_lift
          exists (t,t)
          constr
          · simp only [NFA.run]; rfl
          · constr
            · exact htstart
            · exact htfinal
        · unfold accept
          dec_lift
          exists (s₁,s₂)

end NFA
