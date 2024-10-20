import Automata.NFA.Basic

namespace NFA

@[pp_nodot] structure Bisim (m₁ m₂ : NFA α) where
  rel : m₁.State → m₂.State → Bool
  start : rel s₁ s₂ → m₁.start s₁ = m₂.start s₂
  transLR : rel s₁ s₂ → m₁.trans x s₁ t₁ → Find.any fun t₂ => rel t₁ t₂ && m₂.trans x s₂ t₂
  transRL : rel s₁ s₂ → m₂.trans x s₂ t₂ → Find.any fun t₁ => rel t₁ t₂ && m₁.trans x s₁ t₁
  final : rel s₁ s₂ → m₁.final s₁ = m₂.final s₂

namespace Bisim
variable {m₁ m₂ m₃ : NFA α}

protected def id (m : NFA α) : Bisim m m where
  rel s₁ s₂ := decide (s₁ = s₂)
  start h := by
    simp only [decide_eq_true_eq] at h
    rw [h]
  transLR h ht := by
    simp only [decide_eq_true_eq, Find.any_iff_exists, Bool.and_eq_true, exists_eq_left'] at h
    simp [←h, ht]
  transRL h ht := by
    simp only [decide_eq_true_eq, Find.any_iff_exists, Bool.and_eq_true, exists_eq_left] at h
    simp [h, ht]
  final h := by
    simp only [decide_eq_true_eq] at h
    rw [h]

protected def inv (a : Bisim m₁ m₂) : Bisim m₂ m₁ where
  rel s₁ s₂ := a.rel s₂ s₁
  start h := by
    apply Eq.symm
    exact a.start h
  transLR := a.transRL
  transRL := a.transLR
  final h := by
    apply Eq.symm
    exact a.final h

protected def comp (a : Bisim m₂ m₃) (b : Bisim m₁ m₂) : Bisim m₁ m₃ where
  rel s₁ s₃ := Find.any fun s₂ => b.rel s₁ s₂ && a.rel s₂ s₃
  start h := by
    simp only [Find.any_iff_exists, Bool.and_eq_true] at h
    match h with
    | ⟨s₂, hb, ha⟩ =>
      trans m₂.start s₂
      · exact b.start hb
      · exact a.start ha
  transLR H h₁ := by
    simp only [Find.any_iff_exists, Bool.and_eq_true] at H h₁ ⊢
    match H with
    | ⟨s₂, hb, ha⟩ =>
      have H := b.transLR hb h₁
      simp only [Find.any_iff_exists, Bool.and_eq_true] at H
      match H with
      | ⟨t₂, htb, h₂⟩ =>
        have H := a.transLR ha h₂
        simp only [Find.any_iff_exists, Bool.and_eq_true] at H
        match H with
        | ⟨t₃, hta, h₃⟩ =>
          exists t₃
          constructor
          · exists t₂
          · exact h₃
  transRL H h₃ := by
    simp only [Find.any_iff_exists, Bool.and_eq_true] at H h₃ ⊢
    match H with
    | ⟨s₂, hb, ha⟩ =>
      have H := a.transRL ha h₃
      simp only [Find.any_iff_exists, Bool.and_eq_true] at H
      match H with
      | ⟨t₂, hta, h₂⟩ =>
        have H := b.transRL hb h₂
        simp only [Find.any_iff_exists, Bool.and_eq_true] at H
        match H with
        | ⟨t₁, htb, h₁⟩ =>
          exists t₁
          constructor
          · exists t₂
          · exact h₁
  final h := by
    simp only [Find.any_iff_exists, Bool.and_eq_true] at h
    match h with
    | ⟨s₂, hb, ha⟩ =>
      trans m₂.final s₂
      · exact b.final hb
      · exact a.final ha

protected def join (a b : Bisim m₁ m₂) : Bisim m₁ m₂ where
  rel s t := a.rel s t || b.rel s t
  start h := by
    simp only [Bool.or_eq_true] at h
    match h with
    | .inl ha =>
      exact a.start ha
    | .inr hb =>
      exact b.start hb
  transLR H h := by
    simp only [Bool.or_eq_true] at H h
    simp only [Find.any_iff_exists, Bool.and_eq_true, Bool.or_eq_true]
    match H with
    | .inl ha =>
      have H := a.transLR ha h
      simp only [Find.any_iff_exists, Bool.and_eq_true] at H
      match H with
      | ⟨t₂, ha₂, htrans⟩ =>
        exists t₂
        constructor
        · left
          exact ha₂
        · exact htrans
    | .inr hb =>
      have H := b.transLR hb h
      simp only [Find.any_iff_exists, Bool.and_eq_true] at H
      match H with
      | ⟨t₂, hb₂, htrans⟩ =>
        exists t₂
        constructor
        · right
          exact hb₂
        · exact htrans
  transRL H h := by
    simp only [Bool.or_eq_true] at H h
    simp only [Find.any_iff_exists, Bool.and_eq_true, Bool.or_eq_true]
    match H with
    | .inl ha =>
      have H := a.transRL ha h
      simp only [Find.any_iff_exists, Bool.and_eq_true] at H
      match H with
      | ⟨t₂, ha₂, htrans⟩ =>
        exists t₂
        constructor
        · left
          exact ha₂
        · exact htrans
    | .inr hb =>
      have H := b.transRL hb h
      simp only [Find.any_iff_exists, Bool.and_eq_true] at H
      match H with
      | ⟨t₂, hb₂, htrans⟩ =>
        exists t₂
        constructor
        · right
          exact hb₂
        · exact htrans
  final h := by
    simp only [Bool.or_eq_true] at h
    match h with
    | .inl ha =>
      exact a.final ha
    | .inr hb =>
      exact b.final hb

end Bisim

end NFA
