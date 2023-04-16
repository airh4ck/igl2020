import model
import arith_structure

namespace definability

variables {L : lang}

def vector.to_va {α : Type*} {n : ℕ+} (v : vector α n) [inhabited α] : ℕ → α :=
  λ var, if var < n then v.nth var else default 

/-- We will consider a predicate definable in a structure `M` iff 
`∃ (φ : formula L)` s.t. `φ` is `true` iff a predicate is `true` 
-/
def predicate_is_definable {L₁ L₂ : lang} (M₁ : struc L₁) {M₂ : struc L₂} 
                           (univ_eq : M₁.univ = M₂.univ) {n : ℕ+}
                           {p : L₂.R n} (p_int : M₂.R p) :=
  ∃ φ : formula L₁, 
    φ.count_free_vars = n ∧ 
    (∀ v : vector M₂.univ n, 
      let va : ℕ → M₁.univ := by {
        let va := @vector.to_va M₂.univ n v M₂.univ_inhabited,
        rw ← univ_eq at va,
        exact va
      } in  
      v ∈ p_int ↔ va ⊨ φ)

open arithmetic_structure

def predicate_is_definable_in_arith_struc {L₁ : arith_lang} (S : arith_struc L₁) (pred : formula ordered_semiring_lang) :=
  ∃ φ : formula L₁, 
    -- φ.count_free_vars = n ∧ 
    ∀ va : ℕ → ℕ,
      @models_formula ↑L₁ ↑S va φ ↔ 
      @models_formula ordered_semiring_lang N_arith_semiring va pred


lemma neg_preserves_definability {L₁ : arith_lang} (S : arith_struc L₁) {φ : formula ordered_semiring_lang} :
  predicate_is_definable_in_arith_struc S φ ↔ predicate_is_definable_in_arith_struc S (¬' φ) := 
begin
  split,
  { intro h,
    cases h with ψ h,
    use (¬' ψ),
    simp [models_formula, not_iff_not, h] },
  { intro h,
    cases h with ψ h,
    use (¬' ψ),
    simp only [models_formula, not_iff_comm],
    simp only [models_formula] at h,
    simp [h] }
end

/-- The set of all predicates that are definable in a given arithmetic structure S -/
def definable_predicates {L₁ : arith_lang} (S : arith_struc L₁) : set (formula ordered_semiring_lang) :=
  { φ : formula ordered_semiring_lang | predicate_is_definable_in_arith_struc S φ }

theorem subset_if_predicates_definable {L₁ L₂ : arith_lang} (S₁ : arith_struc L₁) (S₂ : arith_struc L₂) :
  (∀ pred ∈ S₁.rels.to_list, predicate_is_definable_in_arith_struc S₂ pred) → definable_predicates S₁ ⊆ definable_predicates S₂ :=
begin
  intros h₁ φ h₂,
  simp only [definable_predicates, set.mem_set_of] at h₂ ⊢,

  cases h₂ with ψ ψ_h,
  induction ψ generalizing φ,
  { use ⊤', exact ψ_h },
  { use ⊥', exact ψ_h },
  { let α := convert_term_arith_lang L₂ ψ_ᾰ,
    let β := convert_term_arith_lang L₂ ψ_ᾰ_1,
    use (α =' β),
    simp only [models_formula] at ψ_h ⊢,
    have α_eq_ψ_ᾰ := term_conversion_preserves_interpretation S₁ S₂ ψ_ᾰ,
    have β_eq_ψ_ᾰ_1 := term_conversion_preserves_interpretation S₁ S₂ ψ_ᾰ_1,
    simp only [← α] at α_eq_ψ_ᾰ,
    simp only [← β] at β_eq_ψ_ᾰ_1,
    
    simp [← α_eq_ψ_ᾰ, ← β_eq_ψ_ᾰ_1, ψ_h] },
  { have em := em (ψ_n ∈ (vector.of_fn L₁.ar).to_list),
    cases em,
    {
      have g := rel_to_formula S₁ ψ_ᾰ ψ_ᾰ_1 (by {
        simp at em,
        exact em
      }),
      rcases g with ⟨g_w, g_h₁, g_h₂⟩,

      have h₂ := h₁ g_w g_h₁,
      cases h₂ with γ γ_h,
      use γ,

      intro va,
      simp only [γ_h, ← g_h₂, ψ_h] },
    { use ⊥',
      have h₂ : formula.rel ψ_ᾰ ψ_ᾰ_1 = ⊥',
      { sorry },
      simp [← ψ_h, h₂] } },
  { simp only [models_formula, not_iff_comm] at ψ_h,
    simp only [not_models_formula_iff_models_not] at ψ_h,
    have ψ_h₁ : ∀ (va : ℕ → ℕ),
      @models_formula ↑L₁ ↑S₁ va ψ_ᾰ ↔ @models_formula ordered_semiring_lang N_arith_semiring va (¬' φ),
    { intro va,
      simp [ψ_h va] },

    have h₂ := @ψ_ih (¬' φ) ψ_h₁,
    rw neg_preserves_definability S₂,
    exact h₂ },
  { have α := exists_formula_ordered_semiring_lang S₁ ψ_ᾰ,
    have β := exists_formula_ordered_semiring_lang S₁ ψ_ᾰ_1,
    cases α,
    cases β,
    
    have γ := @ψ_ih_ᾰ α_w α_h,
    have δ := @ψ_ih_ᾰ_1 β_w β_h,
    cases γ,
    cases δ,
    
    use (γ_w ∧' δ_w),
    simp only [models_formula] at ψ_h,
    simp [models_formula, γ_h, δ_h, ← α_h, ← β_h, ψ_h] },
  { have α := exists_formula_ordered_semiring_lang S₁ ψ_ᾰ,
    have β := exists_formula_ordered_semiring_lang S₁ ψ_ᾰ_1,
    cases α,
    cases β,
    
    have γ := @ψ_ih_ᾰ α_w α_h,
    have δ := @ψ_ih_ᾰ_1 β_w β_h,
    cases γ,
    cases δ,
    
    use (γ_w ∨' δ_w),
    simp only [models_formula] at ψ_h,
    simp [models_formula, γ_h, δ_h, ← α_h, ← β_h, ψ_h] },
  { have α := exists_formula_ordered_semiring_lang S₁ ψ_ᾰ_1,
    cases α,
    have h₂ := @ψ_ih α_w α_h,
    cases h₂ with γ γ_h,
    use (∃' ψ_ᾰ γ),
    simp only [← ψ_h, models_formula, α_h, γ_h],
    intro va,
    refl },
  { have α := exists_formula_ordered_semiring_lang S₁ ψ_ᾰ_1,
    cases α,
    have h₂ := @ψ_ih α_w α_h,
    cases h₂ with γ γ_h,
    use (∀' ψ_ᾰ γ),
    simp only [← ψ_h, models_formula, α_h, γ_h],
    intro va,
    refl }
end


end definability