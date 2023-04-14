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

/-- A set of all predicates definable in a structure `M` -/
def definable_predicates (M₁ : struc L) (M₂ : struc L) : set (Σ (n : ℕ+), L.R n) :=
    { p : Σ (n : ℕ+), L.R n | 
      ∃ (p_int : M₂.R p.2) (univ_eq : M₁.univ = M₂.univ), 
        predicate_is_definable M₁ univ_eq p_int }

open arithmetic_structure

theorem subset_if_predicates_definable {L₁ : arith_lang} (S₁ S₂ : arith_struc L₁) :
  (∀ (p : Σ (n : ℕ+), L₁.to_lang.R n) 
     (p_int : (arithmetic_structure.arith_struc.to_struc S₁).R p.2 ),
    predicate_is_definable S₂.to_struc (by simp [arith_struc.to_struc]) p_int)
  → ∃ (M₂ : struc L₁), definable_predicates ↑S₁ M₂ ⊆ definable_predicates ↑S₂ M₂ :=
begin
  intro h,
  split,
  { intros x h₁,
    simp only [definable_predicates, set.mem_set_of] at h₁ ⊢,
    rcases h₁ with ⟨p_int, univ_eq, h'⟩,
    have s := h x p_int,
    use p_int,
    use univ_eq,
    exact s }
end

end definability