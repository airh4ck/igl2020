import model
import arith_structure
import util

namespace definability

variable {L : lang}

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
def definable_predicates (M₁ : struc L) : set (Σ (n : ℕ+), L.R n) :=
    { p : Σ (n : ℕ+), L.R n | 
      ∃ (M₂ : struc L) (p_int : M₂.R p.2) (univ_eq : M₁.univ = M₂.univ), 
        predicate_is_definable M₁ univ_eq p_int }

lemma mem_of_definable_predicates_iff_definable (M : struc L) {x : Σ (n : ℕ+), L.R n} :
  x ∈ definable_predicates M ↔ ∃ (M' : struc L) (p_int : M'.R x.2) (univ_eq : M.univ = M'.univ),
                               predicate_is_definable M univ_eq p_int :=
begin
  simp only [definable_predicates, set.mem_set_of]
end

open arithmetic_structure
theorem subset_if_predicates_definable {L₁ : arith_lang} (S₁ S₂ : arith_struc L₁) :
  (∀ (p : Σ (n : ℕ+), L₁.to_lang.R n) 
     (p_int : (arithmetic_structure.arith_struc.to_struc S₁).R p.2 ), 
    predicate_is_definable S₂.to_struc (by simp [arith_struc.to_struc]) p_int)
  → definable_predicates S₁.to_struc ⊆ definable_predicates S₂.to_struc :=
begin
  intros h x x_property,
  simp only [predicate_is_definable] at h,
  
  simp only [mem_of_definable_predicates_iff_definable, predicate_is_definable] at x_property ⊢,
  sorry
end

end definability