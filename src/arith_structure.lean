import model
import examples
import data.vector.mem

structure arith_lang : Type 1 :=
  (n : ℕ+)          -- number of relations
  (ar : fin n → ℕ+) -- arity of each relation

def arith_lang.to_lang (L : arith_lang) : lang :=
  {
    F := λ _, empty,
    R := λ x, let ar_vec := vector.of_fn L.ar in
              fin (ar_vec.to_list.count x),
    C := empty   
  }

/-- An arithmetic structure is a structure in which each relation is arithmetic,
i.e. can be defined in arithmreletics -/
structure arith_struc (L : arith_lang) :=
  (rels : vector (formula ordered_semiring_lang) L.n)            -- formulae defining relations
  (ar_proof : ∀i, formula.count_free_vars_list (rels.nth i) = L.ar i) -- proof that i-th relation has arity `p_ar[i]`)

namespace arithmetic_structure

instance arith_lang_to_lang_coe : has_coe (arith_lang) (lang) := ⟨arith_lang.to_lang⟩

open term

def convert_term_arith_lang {L₁ : arith_lang} (L₂ : arith_lang) : Π {n : ℕ}, term ↑L₁ n → term ↑L₂ n
| 0 (con c)    := by { unfold_coes at c, 
                       simp only [arith_lang.to_lang] at c,
                       cases c }
| 0 (var v)    := var v
| _ (func f)   := by { unfold_coes at f,
                       simp [arith_lang.to_lang] at f,
                       cases f }
| _ (app t t₀) := app (convert_term_arith_lang t) (convert_term_arith_lang t₀)

 
@[reducible] def list.index_of_nth_entry {α : Type*} [decidable_eq α] (l : list α) (n : ℕ) (x : α) (h : n < l.count x) : ℕ :=
  let indices := l.indexes_of x in
  indices.nth_le n (by {
    simp only [indices, list.indexes_of, list.find_indexes_eq_map_indexes_values,
               list.indexes_values_eq_filter_enum, list.length_map],

    rw [← list.length_map (prod.snd) _, ← list.map_filter (eq x) (prod.snd) l.enum,
        ← list.countp_eq_length_filter, ← list.count],
    simp [h]
  })

lemma list.forall_indexes_of_lt_length {α : Type*} [decidable_eq α] (l : list α) (x : α) :
  ∀ i ∈ l.indexes_of x, i < l.length :=
begin
  intros i h,
  simp only [list.indexes_of, list.find_indexes_eq_map_indexes_values,
             list.indexes_values_eq_filter_enum, list.mem_map,
             list.mem_filter] at h,
  cases h,
  have h₁ := h_h.1.1,
  have h₂ := h_h.2,

  cases h_w,
  simp only [list.enum] at h₁,
  have h₃ := list.mem_enum_from l h₁,
  simp at h₂ h₃,
  simp [← h₂, h₃]
end

lemma index_of_nth_entry_lt_length {α : Type*} [decidable_eq α] (l : list α) (n : ℕ) (x : α) (h₁ : n < l.count x) :
  l.index_of_nth_entry n x h₁ < l.length :=
begin
  simp only [list.index_of_nth_entry],

  have h' : n < (list.indexes_of x l).length := by {
    simp only [list.indexes_of, list.find_indexes_eq_map_indexes_values,
               list.indexes_values_eq_filter_enum, list.length_map],

    rw [← list.length_map (prod.snd) _, ← list.map_filter (eq x) (prod.snd) l.enum,
        ← list.countp_eq_length_filter, ← list.count],
    simp [h₁]
  },
  let i := (list.indexes_of x l).nth_le n h',
  simp only [←i], 
  have h'' := l.forall_indexes_of_lt_length x i,
  exact h'' ((l.indexes_of x).nth_le_mem n h')
end

lemma list.nth_index_of_nth_entry_eq {α : Type*} [decidable_eq α] (l : list α) (n : ℕ) (x : α) (h : n < l.count x) :
  l.nth_le (l.index_of_nth_entry n x h) (index_of_nth_entry_lt_length l n x h) = x :=
begin
  simp [list.index_of_nth_entry, list.indexes_of, 
        list.find_indexes_eq_map_indexes_values, list.indexes_values_eq_filter_enum],
  
  have h₁ : n < (list.filter (eq x ∘ prod.snd) l.enum).length,
  { rw [← list.length_map (prod.snd) _, ← list.map_filter (eq x) (prod.snd) l.enum,
        ← list.countp_eq_length_filter, ← list.count],
    simp [h] },
  
  have h₂ := list.nth_le_mem (list.filter (eq x ∘ prod.snd) l.enum) n h₁,
  simp at h₂,
  simp only [list.mem_iff_nth_le] at h₂,
  have h₃ := h₂.1,
  rcases h₃ with ⟨i, h', h''⟩,
  have h₄ := list.nth_le_enum l i h',
  simp only [← h'', h₄],
  have h₅ := h₂.2,
  simp only [← h'', h₄] at h₅,
  simp [h₅]
end

def arith_struc.to_struc {L : arith_lang} (S : arith_struc L) : struc L :=
  {
    univ := ℕ,
    F := λ _, empty.elim,
    C := empty.elim,
    R := λ x r, let ar_vec := vector.of_fn L.ar in
                  let ⟨r_val, r_property⟩ := r in
                  if (ar_vec.to_list.count x) = 0 then ∅ 
                  else 
                    let index := (vector.of_fn L.ar).to_list.index_of_nth_entry r_val x r_property in
                    let φ := S.rels.nth index in
                    let free_vars := φ.free_vars_list in

                    {v : vector ℕ x |
                      let va : ℕ → N_arith_semiring.univ := λ var,
                        if var_mem : var ∈ free_vars 
                        then
                          v.to_list.nth_le 
                            (free_vars.index_of var) 
                            (by { 
                              simp,
                              have h₁ : free_vars.length = ↑x,
                              { have h₂ := S.ar_proof index,
                                simp [← φ] at h₂,
                                have l_ar_eq_x := list.nth_index_of_nth_entry_eq (vector.of_fn L.ar).to_list r_val x r_property,
                                have h₃ : (vector.of_fn L.ar).to_list = list.of_fn L.ar,
                                { simp },
                                simp only [← index] at l_ar_eq_x,
                                simp only [h₃] at l_ar_eq_x,
                                have h₄ : (list.of_fn L.ar).nth_le index (by {
                                  have index_lt := index_of_nth_entry_lt_length (vector.of_fn L.ar).to_list r_val x r_property,
                                  simp only [index],
                                  have of_fn_to_list : (vector.of_fn L.ar).to_list = list.of_fn L.ar,
                                  { simp },
                                  simp only [← of_fn_to_list, index_lt]
                                }) = L.ar index,
                                { have h₅ := list.nth_le_of_fn L.ar index,
                                  simp [← h₅],
                                  have h₆ : index < ↑(L.n),
                                  { have index_lt := index_of_nth_entry_lt_length (vector.of_fn L.ar).to_list r_val x r_property,
                                    simp only [← index] at index_lt,
                                    simp at index_lt,
                                    exact index_lt },
                                  simp only [nat.mod_eq_of_lt h₆] },

                                simp only [h₄] at l_ar_eq_x,
                                simp only [l_ar_eq_x] at h₂,
                                simp only [← h₂],
                              },

                              simp only [← list.index_of_lt_length] at var_mem, 
                              exact lt_of_lt_of_eq var_mem h₁
                            })
                        else @default N_arith_semiring.univ N_arith_semiring.univ_inhabited
                      in
                    va ⊨ φ
                    }
  }

instance arith_struc_to_struc_coe {L : arith_lang} : has_coe (arith_struc L) (struc L) := ⟨arith_struc.to_struc⟩

lemma term_conversion_preserves_interpretation {L₁ L₂ : arith_lang} (S₁ : arith_struc L₁) (S₂ : arith_struc L₂) {n : ℕ} :
  ∀ (t : term L₁ n), 
    ∀ (va : ℕ → ℕ),
      @term_interpretation ↑L₁ ↑S₁ va n t = 
      @term_interpretation ↑L₂ ↑S₂ va n (convert_term_arith_lang L₂ t) :=
begin
  intros t va,
  
  induction t,
  { unfold_coes at t,
    simp only [arith_lang.to_lang] at t,
    cases t },
  { simp only [convert_term_arith_lang, term_interpretation] },
  { unfold_coes at t_ᾰ,
    simp only [arith_lang.to_lang] at t_ᾰ,
    cases t_ᾰ },
  { simp only [convert_term_arith_lang, term_interpretation,
               t_ih_ᾰ, t_ih_ᾰ_1] }
end

def rel_to_formula {L : arith_lang} (S : arith_struc L) {n : ℕ+} 
                   (rel : L.to_lang.R n) (v : vector (term ↑L 0) n)
                   (h : n ∈ list.of_fn L.ar) :
  ∃ pred ∈ S.rels.to_list,
    ∀ (va : ℕ → ℕ),
      @models_formula ↑L S.to_struc va (formula.rel rel v) ↔ 
      @models_formula ordered_semiring_lang N_arith_semiring va pred :=
begin
  cases rel,
  let index := (vector.of_fn L.ar).to_list.index_of_nth_entry rel_val n rel_property,
  use S.rels.nth index,
  split,
  -- Seems obvious but hard to prove.
  { simp },
  { intro va,
    simp only [models_formula],
    dsimp [arith_struc.to_struc],
    simp [if_pos h],
    sorry }
end

lemma exists_formula_ordered_semiring_lang {L : arith_lang} (S : arith_struc L) (φ : formula ↑L) :
    ∃ (ψ : formula ordered_semiring_lang),
      ∀ (va : ℕ → ℕ),
        @models_formula L S va φ ↔ 
        @models_formula ordered_semiring_lang N_arith_semiring va ψ :=
begin
  induction φ,
  { use ⊤', simp },
  { use ⊥', simp },
  { sorry },
  { sorry },
  -- { have γ := rel_to_formula S φ_ᾰ φ_ᾰ_1,
  --   use γ,
  --   simp [γ, formula_rel_iff_rel_to_formula] },
  { cases φ_ih,
    use (¬' φ_ih_w),
    simp [models_formula, not_iff_not, φ_ih_h] },
  { cases φ_ih_ᾰ with α α_h,
    cases φ_ih_ᾰ_1 with β β_h,
    use (α ∧' β),
    simp [models_formula, α_h, β_h] },
  { cases φ_ih_ᾰ with α α_h,
    cases φ_ih_ᾰ_1 with β β_h,
    use (α ∨' β),
    simp [models_formula, α_h, β_h] },
  { cases φ_ih with α α_h,
    use (∃' φ_ᾰ α),
    intro va,
    simp only [models_formula],
    --  TODO: seems easy: `va ⊨ φ_ᾰ_1 ↔ va ⊨ α`, so if we change va at one particular point, then `va ⊨ φ_ᾰ_1 ↔ va ⊨ α` still holds
    sorry },
  { cases φ_ih with α α_h,
    use (∀' φ_ᾰ α),
    intro va,
    simp only [models_formula],
    -- TODO: seems similar to the previous.
    sorry }
end

end arithmetic_structure