import model
import examples

-- def arith_lang (n : ℕ+) (ar : fin n → ℕ+) : lang :=
--   {
--     F := λ _, empty,
--     C := empty,
--     R := λ x, let ar_vec := vector.of_fn ar in 
--               if x ∈ ar_vec.to_list then fin (ar_vec.to_list.count x) else empty
--   }

structure arith_lang : Type 1 :=
  (n : ℕ+)          -- number of relations
  (ar : fin n → ℕ+) --arity of each relation

def arith_lang.to_lang (L : arith_lang) : lang :=
  {
    F := λ _, empty,
    R := λ x, let ar_vec := vector.of_fn L.ar in
              if x ∈ ar_vec.to_list then fin (ar_vec.to_list.count x) else empty,
    C := empty   
  }

/-- An arithmetic structure is a structure in which each relation is arithmetic,
i.e. can be defined in arithmetics -/
structure arith_struc (L : arith_lang) :=
  (rels : vector (formula ordered_semiring_lang) L.n)            -- formulae defining relations
  (ar_proof : ∀i, formula.count_free_vars (rels.nth i) = L.ar i) -- proof that i-th relation has arity `p_ar[i]`)

-- structure arith_struc :=           
-- (n : ℕ+)            -- number of relations
-- (p_ar : fin n → ℕ+) -- arity of each relation
-- (rels : vector (formula ordered_semiring_lang) n) -- formulae defining relations
-- (ar_proof : ∀i, formula.count_free_vars (rels.nth i) = p_ar i) -- proof that i-th relation has arity p_ar[i]

namespace arithmetic_structure

instance arith_lang_to_lang_coe : has_coe (arith_lang) (lang) := ⟨arith_lang.to_lang⟩
 
-- @[reducible] def find_nth {α : Type*} [decidable_eq α] : Π (l : list α) (n) (x), (n < l.count x) → ℕ
-- | []         _       _ h := by { simp at h, contradiction }
-- | (hd :: tl) 0       x h := if h' : hd = x then 
-- | (hd :: tl) (i + 1) x h := if h' : hd = x then 
--                               1 + (find_nth tl i x (by { simp [h'] at h, exact h }))
--                             else find_nth tl i x (by { rw ← ne.def at h',
--                                                        rw list.count_cons_of_ne at h,
--                                                        have h'' := lt_add_one i,
--                                                        exact lt_trans h'' h,
--                                                        symmetry,
--                                                        exact h' })

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
  induction (l.indexes_of x),
  { intros,
    simp at H,
    contradiction },
  { intros,
    cases (list.eq_or_mem_of_mem_cons H),
    { sorry },
    { exact ih i h } }
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

def arith_struc.to_struc {L : arith_lang} (S : arith_struc L) : struc L :=
  {
    univ := ℕ,
    F := λ _, empty.elim,
    C := empty.elim,
    R := λ x r v, let ar_vec := vector.of_fn L.ar in
                  if h : x ∈ ar_vec.to_list then
                  by { unfold_coes at r, 
                       simp only [arith_lang.to_lang] at r,
                       rw if_pos h at r,
                       cases r,
                       let index := (vector.of_fn L.ar).to_list.index_of_nth_entry r_val x r_property,

                       let φ := S.rels.to_list.nth_le index (by {
                        have h' := index_of_nth_entry_lt_length (vector.of_fn L.ar).to_list r_val x r_property,
                        simp [vector.length] at h' ⊢,
                        simp [index, h']
                       }),
                       let free_vars := φ.free_vars_list,

                       let va : ℕ → N_arith_semiring.univ := λ var, 
                        if var ∈ free_vars 
                        then
                          v.to_list.nth_le 
                            (free_vars.index_of var) 
                            (by { 
                              have h' := S.ar_proof index,
                              sorry  
                            })
                        else sorry,
                      
                       exact (va ⊨ φ),
                     }
                  else false
  }

instance arith_struc_to_struc_coe {L : arith_lang} : has_coe (arith_struc L) (struc L) := ⟨arith_struc.to_struc⟩

end arithmetic_structure