import model
import examples
import data.list

def arith_lang (n : ℕ+) (ar : fin n → ℕ+) : lang :=
  {
    F := λ _, empty,
    C := empty,
    R := λ x, let ar_vec := vector.of_fn ar in 
              if x ∈ ar_vec.to_list then fin (ar_vec.to_list.count x) else empty
  }

/-- An arithmetic structure is a structure in which each relation is arithmetic,
i.e. can be defined in arithmetics -/
structure arith_struc :=           
(n : ℕ+)            -- number of relations
(p_ar : fin n → ℕ+) -- arity of each relation
(rels : vector (formula ordered_semiring_lang) n) -- formulae defining relations
(ar_proof : ∀i, formula.count_free_vars (rels.nth i) = p_ar i) -- proof that i-th relation has arity p_ar[i]

namespace arithmetic_structure

open term

def f_add : ordered_semiring_lang.F 2 := sorry 
def f_mul : ordered_semiring_lang.F 2 := sorry
def f_leq : ordered_semiring_lang.F 2 := sorry

infix ` +' ` : 70 := λ a b, app (app (func f_add) a) b
infix ` *' ` : 80 := λ a b, app (app (func f_mul) a) b  
infix ` ≤' ` : 60 := λ a b, app (app (func f_leq) a) b 

def x : term ordered_semiring_lang 0 := var 0
def y : term ordered_semiring_lang 0 := var 1
def z : term ordered_semiring_lang 0 := var 2


@[reducible] def φ₁ : formula ordered_semiring_lang := ∃' 2 (z =' (x +' y))
@[reducible] def φ₂ : formula ordered_semiring_lang := ∃' 2 (y =' (x +' z))
@[reducible] def φ₃ : formula ordered_semiring_lang := ∃' 2 (y =' (x *' z))

/-- ⟨ℕ, ×, +, ≤⟩ 
x × y := ∃z : x × y = z
x + y := ∃z : x + y = z   
x ≤ y := ∃z : x + z = y -/
def ordered_semiring_is_arithmetic_structure : arith_struc :=
  { 
    n := 3,
    p_ar := λ n, by { cases n, cases n_val,
                      { exact 2 },
                      cases n_val,
                      { exact 2 },
                      cases n_val,
                      { exact 2 },
                      { repeat {rw nat.succ_eq_add_one at n_property},
                        simp at n_property,
                        linarith } },
    rels := ⟨[φ₁, φ₂, φ₃], rfl⟩,
    ar_proof := 
    begin
      intro i,
      cases i,
      cases i_val,
      { ring },
      cases i_val,
      { ring },
      cases i_val,
      { ring },
      exfalso,
      repeat {rw nat.succ_eq_add_one at i_property},
      ring at i_property,
      simp at i_property,
      rw ← not_le at i_property,
      exact i_property (zero_le i_val)
    end
  }

def find_nth {α : Type*} [decidable_eq α] : Π (l : list α) (n) (x), (n < l.count x) → ℕ
| []         _       _ h := by { simp at h, linarith }
| (hd :: tl) 0       _ h := 0
| (hd :: tl) (n + 1) x h := if h' : hd = x then 
                              1 + (find_nth tl n x (by { simp [h'] at h,
                                                      rw nat.succ_eq_add_one at h,
                                                      simp at h,
                                                      exact h }))
                            else find_nth tl n x (by { rw ← ne.def at h',
                                                       rw list.count_cons_of_ne at h,
                                                       have h'' := lt_add_one n,
                                                       exact lt_trans h'' h,
                                                       symmetry,
                                                       exact h' })

def arith_struc.to_struc (S : arith_struc) : struc (arith_lang S.n S.p_ar) :=
  {
    univ := ℕ,
    F := λ _, empty.elim,
    C := empty.elim,
    R := λ x r v, let ar_vec := vector.of_fn S.p_ar in
                  if h : x ∈ ar_vec.to_list then
                  by { simp only [arith_lang] at r,
                       rw if_pos h at r,
                       cases r,
                       let index := find_nth (vector.of_fn S.p_ar).to_list r_val x r_property,
                       let φ := option.get_or_else (S.rels.to_list.nth index) sorry,

                       let va : ℕ → N_arith_semiring.univ := λ var, 
                        if var_property : var < v.to_list.length then v.to_list.nth_le var var_property
                        else sorry,
                       
                       exact (va ⊨ φ) }
                  else false
  }

end arithmetic_structure