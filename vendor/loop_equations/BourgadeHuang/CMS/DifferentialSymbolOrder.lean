import BourgadeHuang.CMS.DifferentialSymbols
import Mathlib.Algebra.MvPolynomial.Degrees

/-! Multiplicity indices and order bounds for the faithful operator symbol. -/
noncomputable section
open scoped BigOperators
namespace BourgadeHuang.CMS
open GapExpression
variable {d : ℕ}

def wordIndex (u : List (Fin d)) : Fin d →₀ ℕ := (u.map (fun i=>Finsupp.single i 1)).sum

@[simp] theorem wordIndex_nil : wordIndex ([]:List (Fin d))=0 := rfl
@[simp] theorem wordIndex_cons (i : Fin d) (u : List (Fin d)) :
    wordIndex (i::u)=Finsupp.single i 1+wordIndex u := by simp [wordIndex]

theorem wordIndex_append (u v : List (Fin d)) : wordIndex (u++v)=wordIndex u+wordIndex v := by
  simp [wordIndex]

theorem wordIndex_apply (u : List (Fin d)) (i : Fin d) : wordIndex u i=u.count i := by
  induction u with
  | nil=>simp [wordIndex]
  | cons j u ih=>
    rw [wordIndex_cons,Finsupp.add_apply,ih]
    by_cases hji : j=i
    · subst j; simp [List.count_cons,add_comm]
    · simp [Finsupp.single_apply,List.count_cons,hji,Ne.symm hji]

theorem wordIndex_eq_iff_perm (u v : List (Fin d)) : wordIndex u=wordIndex v ↔ u.Perm v := by
  constructor
  · intro h
    apply List.perm_iff_count.mpr
    intro i
    simpa only [wordIndex_apply] using congrArg (fun w=>w i) h
  · intro h
    ext i
    simpa only [wordIndex_apply] using h.count_eq i

theorem wordIndex_degree (u : List (Fin d)) : (wordIndex u).sum (fun _ n=>n)=u.length := by
  induction u with
  | nil=>simp
  | cons i u ih=>
    rw [wordIndex_cons,Finsupp.sum_add_index' (fun _=>rfl) (fun _ _ _=>rfl),Finsupp.sum_single_index (by rfl),ih]
    simp [Nat.add_comm]

theorem wordSymbol_eq_monomial (u : List (Fin d)) : wordSymbol u=MvPolynomial.monomial (wordIndex u) (1:ℂ) := by
  induction u with
  | nil=>simp [wordSymbol]
  | cons i u ih=>
    simp only [wordSymbol,List.map_cons,List.prod_cons] at ih ⊢
    rw [ih,MvPolynomial.X,wordIndex_cons,MvPolynomial.monomial_mul,one_mul]

theorem coeff_wordSymbol (u : List (Fin d)) (a : Fin d →₀ ℕ) :
    MvPolynomial.coeff a (wordSymbol u)=if wordIndex u=a then (1:ℂ) else 0 := by
  rw [wordSymbol_eq_monomial,MvPolynomial.coeff_monomial]

theorem coeff_operatorSymbol (ts : List (LeibnizTerm d)) (z : Point d) (a : Fin d →₀ ℕ) :
    MvPolynomial.coeff a (operatorSymbol ts z)=
      (ts.map (fun t=>if wordIndex t.2=a then t.1.eval z else 0)).sum := by
  induction ts with
  | nil=>simp [operatorSymbol]
  | cons t ts ih=>
    simp only [operatorSymbol,List.map_cons,List.sum_cons,MvPolynomial.coeff_add] at ih ⊢
    rw [ih,wordSymbol_eq_monomial,MvPolynomial.C_mul_monomial,MvPolynomial.coeff_monomial]
    split_ifs <;> simp

theorem totalDegree_wordSymbol (u : List (Fin d)) : (wordSymbol u).totalDegree=u.length := by
  rw [wordSymbol_eq_monomial,MvPolynomial.totalDegree_monomial _ (by norm_num),wordIndex_degree]

theorem totalDegree_operatorSymbol_le (ts : List (LeibnizTerm d)) (z : Point d) (n : ℕ)
    (h : ∀e u,(e,u)∈ts→u.length≤n) : (operatorSymbol ts z).totalDegree≤n := by
  induction ts with
  | nil=>simp [operatorSymbol]
  | cons t ts ih=>
    simp only [operatorSymbol,List.map_cons,List.sum_cons]
    apply (MvPolynomial.totalDegree_add _ _).trans
    apply max_le
    · apply (MvPolynomial.totalDegree_mul _ _).trans
      rw [MvPolynomial.totalDegree_C,totalDegree_wordSymbol,zero_add]
      exact h _ _ (List.mem_cons_self ..)
    · exact ih (fun e u hu=>h e u (List.mem_cons_of_mem _ hu))

/-- A square-free differential expression has no coefficient at any repeated
coordinate symbol. -/
theorem coeff_operatorSymbol_eq_zero_of_squareFree
    (ts : List (LeibnizTerm d)) (z : Point d) (a : Fin d →₀ ℕ)
    (h : ∀e u,(e,u)∈ts→u.Nodup) (ha : ∃i,2≤a i) :
    MvPolynomial.coeff a (operatorSymbol ts z)=0 := by
  rw [coeff_operatorSymbol]
  apply List.sum_eq_zero
  intro x hx
  obtain ⟨⟨e,u⟩,hu,rfl⟩ := List.mem_map.mp hx
  have hne : wordIndex u≠a := by
    intro he
    obtain ⟨i,hi⟩ := ha
    have hc := List.nodup_iff_count_le_one.mp (h e u hu) i
    rw [←wordIndex_apply,he] at hc
    omega
  simp [hne]

end BourgadeHuang.CMS
