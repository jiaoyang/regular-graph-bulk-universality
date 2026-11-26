import BourgadeHuang.CMS.DifferentialSymbolOrder

/-! Each differentiated PDE row has its monic repeated-coordinate principal
symbol and a strictly lower-order remainder. -/
noncomputable section
open scoped BigOperators Topology
open Set Filter
namespace BourgadeHuang.CMS
open GapExpression
variable {d : ℕ}

theorem stepTerms_word_length_le (i : Fin d) (ts : List (LeibnizTerm d)) (n : ℕ)
    (h : ∀e u,(e,u)∈ts→u.length≤n) : ∀e u,(e,u)∈stepTerms i ts→u.length≤n+1 := by
  induction ts with
  | nil=>simp [stepTerms]
  | cons t ts ih=>
    rcases t with ⟨a,v⟩
    intro e u hu
    simp only [stepTerms,List.mem_cons,Prod.mk.injEq] at hu
    rcases hu with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|hu
    · exact (h _ _ (List.mem_cons_self ..)).trans (Nat.le_succ _)
    · simpa only [List.length_cons] using Nat.succ_le_succ (h _ _ (List.mem_cons_self ..))
    · exact ih (fun e u hu=>h e u (List.mem_cons_of_mem _ hu)) e u hu

theorem leibnizTerms_word_length_le (e : GapExpression d) (u : List (Fin d)) :
    ∀a v,(a,v)∈leibnizTerms e u→v.length≤u.length := by
  induction u with
  | nil=>
    intro a v h
    simp only [leibnizTerms,List.mem_singleton,Prod.mk.injEq] at h
    simp only [h.2,List.length_nil,le_refl]
  | cons i u ih=>simpa only [leibnizTerms,List.length_cons] using
      stepTerms_word_length_le i (leibnizTerms e u) u.length ih

theorem expandTerms_word_length_le (u : List (Fin d)) (ts : List (LeibnizTerm d)) (n : ℕ)
    (h : ∀e v,(e,v)∈ts→v.length≤n) : ∀e v,(e,v)∈expandTerms u ts→v.length≤u.length+n := by
  intro e v hv
  obtain ⟨a,w,hw,t,ht,rfl⟩ := GapExpression.mem_expandTerms u ts hv
  rw [List.length_append]
  exact Nat.add_le_add (leibnizTerms_word_length_le a u e t ht) (h a w hw)

theorem operatorSymbol_append (ts us : List (LeibnizTerm d)) (z : Point d) :
    operatorSymbol (ts++us) z=operatorSymbol ts z+operatorSymbol us z := by simp [operatorSymbol]

theorem operatorSymbol_scale (a : GapExpression d) (ts : List (LeibnizTerm d)) (z : Point d) :
    operatorSymbol (scaleTerms a ts) z=MvPolynomial.C (a.eval z)*operatorSymbol ts z := by
  induction ts with
  | nil=>simp [scaleTerms,operatorSymbol]
  | cons t ts ih=>
    simp only [scaleTerms,List.map_cons,operatorSymbol,List.sum_cons,GapExpression.eval,map_mul] at ih ⊢
    rw [ih]
    ring

namespace SectorialData

/-- A residual row is expanded into its monic principal term and a lower-order
ordinary differential expression, retaining all coefficient derivatives. -/
def residualOperatorTerms (D : SectorialData d) : List (DifferentialResidualTerm d) → List (LeibnizTerm d)
  | []=>[]
  | t::ts=>(t.coefficient,t.word++[t.source,t.source])::
      (scaleTerms t.coefficient (expandTerms t.word (D.lowerTerms t.source))++D.residualOperatorTerms ts)

theorem termSum_residualOperatorTerms (D : SectorialData d) (rs : List (DifferentialResidualTerm d))
    {f : Point d → ℂ} (hf : AnalyticOnNhd ℂ f (OrderedDomain d)) :
    EqOn (termSum (D.residualOperatorTerms rs) f) (D.residualSum rs f) (OrderedDomain d) := by
  induction rs with
  | nil=>intro z hz; rfl
  | cons t rs ih=>
    intro z hz
    have hop : D.operator t.source f=secondPartial t.source f+termSum (D.lowerTerms t.source) f := by
      funext w
      change D.operator t.source f w=secondPartial t.source f w+termSum (D.lowerTerms t.source) f w
      rw [termSum_lowerTerms]
      ring
    have hsplit := wordDerivative_add t.word (orderedDomain_isOpen d)
      (f:=secondPartial t.source f) (g:=termSum (D.lowerTerms t.source) f)
      (fun w hw=>analyticAt_coordDeriv (analyticAt_coordDeriv (hf w hw) t.source) t.source)
      (fun w hw=>analyticAt_termSum (D.lowerTerms t.source) (hf w hw) (orderedDomain_collisionFree hw)) hz
    have hw : wordDerivative t.word (D.operator t.source f) z=
        wordDerivative (t.word++[t.source,t.source]) f z+
          termSum (expandTerms t.word (D.lowerTerms t.source)) f z := by
      rw [hop,hsplit]
      change wordDerivative t.word (secondPartial t.source f) z+
        wordDerivative t.word (termSum (D.lowerTerms t.source) f) z=_
      rw [wordDerivative_termSum _ _ (orderedDomain_isOpen d) (fun _ hw=>orderedDomain_collisionFree hw) hf hz,
        wordDerivative_append]
      rfl
    simp only [residualOperatorTerms,termSum,termSum_append,termSum_scaleTerms,residualSum,ih hz,hw]
    ring

/-- The correction in each left multiple has one fewer derivative than its
monic principal term. -/
theorem residual_lower_totalDegree (D : SectorialData d) (t : DifferentialResidualTerm d) (z : Point d) :
    (operatorSymbol (scaleTerms t.coefficient (expandTerms t.word (D.lowerTerms t.source))) z).totalDegree≤
      t.word.length+1 := by
  rw [operatorSymbol_scale]
  apply (MvPolynomial.totalDegree_mul _ _).trans
  rw [MvPolynomial.totalDegree_C,zero_add]
  exact totalDegree_operatorSymbol_le _ z _
    (expandTerms_word_length_le t.word (D.lowerTerms t.source) 1 (D.lowerTerms_word_length_le t.source))

/-- At the largest possible row order only the monic repeated-coordinate
terms contribute; every differentiated lower coefficient drops out. -/
theorem coeff_residualOperatorTerms_top (D : SectorialData d) (rs : List (DifferentialResidualTerm d))
    (z : Point d) (n : ℕ) (a : Fin d →₀ ℕ)
    (ha : a.sum (fun _ m=>m)=n+2) (horder : ∀t∈rs,t.word.length≤n) :
    MvPolynomial.coeff a (operatorSymbol (D.residualOperatorTerms rs) z)=
      (rs.map (fun t=>if wordIndex (t.word++[t.source,t.source])=a then t.coefficient.eval z else 0)).sum := by
  induction rs with
  | nil=>simp [residualOperatorTerms,operatorSymbol]
  | cons t rs ih=>
    have hlow : MvPolynomial.coeff a
        (operatorSymbol (scaleTerms t.coefficient (expandTerms t.word (D.lowerTerms t.source))) z)=0 := by
      apply MvPolynomial.coeff_eq_zero_of_totalDegree_lt
      change _<a.sum (fun _ m=>m)
      rw [ha]
      have ht := horder t (List.mem_cons_self ..)
      exact (D.residual_lower_totalDegree t z).trans_lt (by omega)
    have htail := ih (fun t ht=>horder t (List.mem_cons_of_mem _ ht))
    change MvPolynomial.coeff a
      (operatorSymbol ([(t.coefficient,t.word++[t.source,t.source])]++
        scaleTerms t.coefficient (expandTerms t.word (D.lowerTerms t.source))++D.residualOperatorTerms rs) z)=_
    rw [operatorSymbol_append,operatorSymbol_append,MvPolynomial.coeff_add,MvPolynomial.coeff_add,
      hlow,htail,coeff_operatorSymbol]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,zero_add]

/-- Leading coefficient cancellation is forced by a square-free ideal
identity. This uses all analytic tests through the faithful full symbol. -/
theorem principal_residual_cancellation (D : SectorialData d)
    (ts us : List (LeibnizTerm d)) (rs : List (DifferentialResidualTerm d))
    (hidentity : ∀f,AnalyticOnNhd ℂ f (OrderedDomain d)→∀z∈OrderedDomain d,
      termSum ts f z=termSum us f z+D.residualSum rs f z)
    (hts : ∀e u,(e,u)∈ts→u.Nodup) (hus : ∀e u,(e,u)∈us→u.Nodup)
    (n : ℕ) (horder : ∀t∈rs,t.word.length≤n)
    (a : Fin d →₀ ℕ) (ha : a.sum (fun _ m=>m)=n+2) (harep : ∃i,2≤a i)
    {z : Point d} (hz : z∈OrderedDomain d) :
    (rs.map (fun t=>if wordIndex (t.word++[t.source,t.source])=a then t.coefficient.eval z else 0)).sum=0 := by
  have he := operatorSymbol_eq_of_identity ts (us++D.residualOperatorTerms rs) hz (by
    intro f hf z hz
    rw [termSum_append,D.termSum_residualOperatorTerms rs hf hz]
    exact hidentity f hf z hz)
  have hc := congrArg (MvPolynomial.coeff a) he
  rw [operatorSymbol_append,MvPolynomial.coeff_add,
    coeff_operatorSymbol_eq_zero_of_squareFree ts z a hts harep,
    coeff_operatorSymbol_eq_zero_of_squareFree us z a hus harep,
    D.coeff_residualOperatorTerms_top rs z n a ha horder,zero_add] at hc
  exact hc.symm

end SectorialData
end BourgadeHuang.CMS
