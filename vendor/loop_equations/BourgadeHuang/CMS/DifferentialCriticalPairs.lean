import BourgadeHuang.CMS.DifferentialCertificates
import BourgadeHuang.CMS.GaugeCommutators
import BourgadeHuang.CMS.SectorialNormalForm

/-! The actual sectorial commutator gives an explicit lower-order resolution
of every pair of repeated-coordinate PDE rows. This is the critical-pair
identity used by differential-ideal confluence, on arbitrary analytic tests. -/
noncomputable section
open scoped BigOperators Topology
open Set Filter
namespace BourgadeHuang.CMS
open GapExpression
namespace SectorialData
variable {d : ℕ}

theorem operator_congr_nhds (D : SectorialData d) (i : Fin d)
    {f g : Point d → ℂ} {z : Point d} (hfg : f=ᶠ[𝓝 z] g) : D.operator i f z=D.operator i g z := by
  simp only [operator,secondPartial_congr_nhds hfg,coordDeriv_congr_nhds hfg,hfg.eq_of_nhds]

/-- Compatibility in the exact `SectorialData.operator` interface. -/
theorem general_operator_commutator (β : ℂ) (c : Fin d → ℂ) (σ : Fin d → Sign)
    (i j : Fin d) {f : Point d → ℂ} {z : Point d}
    (hf : AnalyticAt ℂ f z) (hz : z∈OrderedDomain d) (hij : i≠j)
    (hβ : β≠0) (hc : ∀k,c k= -1 ∨ c k=β/2) :
    (general β c σ).operator i ((general β c σ).operator j f) z-
      (general β c σ).operator j ((general β c σ).operator i f) z=
      (4/β)/(z i-z j)^2*(c i^2*(general β c σ).operator j f z-
        c j^2*(general β c σ).operator i f z) := by
  have he (a b : Fin d) : (general β c σ).operator a ((general β c σ).operator b f) z=
      sectorialOperator β c σ a (sectorialOperator β c σ b f) z := by
    rw [operator_congr_nhds _ a (Filter.eventuallyEq_of_mem ((orderedDomain_isOpen d).mem_nhds hz)
      (fun w hw=>operator_general β c σ b f hw)),operator_general β c σ a _ hz]
  rw [he,he,operator_general β c σ j f hz,operator_general β c σ i f hz]
  exact sectorialOperator_commutator β c σ i j hf hz hij hβ hc

/-- The order-at-most-one part after removing the monic square derivative. -/
def lowerTerms (D : SectorialData d) (i : Fin d) : List (LeibnizTerm d) :=
  (.const (D.phase i),[i])::D.remainderTerms i

theorem termSum_lowerTerms (D : SectorialData d) (i : Fin d) (f : Point d → ℂ) (z : Point d) :
    termSum (D.lowerTerms i) f z=D.operator i f z-secondPartial i f z := by
  simp only [lowerTerms,termSum,GapExpression.eval,wordDerivative,D.termSum_remainderTerms,operator]
  ring

def liftResiduals (i : Fin d) (ts : List (LeibnizTerm d)) : List (DifferentialResidualTerm d) :=
  ts.map (fun t=>⟨t.1,t.2,i⟩)

theorem residualSum_liftResiduals (D : SectorialData d) (i : Fin d) (ts : List (LeibnizTerm d))
    (f : Point d → ℂ) (z : Point d) :
    D.residualSum (liftResiduals i ts) f z=termSum ts (D.operator i f) z := by
  induction ts with
  | nil=>rfl
  | cons t ts ih=>simp only [liftResiduals,List.map_cons,residualSum,termSum] at ih ⊢; rw [ih]

def criticalFactor (β : ℂ) (i j : Fin d) : GapExpression d :=
  .mul (.const (4/β)) (.mul (GapExpression.inverseGap i j) (GapExpression.inverseGap i j))

theorem eval_criticalFactor (β : ℂ) (i j : Fin d) (z : Point d) :
    (criticalFactor β i j).eval z=(4/β)/(z i-z j)^2 := by
  simp only [criticalFactor,GapExpression.eval,GapExpression.eval_inverseGap,div_eq_mul_inv]
  rw [←inv_pow]
  ring

/-- The degree-lowering replacement of a repeated-pair overlap. -/
def criticalResiduals (β : ℂ) (c : Fin d → ℂ) (σ : Fin d → Sign) (i j : Fin d) :
    List (DifferentialResidualTerm d) :=
  liftResiduals j ((general β c σ).lowerTerms i)++
    scaleResiduals (.const (-1)) (liftResiduals i ((general β c σ).lowerTerms j))++
    [⟨.mul (criticalFactor β i j) (.const (c j^2)),[],i⟩,
     ⟨.mul (criticalFactor β i j) (.const (-(c i^2))),[],j⟩]

/-- Actual compatibility resolves the critical overlap into first-order
left multiples of the PDE rows. -/
theorem residualSum_criticalPair (β : ℂ) (c : Fin d → ℂ) (σ : Fin d → Sign)
    (i j : Fin d) {f : Point d → ℂ} {z : Point d}
    (hf : AnalyticAt ℂ f z) (hz : z∈OrderedDomain d) (hij : i≠j)
    (hβ : β≠0) (hc : ∀k,c k= -1 ∨ c k=β/2) :
    (general β c σ).residualSum [⟨.const 1,[j,j],i⟩,⟨.const (-1),[i,i],j⟩] f z=
      (general β c σ).residualSum (criticalResiduals β c σ i j) f z := by
  have h := general_operator_commutator β c σ i j hf hz hij hβ hc
  simp only [criticalResiduals,residualSum_append,residualSum_liftResiduals,residualSum_scaleResiduals,
    residualSum,GapExpression.eval,wordDerivative,one_mul,add_zero,eval_criticalFactor,termSum_lowerTerms]
  simp only [secondPartial] at h ⊢
  linear_combination -h

/-- Equivalence of stored PDE residuals on all analytic tests. -/
def ResidualEquivalent (D : SectorialData d) (rs qs : List (DifferentialResidualTerm d)) : Prop :=
  ∀f,AnalyticOnNhd ℂ f (OrderedDomain d)→EqOn (D.residualSum rs f) (D.residualSum qs f) (OrderedDomain d)

theorem ResidualEquivalent.expand {D : SectorialData d} {rs qs : List (DifferentialResidualTerm d)}
    (h : D.ResidualEquivalent rs qs) (u : List (Fin d)) :
    D.ResidualEquivalent (expandResiduals u rs) (expandResiduals u qs) := by
  intro f hf z hz
  have hh := wordDerivative_congr u (orderedDomain_isOpen d) (h f hf) hz
  rw [D.wordDerivative_residualSum u rs hf hz,D.wordDerivative_residualSum u qs hf hz] at hh
  exact hh

/-- The compatibility identity remains certified after every outer word of
coordinate derivatives. -/
theorem criticalPair_equivalent (β : ℂ) (c : Fin d → ℂ) (σ : Fin d → Sign)
    (i j : Fin d) (hij : i≠j) (hβ : β≠0) (hc : ∀k,c k= -1 ∨ c k=β/2)
    (u : List (Fin d)) :
    (general β c σ).ResidualEquivalent
      (expandResiduals u [⟨.const 1,[j,j],i⟩,⟨.const (-1),[i,i],j⟩])
      (expandResiduals u (criticalResiduals β c σ i j)) := by
  apply ResidualEquivalent.expand
  intro f hf z hz
  exact residualSum_criticalPair β c σ i j (hf z hz) hz hij hβ hc

/-- Differentiating a residual raises its left-operator order by at most one. -/
theorem stepResiduals_word_length_le (i : Fin d) (rs : List (DifferentialResidualTerm d)) (n : ℕ)
    (h : ∀t∈rs,t.word.length≤n) : ∀t∈stepResiduals i rs,t.word.length≤n+1 := by
  induction rs with
  | nil=>simp [stepResiduals]
  | cons r rs ih=>
    intro t ht
    simp only [stepResiduals,List.mem_cons] at ht
    rcases ht with rfl|rfl|ht
    · exact (h r (List.mem_cons_self ..)).trans (Nat.le_succ _)
    · simpa only [List.length_cons] using Nat.succ_le_succ (h r (List.mem_cons_self ..))
    · exact ih (fun q hq=>h q (List.mem_cons_of_mem _ hq)) t ht

theorem expandResiduals_word_length_le (u : List (Fin d)) (rs : List (DifferentialResidualTerm d)) (n : ℕ)
    (h : ∀t∈rs,t.word.length≤n) : ∀t∈expandResiduals u rs,t.word.length≤n+u.length := by
  induction u with
  | nil=>simpa only [expandResiduals,List.length_nil,Nat.add_zero] using h
  | cons i u ih=>
    simpa only [expandResiduals,List.length_cons,Nat.add_assoc] using
      stepResiduals_word_length_le i (expandResiduals u rs) (n+u.length) ih

theorem lowerTerms_word_length_le (D : SectorialData d) (i : Fin d) :
    ∀e v,(e,v)∈D.lowerTerms i→v.length≤1 := by
  intro e v hv
  simp only [lowerTerms,List.mem_cons,Prod.mk.injEq] at hv
  rcases hv with ⟨rfl,rfl⟩|hv
  · simp
  · rcases D.remainderTerms_spec i hv with ⟨j,rfl,rfl⟩|⟨rfl,rfl⟩ <;> simp

theorem criticalResiduals_word_length_le (β : ℂ) (c : Fin d → ℂ) (σ : Fin d → Sign) (i j : Fin d) :
    ∀t∈criticalResiduals β c σ i j,t.word.length≤1 := by
  intro t ht
  simp only [criticalResiduals,List.mem_append] at ht
  rcases ht with (ht|ht)|ht
  · obtain ⟨⟨e,v⟩,hv,rfl⟩ := List.mem_map.mp ht
    exact lowerTerms_word_length_le _ _ e v hv
  · obtain ⟨q,hq,rfl⟩ := List.mem_map.mp ht
    obtain ⟨⟨e,v⟩,hv,rfl⟩ := List.mem_map.mp hq
    exact lowerTerms_word_length_le _ _ e v hv
  · simp only [List.mem_cons,List.mem_nil_iff,or_false] at ht
    rcases ht with rfl|rfl <;> simp

/-- Every differentiated overlap resolution strictly lowers its original
left-operator degree `u.length+2`. -/
theorem expanded_criticalResiduals_order_drop (β : ℂ) (c : Fin d → ℂ) (σ : Fin d → Sign)
    (i j : Fin d) (u : List (Fin d)) :
    ∀t∈expandResiduals u (criticalResiduals β c σ i j),t.word.length<u.length+2 := by
  intro t ht
  have hh := expandResiduals_word_length_le u (criticalResiduals β c σ i j) 1
    (criticalResiduals_word_length_le β c σ i j) t ht
  omega

end SectorialData
end BourgadeHuang.CMS
