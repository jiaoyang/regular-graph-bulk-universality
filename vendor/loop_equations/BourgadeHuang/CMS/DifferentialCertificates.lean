import BourgadeHuang.CMS.SectorialReduction

/-! Explicit left differential-ideal certificates for the sectorial PDE.
A certificate is an identity on every analytic test function, with a finite
sum of differentiated PDE rows as its residual. It does not test only
already-existing solutions. -/
noncomputable section
open scoped BigOperators Topology
open Set Filter
namespace BourgadeHuang.CMS
open GapExpression

/-- One explicit left multiple of an actual differential-equation row. -/
structure DifferentialResidualTerm (d : ℕ) where
  coefficient : GapExpression d
  word : List (Fin d)
  source : Fin d

namespace SectorialData
variable {d : ℕ} (D : SectorialData d)

theorem analyticAt_operator {f : Point d → ℂ} {z : Point d}
    (hf : AnalyticAt ℂ f z) (hz : CollisionFree z) (i : Fin d) :
    AnalyticAt ℂ (D.operator i f) z := by
  unfold operator
  apply AnalyticAt.add
  · apply AnalyticAt.add
    · exact (analyticAt_coordDeriv (analyticAt_coordDeriv hf i) i).add
        (analyticAt_const.mul (analyticAt_coordDeriv hf i))
    · exact Finset.analyticAt_sum _ (fun j _=>
        (GapExpression.analyticAt_eval _ hz).mul (analyticAt_coordDeriv hf j))
  · exact (GapExpression.analyticAt_eval _ hz).mul hf

/-- The finite explicit residual, evaluated on an arbitrary analytic test. -/
def residualSum : List (DifferentialResidualTerm d) → (Point d → ℂ) → Point d → ℂ
  | [],_,_=>0
  | t::ts,f,z=>t.coefficient.eval z*wordDerivative t.word (D.operator t.source f) z+
      residualSum ts f z

@[simp] theorem residualSum_nil (f : Point d → ℂ) (z : Point d) :
    D.residualSum [] f z=0 := rfl

@[simp] theorem residualSum_cons (t : DifferentialResidualTerm d)
    (ts : List (DifferentialResidualTerm d)) (f : Point d → ℂ) (z : Point d) :
    D.residualSum (t::ts) f z=t.coefficient.eval z*wordDerivative t.word (D.operator t.source f) z+
      D.residualSum ts f z := rfl

theorem residualSum_append (ts us : List (DifferentialResidualTerm d))
    (f : Point d → ℂ) (z : Point d) :
    D.residualSum (ts++us) f z=D.residualSum ts f z+D.residualSum us f z := by
  induction ts with
  | nil=>simp [residualSum]
  | cons t ts ih=>simp only [List.cons_append,residualSum,ih,add_assoc]

def scaleResiduals (a : GapExpression d) (ts : List (DifferentialResidualTerm d)) :
    List (DifferentialResidualTerm d) := ts.map (fun t=>{t with coefficient:=.mul a t.coefficient})

theorem residualSum_scaleResiduals (a : GapExpression d) (ts : List (DifferentialResidualTerm d))
    (f : Point d → ℂ) (z : Point d) :
    D.residualSum (scaleResiduals a ts) f z=a.eval z*D.residualSum ts f z := by
  induction ts with
  | nil=>simp [scaleResiduals,residualSum]
  | cons t ts ih=>
    simp only [scaleResiduals,List.map_cons,residualSum,GapExpression.eval] at ih ⊢
    rw [ih]
    ring

def stepResiduals (i : Fin d) : List (DifferentialResidualTerm d) → List (DifferentialResidualTerm d)
  | []=>[]
  | t::ts=>{t with coefficient:=t.coefficient.derivative i}::{t with word:=i::t.word}::stepResiduals i ts

theorem analyticAt_residualSum (ts : List (DifferentialResidualTerm d))
    {f : Point d → ℂ} {z : Point d} (hf : AnalyticAt ℂ f z) (hz : CollisionFree z) :
    AnalyticAt ℂ (D.residualSum ts f) z := by
  induction ts with
  | nil=>exact analyticAt_const
  | cons t ts ih=>exact ((GapExpression.analyticAt_eval _ hz).mul
      (analyticAt_wordDerivative _ (D.analyticAt_operator hf hz _))).add ih

theorem coordDeriv_residualSum (ts : List (DifferentialResidualTerm d))
    {f : Point d → ℂ} {z : Point d} (hf : AnalyticAt ℂ f z) (hz : CollisionFree z) (i : Fin d) :
    coordDeriv i (D.residualSum ts f) z=D.residualSum (stepResiduals i ts) f z := by
  induction ts with
  | nil=>simp [residualSum,stepResiduals,coordDeriv]
  | cons t ts ih=>
    change coordDeriv i ((fun w=>t.coefficient.eval w*wordDerivative t.word (D.operator t.source f) w)+
      D.residualSum ts f) z=_
    rw [coordDeriv_add_analytic
      (f:=fun w=>t.coefficient.eval w*wordDerivative t.word (D.operator t.source f) w)
      (g:=D.residualSum ts f)
      ((GapExpression.analyticAt_eval _ hz).mul (analyticAt_wordDerivative _ (D.analyticAt_operator hf hz _)))
      (D.analyticAt_residualSum ts hf hz),coordDeriv_mul_analytic (GapExpression.analyticAt_eval _ hz)
      (analyticAt_wordDerivative _ (D.analyticAt_operator hf hz _)),GapExpression.coordDeriv_eval _ hz,ih]
    simp only [stepResiduals,residualSum,wordDerivative]
    ring

/-- Differentiate the stored residual without discarding its PDE source. -/
def expandResiduals : List (Fin d) → List (DifferentialResidualTerm d) → List (DifferentialResidualTerm d)
  | [],rs=>rs
  | i::u,rs=>stepResiduals i (expandResiduals u rs)

theorem wordDerivative_residualSum (u : List (Fin d)) (rs : List (DifferentialResidualTerm d))
    {f : Point d → ℂ} (hf : AnalyticOnNhd ℂ f (OrderedDomain d)) :
    EqOn (wordDerivative u (D.residualSum rs f))
      (D.residualSum (expandResiduals u rs) f) (OrderedDomain d) := by
  induction u with
  | nil=>intro z hz; rfl
  | cons i u ih=>
    intro z hz
    change coordDeriv i (wordDerivative u (D.residualSum rs f)) z=_
    rw [coordDeriv_congr_nhds (Filter.eventuallyEq_of_mem ((orderedDomain_isOpen d).mem_nhds hz) ih)]
    exact D.coordDeriv_residualSum _ (hf z hz) (orderedDomain_collisionFree hz) i

/-- An explicit certificate of equality modulo the actual left differential
ideal. Every residual is stored; equality is checked on all analytic tests. -/
def OperatorCongruent (ts us : List (LeibnizTerm d)) : Prop :=
  ∃rs : List (DifferentialResidualTerm d),∀f,AnalyticOnNhd ℂ f (OrderedDomain d)→
    ∀z∈OrderedDomain d,termSum ts f z=termSum us f z+D.residualSum rs f z

namespace OperatorCongruent
variable {D : SectorialData d} {ts us vs ws : List (LeibnizTerm d)}

protected theorem refl (ts : List (LeibnizTerm d)) : D.OperatorCongruent ts ts :=
  ⟨[],fun _ _ _ _=>by simp⟩

/-- A genuine analytic operator identity has the empty residual certificate. -/
theorem of_identity (h : ∀f,AnalyticOnNhd ℂ f (OrderedDomain d)→
    EqOn (termSum ts f) (termSum us f) (OrderedDomain d)) : D.OperatorCongruent ts us :=
  ⟨[],fun f hf z hz=>by simpa using h f hf hz⟩

protected theorem symm (h : D.OperatorCongruent ts us) : D.OperatorCongruent us ts := by
  obtain ⟨rs,hr⟩ := h
  refine ⟨scaleResiduals (.const (-1)) rs,?_⟩
  intro f hf z hz
  rw [D.residualSum_scaleResiduals]
  have hh := hr f hf z hz
  simp only [GapExpression.eval]
  linear_combination -hh

protected theorem trans (h : D.OperatorCongruent ts us) (h' : D.OperatorCongruent us vs) :
    D.OperatorCongruent ts vs := by
  obtain ⟨rs,hr⟩ := h
  obtain ⟨qs,hq⟩ := h'
  refine ⟨qs++rs,?_⟩
  intro f hf z hz
  rw [hr f hf z hz,hq f hf z hz,D.residualSum_append]
  ring

theorem append (h : D.OperatorCongruent ts us) (h' : D.OperatorCongruent vs ws) :
    D.OperatorCongruent (ts++vs) (us++ws) := by
  obtain ⟨rs,hr⟩ := h
  obtain ⟨qs,hq⟩ := h'
  refine ⟨rs++qs,?_⟩
  intro f hf z hz
  rw [termSum_append,termSum_append,hr f hf z hz,hq f hf z hz,D.residualSum_append]
  ring

theorem scale (h : D.OperatorCongruent ts us) (a : GapExpression d) :
    D.OperatorCongruent (scaleTerms a ts) (scaleTerms a us) := by
  obtain ⟨rs,hr⟩ := h
  refine ⟨scaleResiduals a rs,?_⟩
  intro f hf z hz
  rw [termSum_scaleTerms,termSum_scaleTerms,hr f hf z hz,D.residualSum_scaleResiduals,mul_add]

theorem step (h : D.OperatorCongruent ts us) (i : Fin d) :
    D.OperatorCongruent (stepTerms i ts) (stepTerms i us) := by
  obtain ⟨rs,hr⟩ := h
  refine ⟨stepResiduals i rs,?_⟩
  intro f hf z hz
  have he : termSum ts f =ᶠ[𝓝 z] fun w=>termSum us f w+D.residualSum rs f w :=
    Filter.eventuallyEq_of_mem ((orderedDomain_isOpen d).mem_nhds hz) (hr f hf)
  have hc := coordDeriv_congr_nhds he i
  rw [coordDeriv_termSum _ (hf z hz) (orderedDomain_collisionFree hz)] at hc
  change termSum (stepTerms i ts) f z=coordDeriv i (termSum us f+D.residualSum rs f) z at hc
  rw [coordDeriv_add_analytic (f:=termSum us f) (g:=D.residualSum rs f)
      (analyticAt_termSum _ (hf z hz) (orderedDomain_collisionFree hz))
      (D.analyticAt_residualSum rs (hf z hz) (orderedDomain_collisionFree hz)),
    coordDeriv_termSum _ (hf z hz) (orderedDomain_collisionFree hz),
    D.coordDeriv_residualSum rs (hf z hz) (orderedDomain_collisionFree hz)] at hc
  exact hc

theorem expand (h : D.OperatorCongruent ts us) (u : List (Fin d)) :
    D.OperatorCongruent (expandTerms u ts) (expandTerms u us) := by
  obtain ⟨rs,hr⟩ := h
  refine ⟨expandResiduals u rs,?_⟩
  intro f hf z hz
  have he : EqOn (termSum ts f) (termSum us f+D.residualSum rs f) (OrderedDomain d) := hr f hf
  have hc := wordDerivative_congr u (orderedDomain_isOpen d) he hz
  rw [wordDerivative_termSum u ts (orderedDomain_isOpen d) (fun _ hw=>orderedDomain_collisionFree hw) hf hz,
    wordDerivative_add u (orderedDomain_isOpen d)
      (fun w hw=>analyticAt_termSum us (hf w hw) (orderedDomain_collisionFree hw))
      (fun w hw=>D.analyticAt_residualSum rs (hf w hw) (orderedDomain_collisionFree hw)) hz] at hc
  change termSum (expandTerms u ts) f z=wordDerivative u (termSum us f) z+
    wordDerivative u (D.residualSum rs f) z at hc
  rw [wordDerivative_termSum u us (orderedDomain_isOpen d) (fun _ hw=>orderedDomain_collisionFree hw) hf hz,
    D.wordDerivative_residualSum u rs hf hz] at hc
  exact hc

theorem word_perm {u v : List (Fin d)} (h : u.Perm v) (a : GapExpression d) :
    D.OperatorCongruent [(a,u)] [(a,v)] := by
  apply of_identity
  intro f hf z hz
  simp only [termSum,add_zero,wordDerivative_perm h (orderedDomain_isOpen d) hf hz]

/-- The explicit primitive equation has exactly one undifferentiated PDE row
as its residual. -/
theorem equation (D : SectorialData d) (i : Fin d) :
    D.OperatorCongruent [(.const 1,[i,i])]
      ((.const (-(D.phase i)),[i])::scaleTerms (.const (-1)) (D.remainderTerms i)) := by
  refine ⟨[⟨.const 1,[],i⟩],?_⟩
  intro f _ z _
  simp only [termSum,termSum_scaleTerms,residualSum,wordDerivative,GapExpression.eval,one_mul,
    add_zero,D.termSum_remainderTerms,operator,secondPartial]
  ring

/-- Finite componentwise replacements retain a concatenated ideal certificate. -/
theorem finTerms {n : ℕ} (t u : Fin n → List (LeibnizTerm d))
    (h : ∀i,D.OperatorCongruent (t i) (u i)) :
    D.OperatorCongruent (GapExpression.finTerms n t) (GapExpression.finTerms n u) := by
  induction n with
  | zero=>exact OperatorCongruent.refl _
  | succ n ih=>exact (h 0).append (ih _ _ (fun i=>h i.succ))

/-- A stored residual vanishes on a true PDE solution. -/
theorem eqOn_solution (h : D.OperatorCongruent ts us) {f : Point d → ℂ} (hf : D.IsSolution f) :
    EqOn (termSum ts f) (termSum us f) (OrderedDomain d) := by
  obtain ⟨rs,hr⟩ := h
  have hzero (u : List (Fin d)) : wordDerivative u (fun _ : Point d=> (0:ℂ))=fun _=>0 := by
    induction u with
    | nil=>rfl
    | cons i u ih=>funext z; simp [wordDerivative,ih,coordDeriv]
  have hop (i : Fin d) : EqOn (D.operator i f) (fun _=>0) (OrderedDomain d) := fun z hz=>hf.2 z hz i
  have hs (z : Point d) (hz : z∈OrderedDomain d) : D.residualSum rs f z=0 := by
    clear hr
    induction rs with
    | nil=>rfl
    | cons t rs ih=>
      rw [residualSum_cons,wordDerivative_congr t.word (orderedDomain_isOpen d) (hop t.source) hz,hzero,ih]
      ring
  intro z hz
  simpa only [hs z hz,add_zero] using hr f hf.1 z hz

end OperatorCongruent

end SectorialData
end BourgadeHuang.CMS
