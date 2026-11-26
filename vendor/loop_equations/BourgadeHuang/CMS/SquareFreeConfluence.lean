import BourgadeHuang.CMS.DifferentialElimination

/-! Confluence of the physical-charge PDE reduction: a square-free expression
in the left differential ideal is zero as a genuine differential operator. -/
noncomputable section
open scoped BigOperators Topology
open Set Filter
namespace BourgadeHuang.CMS
open GapExpression
namespace SectorialData
variable {d : ℕ}

/-- Highest-symbol cancellation and the critical-pair reductions eliminate
all residual rows, by induction on their order and then their finite number. -/
theorem squareFree_residual_zero (β : ℂ) (c : Fin d → ℂ) (σ : Fin d → Sign)
    (hβ : β≠0) (hc : ∀i,c i= -1 ∨ c i=β/2)
    (ts us : List (LeibnizTerm d))
    (hts : ∀e u,(e,u)∈ts→u.Nodup) (hus : ∀e u,(e,u)∈us→u.Nodup)
    (n : ℕ) (rs : List (DifferentialResidualTerm d))
    (horder : ∀t∈rs,t.word.length≤n)
    (hidentity : ∀f,AnalyticOnNhd ℂ f (OrderedDomain d)→∀z∈OrderedDomain d,
      termSum ts f z=termSum us f z+(general β c σ).residualSum rs f z) :
    ∀f,AnalyticOnNhd ℂ f (OrderedDomain d)→∀z∈OrderedDomain d,
      (general β c σ).residualSum rs f z=0 := by
  classical
  induction n using Nat.strong_induction_on generalizing rs with
  | h n ihn=>
    generalize hk : residualTopCount n rs=k
    induction k using Nat.strong_induction_on generalizing rs with
    | h k ihk=>
      by_cases hex : ∃p∈rs,p.word.length=n
      · obtain ⟨p,hp,hpn⟩ := hex
        let qs := reduceAtPivot β c σ hβ hc p rs
        have hqorder : ∀t∈qs,t.word.length≤n := reduceAtPivot_order β c σ hβ hc p rs n horder
        have hqcount : residualTopCount n qs<k := by
          rw [←hk]
          exact reduceAtPivot_topCount_lt β c σ hβ hc p rs n hp hpn horder
        have heq : ∀f,AnalyticOnNhd ℂ f (OrderedDomain d)→∀z∈OrderedDomain d,
            (general β c σ).residualSum rs f z=(general β c σ).residualSum qs f z := by
          intro f hf z hz
          have hcancel := (general β c σ).principal_residual_cancellation ts us rs hidentity hts hus n horder
            p.principalIndex (by rw [DifferentialResidualTerm.principalIndex_degree,hpn])
            p.principalIndex_repeated hz
          change (rs.map (fun t=>if t.principalIndex=p.principalIndex then t.coefficient.eval z else 0)).sum=0 at hcancel
          have he := reduceAtPivot_identity β c σ hβ hc p rs hf hz
          change _=(general β c σ).residualSum qs f z+_ at he
          rw [hcancel,zero_mul,add_zero] at he
          exact he
        have hqidentity : ∀f,AnalyticOnNhd ℂ f (OrderedDomain d)→∀z∈OrderedDomain d,
            termSum ts f z=termSum us f z+(general β c σ).residualSum qs f z := by
          intro f hf z hz
          rw [←heq f hf z hz]
          exact hidentity f hf z hz
        intro f hf z hz
        rw [heq f hf z hz]
        exact ihk (residualTopCount n qs) hqcount qs hqorder hqidentity rfl f hf z hz
      · have hne : ∀t∈rs,t.word.length≠n := by
          intro t ht he
          exact hex ⟨t,ht,he⟩
        by_cases hn : n=0
        · have hrs : rs=[] := by
            cases rs with
            | nil=>rfl
            | cons t rs=>
              have h₁ := horder t (List.mem_cons_self ..)
              have h₂ := hne t (List.mem_cons_self ..)
              omega
          subst rs
          intro f hf z hz
          rfl
        · have hsmall : ∀t∈rs,t.word.length≤n-1 := by
            intro t ht
            have h₁ := horder t ht
            have h₂ := hne t ht
            omega
          exact ihn (n-1) (by omega) rs hsmall hidentity

/-- The certified square-free normal form is unique as an operator on all
analytic functions, rather than merely on already-constructed PDE solutions. -/
theorem OperatorCongruent.squareFree_identity (β : ℂ) (c : Fin d → ℂ) (σ : Fin d → Sign)
    (hβ : β≠0) (hc : ∀i,c i= -1 ∨ c i=β/2)
    {ts us : List (LeibnizTerm d)}
    (h : (general β c σ).OperatorCongruent ts us)
    (hts : ∀e u,(e,u)∈ts→u.Nodup) (hus : ∀e u,(e,u)∈us→u.Nodup) :
    ∀f,AnalyticOnNhd ℂ f (OrderedDomain d)→EqOn (termSum ts f) (termSum us f) (OrderedDomain d) := by
  obtain ⟨rs,hidentity⟩ := h
  let n := (rs.map (fun t=>t.word.length)).sum
  have horder : ∀t∈rs,t.word.length≤n := by
    intro t ht
    change t.word.length≤(rs.map (fun t=>t.word.length)).sum
    clear hidentity n
    induction rs with
    | nil=>simp at ht
    | cons s rs ih=>
      simp only [List.map_cons,List.sum_cons]
      rcases List.mem_cons.mp ht with rfl|ht
      · omega
      · have hh := ih ht
        omega
  intro f hf z hz
  have hzro := squareFree_residual_zero β c σ hβ hc ts us hts hus n rs horder hidentity f hf z hz
  simpa only [hzro,add_zero] using hidentity f hf z hz

theorem OperatorCongruent.squareFree_symbol (β : ℂ) (c : Fin d → ℂ) (σ : Fin d → Sign)
    (hβ : β≠0) (hc : ∀i,c i= -1 ∨ c i=β/2)
    {ts us : List (LeibnizTerm d)}
    (h : (general β c σ).OperatorCongruent ts us)
    (hts : ∀e u,(e,u)∈ts→u.Nodup) (hus : ∀e u,(e,u)∈us→u.Nodup)
    {z : Point d} (hz : z∈OrderedDomain d) : operatorSymbol ts z=operatorSymbol us z :=
  operatorSymbol_eq_of_identity ts us hz (fun f hf _ hz=>h.squareFree_identity β c σ hβ hc hts hus f hf hz)

end SectorialData
end BourgadeHuang.CMS
