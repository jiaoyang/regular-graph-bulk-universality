import BourgadeHuang.CMS.DifferentialWordOverlap

/-! Finite elimination of the highest-order left-ideal residuals. -/
noncomputable section
open scoped BigOperators Topology
open Set Filter
namespace BourgadeHuang.CMS
open GapExpression
variable {d : ℕ}

namespace DifferentialResidualTerm

def principalIndex (t : DifferentialResidualTerm d) : Fin d →₀ ℕ :=
  wordIndex (t.word++[t.source,t.source])

theorem principalIndex_degree (t : DifferentialResidualTerm d) :
    t.principalIndex.sum (fun _ n=>n)=t.word.length+2 := by
  simp [principalIndex,wordIndex_degree]

theorem length_eq_of_principalIndex_eq {t p : DifferentialResidualTerm d}
    (h : t.principalIndex=p.principalIndex) : t.word.length=p.word.length := by
  have hh := congrArg (fun a : Fin d →₀ ℕ=>a.sum (fun _ n=>n)) h
  dsimp only at hh
  rw [principalIndex_degree,principalIndex_degree] at hh
  omega

theorem principalIndex_repeated (t : DifferentialResidualTerm d) :
    ∃i,2≤t.principalIndex i := by
  refine ⟨t.source,?_⟩
  simp [principalIndex,wordIndex_apply,List.count_append]

end DifferentialResidualTerm

namespace SectorialData
variable (β : ℂ) (c : Fin d → ℂ) (σ : Fin d → Sign)
variable (hβ : β≠0) (hc : ∀i,c i= -1 ∨ c i=β/2)

def pivotReplacement (p t : DifferentialResidualTerm d) : List (DifferentialResidualTerm d) :=
  if h : t.principalIndex=p.principalIndex then
    Classical.choose (residual_pair_order_drop β c σ hβ hc t.coefficient t.word p.word t.source p.source
      ((wordIndex_eq_iff_perm _ _).mp h))
  else [t]

theorem pivotReplacement_short (p t : DifferentialResidualTerm d)
    (h : t.principalIndex=p.principalIndex) :
    ∀s∈pivotReplacement β c σ hβ hc p t,s.word.length<t.word.length := by
  unfold pivotReplacement
  rw [dif_pos h]
  exact (Classical.choose_spec (residual_pair_order_drop β c σ hβ hc t.coefficient t.word p.word
    t.source p.source ((wordIndex_eq_iff_perm _ _).mp h))).1

theorem pivotReplacement_identity (p t : DifferentialResidualTerm d)
    {f : Point d → ℂ} (hf : AnalyticOnNhd ℂ f (OrderedDomain d))
    {z : Point d} (hz : z∈OrderedDomain d) :
    (general β c σ).residualSum [t] f z=
      (general β c σ).residualSum (pivotReplacement β c σ hβ hc p t) f z+
      (if t.principalIndex=p.principalIndex then t.coefficient.eval z else 0)*
        wordDerivative p.word ((general β c σ).operator p.source f) z := by
  classical
  by_cases h : t.principalIndex=p.principalIndex
  · have he := (Classical.choose_spec (residual_pair_order_drop β c σ hβ hc t.coefficient t.word p.word
      t.source p.source ((wordIndex_eq_iff_perm _ _).mp h))).2 f hf hz
    simp only [pivotReplacement,dif_pos h,if_pos h]
    simp only [residualSum,GapExpression.eval,add_zero] at he ⊢
    linear_combination he
  · simp [pivotReplacement,h]

def reduceAtPivot (p : DifferentialResidualTerm d) (rs : List (DifferentialResidualTerm d)) :=
  rs.flatMap (pivotReplacement β c σ hβ hc p)

theorem reduceAtPivot_identity (p : DifferentialResidualTerm d) (rs : List (DifferentialResidualTerm d))
    {f : Point d → ℂ} (hf : AnalyticOnNhd ℂ f (OrderedDomain d))
    {z : Point d} (hz : z∈OrderedDomain d) :
    (general β c σ).residualSum rs f z=
      (general β c σ).residualSum (reduceAtPivot β c σ hβ hc p rs) f z+
      (rs.map (fun t=>if t.principalIndex=p.principalIndex then t.coefficient.eval z else 0)).sum*
        wordDerivative p.word ((general β c σ).operator p.source f) z := by
  induction rs with
  | nil=>simp [reduceAtPivot,residualSum]
  | cons t rs ih=>
    have hh := pivotReplacement_identity β c σ hβ hc p t hf hz
    simp only [residualSum,add_zero] at hh
    simp only [reduceAtPivot,List.flatMap_cons,residualSum_append,List.map_cons,List.sum_cons,residualSum]
    rw [hh,ih]
    change _ = (general β c σ).residualSum (pivotReplacement β c σ hβ hc p t) f z +
      (general β c σ).residualSum (reduceAtPivot β c σ hβ hc p rs) f z + _
    ring

theorem reduceAtPivot_order (p : DifferentialResidualTerm d) (rs : List (DifferentialResidualTerm d))
    (n : ℕ) (horder : ∀t∈rs,t.word.length≤n) :
    ∀s∈reduceAtPivot β c σ hβ hc p rs,s.word.length≤n := by
  intro s hs
  obtain ⟨t,ht,hs⟩ := List.mem_flatMap.mp hs
  by_cases h : t.principalIndex=p.principalIndex
  · exact (pivotReplacement_short β c σ hβ hc p t h s hs).le.trans (horder t ht)
  · simp only [pivotReplacement,dif_neg h,List.mem_singleton] at hs
    exact hs ▸ horder t ht

/-- Number of terms at a specified left-derivative order. -/
def residualTopCount (n : ℕ) (rs : List (DifferentialResidualTerm d)) : ℕ :=
  (rs.filter (fun t=>t.word.length=n)).length

@[simp] theorem residualTopCount_nil (n : ℕ) : residualTopCount n ([] : List (DifferentialResidualTerm d))=0 := rfl
@[simp] theorem residualTopCount_cons (n : ℕ) (t : DifferentialResidualTerm d) (rs) :
    residualTopCount n (t::rs)=(if t.word.length=n then 1 else 0)+residualTopCount n rs := by
  classical
  by_cases h : t.word.length=n <;> simp [residualTopCount,h,Nat.add_comm]
@[simp] theorem residualTopCount_append (n : ℕ) (rs qs : List (DifferentialResidualTerm d)) :
    residualTopCount n (rs++qs)=residualTopCount n rs+residualTopCount n qs := by
  simp [residualTopCount]

theorem residualTopCount_eq_zero (n : ℕ) (rs : List (DifferentialResidualTerm d))
    (h : ∀t∈rs,t.word.length≠n) : residualTopCount n rs=0 := by
  induction rs with
  | nil=>rfl
  | cons t rs ih=>
    rw [residualTopCount_cons,if_neg (h t (List.mem_cons_self ..)),zero_add]
    exact ih (fun t ht=>h t (List.mem_cons_of_mem _ ht))

theorem pivotReplacement_topCount_le (p t : DifferentialResidualTerm d) (n : ℕ)
    (ht : t.word.length≤n) :
    residualTopCount n (pivotReplacement β c σ hβ hc p t)≤(if t.word.length=n then 1 else 0) := by
  classical
  by_cases h : t.principalIndex=p.principalIndex
  · rw [residualTopCount_eq_zero n _ (fun s hs=>by
      have hh := pivotReplacement_short β c σ hβ hc p t h s hs
      omega)]
    exact Nat.zero_le _
  · simp [pivotReplacement,h]

theorem reduceAtPivot_topCount_le (p : DifferentialResidualTerm d) (rs : List (DifferentialResidualTerm d))
    (n : ℕ) (horder : ∀t∈rs,t.word.length≤n) :
    residualTopCount n (reduceAtPivot β c σ hβ hc p rs)≤residualTopCount n rs := by
  induction rs with
  | nil=>simp [reduceAtPivot]
  | cons t rs ih=>
    simp only [reduceAtPivot,List.flatMap_cons,residualTopCount_append,residualTopCount_cons]
    exact Nat.add_le_add (pivotReplacement_topCount_le β c σ hβ hc p t n (horder t (List.mem_cons_self ..)))
      (ih (fun t ht=>horder t (List.mem_cons_of_mem _ ht)))

theorem reduceAtPivot_topCount_lt (p : DifferentialResidualTerm d) (rs : List (DifferentialResidualTerm d))
    (n : ℕ) (hp : p∈rs) (hpn : p.word.length=n) (horder : ∀t∈rs,t.word.length≤n) :
    residualTopCount n (reduceAtPivot β c σ hβ hc p rs)<residualTopCount n rs := by
  induction rs with
  | nil=>simp at hp
  | cons t rs ih=>
    have htail : ∀t∈rs,t.word.length≤n := fun t ht=>horder t (List.mem_cons_of_mem _ ht)
    simp only [reduceAtPivot,List.flatMap_cons,residualTopCount_append,residualTopCount_cons]
    rcases List.mem_cons.mp hp with rfl|hp
    · have he : residualTopCount n (pivotReplacement β c σ hβ hc p p)=0 :=
        residualTopCount_eq_zero n _ (fun s hs=>by
          have hh := pivotReplacement_short β c σ hβ hc p p rfl s hs
          omega)
      rw [he,if_pos hpn,zero_add]
      have hh := reduceAtPivot_topCount_le β c σ hβ hc p rs n htail
      change residualTopCount n (reduceAtPivot β c σ hβ hc p rs)<_
      omega
    · have hh := pivotReplacement_topCount_le β c σ hβ hc p t n (horder t (List.mem_cons_self ..))
      have hi := ih hp htail
      change residualTopCount n (pivotReplacement β c σ hβ hc p t)+
        residualTopCount n (reduceAtPivot β c σ hβ hc p rs)<_
      omega

end SectorialData
end BourgadeHuang.CMS
