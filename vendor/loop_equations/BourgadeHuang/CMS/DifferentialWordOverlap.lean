import BourgadeHuang.CMS.DifferentialPrincipalSymbol

/-! Repeated-coordinate word overlaps and their explicit lower-order
residual replacements. -/
noncomputable section
open scoped BigOperators Topology
open Set Filter
namespace BourgadeHuang.CMS
open GapExpression

/-- Distinct repeated symbols in one commutative word leave a common prefix. -/
theorem repeated_word_overlap {α : Type*} [DecidableEq α] (u v : List α) (i j : α)
    (hij : i≠j) (h : (u++[i,i]).Perm (v++[j,j])) :
    ∃w,u.Perm (w++[j,j]) ∧ v.Perm (w++[i,i]) := by
  have hc := h.count_eq j
  simp [List.count_append,List.count_cons,hij,Ne.symm hij] at hc
  have huj : j∈u := List.count_pos_iff.mp (by omega)
  have huj' : j∈u.erase j := List.count_pos_iff.mp (by rw [List.count_erase_self];omega)
  let w := (u.erase j).erase j
  have hp : u.Perm ([j,j]++w) :=
    (List.perm_cons_erase huj).trans ((List.perm_cons_erase huj').cons j)
  have hu : u.Perm (w++[j,j]) := hp.trans List.perm_append_comm
  refine ⟨w,hu,?_⟩
  have h₁ := (hu.symm.append_right [i,i]).trans h
  have h₂ : ((w++[j,j])++[i,i]).Perm ((w++[i,i])++[j,j]) := by
    simp only [List.append_assoc]
    exact List.Perm.append_left w List.perm_append_comm
  exact ((List.perm_append_right_iff [j,j]).mp (h₂.symm.trans h₁)).symm

theorem wordDerivative_sub {d : ℕ} (u : List (Fin d)) {U : Set (Point d)}
    (hU : IsOpen U) {f g : Point d → ℂ} (hf : AnalyticOnNhd ℂ f U) (hg : AnalyticOnNhd ℂ g U) :
    EqOn (wordDerivative u (f-g)) (wordDerivative u f-wordDerivative u g) U := by
  have he : f-g=f+(fun w=>(-1:ℂ)*g w) := by funext w; simp [sub_eq_add_neg]
  intro z hz
  rw [he,wordDerivative_add u hU hf (analyticOnNhd_const.mul hg) hz]
  change wordDerivative u f z+wordDerivative u (fun w=>(-1:ℂ)*g w) z=_
  rw [wordDerivative_const_mul u (-1) hU hg hz]
  simp [sub_eq_add_neg]

namespace SectorialData
variable {d : ℕ}

/-- Every critical-pair relation holds after an arbitrary outer derivative
word, written without derivatives of the constant coefficients ±1. -/
theorem critical_word_identity (β : ℂ) (c : Fin d → ℂ) (σ : Fin d → Sign)
    (i j : Fin d) (hij : i≠j) (hβ : β≠0) (hc : ∀k,c k= -1 ∨ c k=β/2)
    (u : List (Fin d)) {f : Point d → ℂ} (hf : AnalyticOnNhd ℂ f (OrderedDomain d))
    {z : Point d} (hz : z∈OrderedDomain d) :
    wordDerivative (u++[j,j]) ((general β c σ).operator i f) z-
      wordDerivative (u++[i,i]) ((general β c σ).operator j f) z=
      (general β c σ).residualSum (expandResiduals u (criticalResiduals β c σ i j)) f z := by
  let D := general β c σ
  have hop (a : Fin d) : AnalyticOnNhd ℂ (D.operator a f) (OrderedDomain d) :=
    fun w hw=>D.analyticAt_operator (hf w hw) (orderedDomain_collisionFree hw) a
  have he : EqOn (secondPartial j (D.operator i f)-secondPartial i (D.operator j f))
      (D.residualSum (criticalResiduals β c σ i j) f) (OrderedDomain d) := by
    intro w hw
    have hh := residualSum_criticalPair β c σ i j (hf w hw) hw hij hβ hc
    simpa only [residualSum,GapExpression.eval,wordDerivative,one_mul,neg_one_mul,add_zero,sub_eq_add_neg,secondPartial]
      using hh
  have hh := wordDerivative_congr u (orderedDomain_isOpen d) he hz
  rw [wordDerivative_sub u (orderedDomain_isOpen d)
      (f:=secondPartial j (D.operator i f)) (g:=secondPartial i (D.operator j f))
      (fun w hw=>analyticAt_coordDeriv (analyticAt_coordDeriv (hop i w hw) j) j)
      (fun w hw=>analyticAt_coordDeriv (analyticAt_coordDeriv (hop j w hw) i) i) hz,
    D.wordDerivative_residualSum u (criticalResiduals β c σ i j) hf hz] at hh
  simpa only [wordDerivative_append,wordDerivative,secondPartial,Pi.sub_apply] using hh

/-- Two residual terms with the same principal monomial admit a replacement
whose left derivative words are strictly shorter. -/
theorem residual_pair_order_drop (β : ℂ) (c : Fin d → ℂ) (σ : Fin d → Sign)
    (hβ : β≠0) (hc : ∀k,c k= -1 ∨ c k=β/2)
    (a : GapExpression d) (u v : List (Fin d)) (i j : Fin d)
    (hkey : (u++[i,i]).Perm (v++[j,j])) :
    ∃rs : List (DifferentialResidualTerm d),(∀t∈rs,t.word.length<u.length) ∧
      (general β c σ).ResidualEquivalent
        [⟨a,u,i⟩,⟨.mul (.const (-1)) a,v,j⟩] rs := by
  by_cases hij : i=j
  · subst j
    have huv := (List.perm_append_right_iff [i,i]).mp hkey
    refine ⟨[],by simp,?_⟩
    intro f hf z hz
    have he := wordDerivative_perm huv (orderedDomain_isOpen d)
      (fun w hw=>(general β c σ).analyticAt_operator (hf w hw) (orderedDomain_collisionFree hw) i) hz
    simp only [residualSum,GapExpression.eval,he]
    ring
  · obtain ⟨w,huw,hvw⟩ := repeated_word_overlap u v i j hij hkey
    refine ⟨scaleResiduals a (expandResiduals w (criticalResiduals β c σ i j)),?_,?_⟩
    · intro t ht
      obtain ⟨s,hs,rfl⟩ := List.mem_map.mp ht
      have hl := expanded_criticalResiduals_order_drop β c σ i j w s hs
      have he := huw.length_eq
      simp only [List.length_append,List.length_cons,List.length_nil] at he
      simpa only [←he] using hl
    · intro f hf z hz
      have hop (r : Fin d) : AnalyticOnNhd ℂ ((general β c σ).operator r f) (OrderedDomain d) :=
        fun w hw=>(general β c σ).analyticAt_operator (hf w hw) (orderedDomain_collisionFree hw) r
      rw [residualSum_scaleResiduals]
      simp only [residualSum,GapExpression.eval,add_zero]
      rw [wordDerivative_perm huw (orderedDomain_isOpen d) (hop i) hz,
        wordDerivative_perm hvw (orderedDomain_isOpen d) (hop j) hz,
        ←critical_word_identity β c σ i j hij hβ hc w hf hz]
      ring

end SectorialData
end BourgadeHuang.CMS
