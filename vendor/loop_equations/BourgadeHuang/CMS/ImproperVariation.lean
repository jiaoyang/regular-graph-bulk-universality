import BourgadeHuang.CMS.TriangularEvolutionComposition

/-! Differentiation of the genuine improper variation-of-constants integral. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace BourgadeHuang.CMS
set_option linter.unusedSectionVars false
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

lemma integral_tail_eq_sub_interval {f : ℝ → E} {R t : ℝ} (hRt : R≤t)
    (hf : IntegrableOn f (Ioi R)) :
    (∫ s in Ioi t, f s) = (∫ s in Ioi R, f s)-(∫ s in R..t, f s) := by
  have hd : Disjoint (Ioc R t) (Ioi t) := Set.disjoint_left.mpr (fun x hx hy => not_lt_of_ge hx.2 hy)
  have h := setIntegral_union hd measurableSet_Ioi
    (hf.mono_set Ioc_subset_Ioi_self) (hf.mono_set (Ioi_subset_Ioi hRt))
  rw [Ioc_union_Ioi_eq_Ioi hRt,← intervalIntegral.integral_of_le hRt] at h
  rw [h]
  abel

lemma hasDerivAt_tailIntegral {f : ℝ → E} {R t : ℝ} (hRt : R<t)
    (hf : Continuous f) (hi : IntegrableOn f (Ioi R)) :
    HasDerivAt (fun t => ∫ s in Ioi t, f s) (-f t) t := by
  have hd := (hf.integral_hasStrictDerivAt R t).hasDerivAt.const_sub (∫ s in Ioi R, f s)
  apply hd.congr_of_eventuallyEq
  filter_upwards [lt_mem_nhds hRt] with x hx
  exact integral_tail_eq_sub_interval hx.le hi

lemma integral_shift_tail (f : ℝ → E) (t : ℝ) :
    (∫ u : ℝ in Ioi 0, f (t+u)) = ∫ s : ℝ in Ioi t, f s := by
  rw [← integral_indicator measurableSet_Ioi,← integral_indicator measurableSet_Ioi]
  have h := integral_add_left_eq_self (μ:=volume) ((Ioi t).indicator f) t
  convert h using 1
  congr 1
  apply funext
  intro u
  by_cases hu : 0<u
  · have ht : t<t+u := by linarith
    simp [Set.indicator_of_mem,hu,ht]
  · have ht : ¬t<t+u := by linarith
    simp [Set.indicator_of_not_mem,hu,ht]

/-- The factorized improper variation-of-constants integral. -/
def backwardTail (B : ℝ → ℝ → E →L[ℝ] E) (R : ℝ) (f : ℝ → E) (t : ℝ) : E :=
  -(B t R) (∫ s in Ioi t, B R s (f s))

lemma backwardTail_eq_integral (B : ℝ → ℝ → E →L[ℝ] E) (R : ℝ) (f : ℝ → E)
    (hcomp : ∀ t r s, (B t r).comp (B r s)=B t s)
    (hi : IntegrableOn (fun s=>B R s (f s)) (Ioi R)) {t : ℝ} (ht : R≤t) :
    backwardTail B R f t = -(∫ s in Ioi t, B t s (f s)) := by
  unfold backwardTail
  congr 1
  rw [← ContinuousLinearMap.integral_comp_comm _ (hi.mono_set (Ioi_subset_Ioi ht))]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro s hs
  exact congrArg (fun L : E→L[ℝ]E =>L (f s)) (hcomp t R s)

/-- Exact differentiation of the actual improper tail integral. The cocycle
reduces it to a fixed kernel and the ordinary fundamental theorem of calculus. -/
theorem hasDerivAt_backwardTail (B : ℝ → ℝ → E →L[ℝ] E)
    (A : ℝ → E →L[ℝ] E) (R : ℝ) (f : ℝ → E)
    (hcomp : ∀ t r s, (B t r).comp (B r s)=B t s)
    (hself : ∀ t, B t t=ContinuousLinearMap.id ℝ E)
    (hderiv : ∀ t s, HasDerivAt (fun t=>B t s) ((A t).comp (B t s)) t)
    (hc : Continuous (fun s=>B R s (f s)))
    (hi : IntegrableOn (fun s=>B R s (f s)) (Ioi R)) {t : ℝ} (ht : R<t) :
    HasDerivAt (backwardTail B R f) (A t (backwardTail B R f t)+f t) t := by
  have hd := ((hderiv t R).clm_apply (hasDerivAt_tailIntegral ht hc hi)).neg
  have heq : B t R (B R t (f t))=f t := by
    change ((B t R).comp (B R t)) (f t)=f t
    rw [hcomp,hself,ContinuousLinearMap.id_apply]
  convert hd using 1
  simp only [backwardTail,ContinuousLinearMap.comp_apply,map_neg,neg_add_rev,neg_neg,heq]
  abel

end BourgadeHuang.CMS
