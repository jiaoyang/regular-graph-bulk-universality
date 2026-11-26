import BourgadeHuang.CharacteristicRatioJointExpectation
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

/-! Actual differentiation under the anchored expectation. The common measurable
power series supplies integrability of every derivative and identifies every
Taylor coefficient after integration. -/
noncomputable section
open scoped Topology BigOperators NNReal ENNReal
open MeasureTheory Filter
namespace BourgadeHuang

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]

theorem HasAnchoredPowerSeries.comp_sub {f : AnchoredCountingState → E → ℂ} {x : E}
    (hf : HasAnchoredPowerSeries f x) (b : E) :
    HasAnchoredPowerSeries (fun s z => f s (z-b)) (x+b) := by
  obtain ⟨r,hr,p,L,hL,hm,hp,hb⟩ := hf
  exact ⟨r,hr,p,L,hL,hm,fun s => (hp s).comp_sub b,hb⟩

/-- An affine contractive parameter map preserves the measurable common series. -/
theorem HasAnchoredPowerSeries.comp_affine
    {f : AnchoredCountingState → F → ℂ} (L : E →L[ℂ] F) (hL : ‖L‖ ≤ 1)
    (b : F) (x : E) (hf : HasAnchoredPowerSeries f (L x+b)) :
    HasAnchoredPowerSeries (fun s z => f s (L z+b)) x := by
  have ht := hf.comp_sub (-b)
  simp only [add_neg_cancel_right, sub_neg_eq_add] at ht
  exact ht.pullback L hL x

theorem HasAnchoredPowerSeries.integral_iteratedDeriv
    {f : AnchoredCountingState → ℂ → ℂ} {x : ℂ}
    (hf : HasAnchoredPowerSeries f x) (ν : Measure AnchoredCountingState)
    {a : ℝ} (ha : 0 < a)
    (he : Integrable (fun s : AnchoredCountingState => Real.exp (a*‖s.val.2‖^2)) ν)
    (n : ℕ) :
    Integrable (fun s => iteratedDeriv n (f s) x) ν ∧
    iteratedDeriv n (fun z => ∫ s, f s z ∂ν) x = ∫ s, iteratedDeriv n (f s) x ∂ν := by
  obtain ⟨r,hr,p,L,_,hpm,hp,hpb⟩ := hf
  have hi : Integrable (fun s : AnchoredCountingState => Real.exp (L*‖s.val.2‖)) ν := by
    simpa using integrable_anchor_polynomial_exp ν ha he (by norm_num : (0:ℝ)≤1) 0 L
  have hic (m : ℕ) : Integrable (fun s => p s m) ν :=
    (hi.div_const _).mono' (hpm m).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun s => hpb s m))
  have heq (s : AnchoredCountingState) :
      iteratedDeriv n (f s) x = (n.factorial:ℂ)*p s n (fun _ => 1) := by
    rw [iteratedDeriv_eq_iteratedFDeriv, ← (hp s).factorial_smul (1:ℂ) n, nsmul_eq_mul]
  have hint := hasFPowerSeriesOnBall_integral f p x r hr hp hic
    (fun s => Real.exp (L*‖s.val.2‖)) hi (fun _ => Real.exp_nonneg _) hpb
  constructor
  · simp_rw [heq]
    exact ((ContinuousMultilinearMap.apply ℂ (fun _ : Fin n => ℂ) ℂ
      (fun _ => 1)).integrable_comp (hic n)).const_mul _
  · rw [iteratedDeriv_eq_iteratedFDeriv, ← hint.factorial_smul (1:ℂ) n, nsmul_eq_mul]
    simp only [integralFormalMultilinearSeries]
    rw [ContinuousMultilinearMap.integral_apply (hic n), ← integral_const_mul]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun s => (heq s).symm)

theorem HasAnchoredPowerSeries.integral_deriv
    {f : AnchoredCountingState → ℂ → ℂ} {x : ℂ}
    (hf : HasAnchoredPowerSeries f x) (ν : Measure AnchoredCountingState)
    {a : ℝ} (ha : 0 < a)
    (he : Integrable (fun s : AnchoredCountingState => Real.exp (a*‖s.val.2‖^2)) ν) :
    Integrable (fun s => deriv (f s) x) ν ∧
    HasDerivAt (fun z => ∫ s, f s z ∂ν) (∫ s, deriv (f s) x ∂ν) x := by
  have hd := hf.integral_iteratedDeriv ν ha he 1
  simp only [iteratedDeriv_succ,iteratedDeriv_zero] at hd
  exact ⟨hd.1, hd.2 ▸ (hf.analyticAt_integral ν ha he).differentiableAt.hasDerivAt⟩

end BourgadeHuang
