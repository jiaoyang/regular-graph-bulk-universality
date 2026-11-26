import GeneralizedBulk.Entropy.ProfileConcentration

/-! Cauchy--Schwarz tail-energy bounds for arbitrary probability laws. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators Classical

namespace GeneralizedBulk.Entropy

variable {Ω : Type*} [MeasurableSpace Ω]

theorem integral_abs_tail_le_sqrt (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f : Ω → ℝ) (hf : MemLp f 2 μ) (s : Set Ω) (hs : MeasurableSet s) :
    (∫ x,if x ∈ s then |f x| else 0 ∂μ) ≤
      Real.sqrt (∫ x,f x^2 ∂μ)*Real.sqrt (μ.real s) := by
  let g : Ω → ℝ := s.indicator (fun _ => 1)
  have hg : MemLp g 2 μ := (memLp_const (1 : ℝ)).indicator hs
  have hpq : (2 : ℝ).HolderConjugate 2 := Real.holderConjugate_iff.mpr ⟨by norm_num,by norm_num⟩
  have h := integral_mul_norm_le_Lp_mul_Lq hpq
    (show MemLp f (ENNReal.ofReal (2 : ℝ)) μ by simpa using hf)
    (show MemLp g (ENNReal.ofReal (2 : ℝ)) μ by simpa using hg)
  have hleft : (fun x => ‖f x‖*‖g x‖) = (fun x => if x ∈ s then |f x| else 0) := by
    funext x
    by_cases hx : x ∈ s <;> simp [g,hx,Real.norm_eq_abs]
  have hsq : (fun x => ‖g x‖^(2 : ℝ)) = s.indicator (fun _ => (1 : ℝ)) := by
    funext x
    by_cases hx : x ∈ s <;> simp [g,hx]
  have hint : integral μ (s.indicator (fun _ => (1 : ℝ))) = μ.real s := by
    simpa using (integral_indicator_const (μ := μ) (1 : ℝ) hs)
  rw [hleft,hsq,hint] at h
  simpa only [Real.norm_eq_abs,Real.rpow_two,sq_abs,← Real.sqrt_eq_rpow] using h

end GeneralizedBulk.Entropy
