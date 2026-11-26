import GeneralizedBulk.Gaussian.CoordinateLaw

/-! Actual second moments of scalar Gaussian marginals, obtained from the
proved Gaussian MGF, including degenerate Gaussian laws. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

namespace GeneralizedBulk.Entropy

variable {Ω : Type*} [MeasurableSpace Ω]

theorem gaussianLaw_zero_interior (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ) (m : ℝ) (v : ℝ≥0)
    (hX : Measure.map X μ = gaussianReal m v) :
    (0 : ℝ) ∈ interior (integrableExpSet X μ) := by
  have he : integrableExpSet X μ = Set.univ := by
    ext t
    simp only [integrableExpSet,Set.mem_setOf_eq,Set.mem_univ,iff_true]
    exact mgf_pos_iff.mp (by rw [mgf_gaussianReal hX t]; exact Real.exp_pos _)
  rw [he,interior_univ]
  trivial

theorem gaussianLaw_integrable_pow (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ) (m : ℝ) (v : ℝ≥0)
    (hX : Measure.map X μ = gaussianReal m v) (n : ℕ) :
    Integrable (fun x => X x^n) μ :=
  integrable_pow_of_mem_interior_integrableExpSet (gaussianLaw_zero_interior μ X m v hX) n

theorem gaussianLaw_memLp_two (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ) (hXm : Measurable X)
    (m : ℝ) (v : ℝ≥0) (hX : Measure.map X μ = gaussianReal m v) : MemLp X 2 μ :=
  (memLp_two_iff_integrable_sq hXm.aestronglyMeasurable).mpr (gaussianLaw_integrable_pow μ X m v hX 2)

set_option maxHeartbeats 1000000 in
theorem gaussianLaw_second_moment (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ) (m : ℝ) (v : ℝ≥0)
    (hX : Measure.map X μ = gaussianReal m v) :
    (∫ x,X x^2 ∂μ) = m^2+(v : ℝ) := by
  let f : ℝ → ℝ := fun t => Real.exp (t*m+(v : ℝ)*t^2/2)
  let g : ℝ → ℝ := fun t => (m+(v : ℝ)*t)*f t
  have df (t : ℝ) : HasDerivAt f (g t) t := by
    convert (((hasDerivAt_id t).mul_const m).add ((((hasDerivAt_id t).pow 2).const_mul (v : ℝ)).div_const 2)).exp using 1 <;>
      dsimp [f,g] <;> ring
  have dg (t : ℝ) : HasDerivAt g (((v : ℝ)+(m+(v : ℝ)*t)^2)*f t) t := by
    convert ((hasDerivAt_const t m).add ((hasDerivAt_id t).const_mul (v : ℝ))).mul (df t) using 1 <;>
      dsimp [f,g] <;> ring
  have hiter : iteratedDeriv 2 f 0 = m^2+(v : ℝ) := by
    rw [show (2 : ℕ) = 1+1 from rfl,iteratedDeriv_succ,
      show iteratedDeriv 1 f = g from funext (fun t => by simpa using (df t).deriv)]
    simpa [f,add_comm] using (dg 0).deriv
  have h := iteratedDeriv_mgf_zero (gaussianLaw_zero_interior μ X m v hX) 2
  have hmf : mgf X μ = f := by
    funext t
    simpa only [f,mul_comm t m] using mgf_gaussianReal hX t
  rw [hmf,hiter] at h
  simpa only [Pi.pow_apply] using h.symm

end GeneralizedBulk.Entropy
