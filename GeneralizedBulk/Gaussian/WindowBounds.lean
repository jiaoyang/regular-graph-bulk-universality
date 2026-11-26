import GeneralizedBulk.Gaussian.WindowTruncation

/-! Uniform integrable domination for actual Gaussian window errors. -/
noncomputable section
open MeasureTheory BourgadeHuang Filter
open scoped Topology BigOperators
namespace GeneralizedBulk.Gaussian
variable {I : Type*} [Countable I] {s : AnchoredCountingState}

theorem windowL2_norm_sq_le (parameters : Parameters) (p : ParticlePresentation s I) (R : ℝ)
    (v : ℂ × Bool) (i j : Fin 4) :
    ‖windowL2 parameters p R v i j‖ ^ 2 ≤
      2 * ∑' k : I, ‖(parameters.scale : ℂ) * particleCoefficient (p.location k) v‖ ^ 2 := by
  let a := fun k => (parameters.scale : ℂ) * particleCoefficient (p.location k) v
  let f := fun k => a k • markQuadraticLp parameters.p k i j
  have horth : Pairwise (fun k l => @inner ℂ _ _ (f k) (f l) = 0) := by
    intro k l hkl
    simp only [f,inner_smul_left,inner_smul_right,markQuadraticLp_inner_off parameters.p
      parameters.abs_p_lt_one hkl i j,mul_zero]
  have ha : Summable (fun k => ‖a k‖ ^ 2) := by
    simpa only [a,norm_mul,mul_pow] using
      (p.summable_coefficient_sq v).mul_left (‖(parameters.scale : ℂ)‖ ^ 2)
  change ‖∑ k ∈ presentationWindowFinset p R, f k‖ ^ 2 ≤ _
  rw [norm_sum_sq_of_pairwise_inner_zero f horth]
  calc
    _ ≤ ∑ k ∈ presentationWindowFinset p R, 2 * ‖a k‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro k hk
      dsimp [f]
      rw [norm_smul,mul_pow]
      nlinarith [markQuadraticLp_norm_sq_le_two parameters.p parameters.abs_p_lt_one k i j,
        sq_nonneg ‖a k‖]
    _ = 2 * ∑ k ∈ presentationWindowFinset p R, ‖a k‖ ^ 2 := (Finset.mul_sum _ _ _).symm
    _ ≤ 2 * ∑' k, ‖a k‖ ^ 2 := mul_le_mul_of_nonneg_left
      (sum_le_tsum (presentationWindowFinset p R) (fun k hk => sq_nonneg _) ha) (by norm_num)

theorem windowL2_error_norm_sq_le_anchor (parameters : Parameters) (p : ParticlePresentation s I) (R : ℝ)
    (v : ℂ × Bool) (i j : Fin 4) :
    ‖l2Series (iidLaw (markLaw parameters.p) I) (fun k => markQuadraticLp parameters.p k i j)
      (fun k => (parameters.scale : ℂ) * particleCoefficient (p.location k) v) -
        windowL2 parameters p R v i j‖ ^ 2 ≤
      (8 * (‖(parameters.scale : ℂ)‖ ^ 2 * coefficientSquareEnvelope v)) * ‖s.val.2‖ := by
  let L := l2Series (iidLaw (markLaw parameters.p) I) (fun k => markQuadraticLp parameters.p k i j)
    (fun k => (parameters.scale : ℂ) * particleCoefficient (p.location k) v)
  let W := windowL2 parameters p R v i j
  let S := ∑' k : I, ‖(parameters.scale : ℂ) * particleCoefficient (p.location k) v‖ ^ 2
  have hfull : ‖L‖ ^ 2 ≤ 2 * S := norm_weighted_tsum_sq_le
    (fun k => markQuadraticLp parameters.p k i j)
    (fun k => (parameters.scale : ℂ) * particleCoefficient (p.location k) v) 2
    (fun k l hkl => markQuadraticLp_inner_off _ parameters.abs_p_lt_one hkl i j)
    (by norm_num) (fun k => markQuadraticLp_norm_sq_le_two _ parameters.abs_p_lt_one k i j)
    (by simpa only [norm_mul,mul_pow] using
      (p.summable_coefficient_sq v).mul_left (‖(parameters.scale : ℂ)‖ ^ 2))
  have hwin : ‖W‖ ^ 2 ≤ 2 * S := windowL2_norm_sq_le parameters p R v i j
  have hsum := presented_coefficient_square_sum_le p (parameters.scale : ℂ) v
  have hnorm := norm_sub_le L W
  have hdiff : ‖L - W‖ ^ 2 ≤ 2 * ‖L‖ ^ 2 + 2 * ‖W‖ ^ 2 := by
    nlinarith [sq_nonneg (‖L‖ - ‖W‖),norm_nonneg (L-W),norm_nonneg L,norm_nonneg W]
  change ‖L-W‖ ^ 2 ≤ _
  nlinarith

/-- The conditional second-moment window error has an anchor-integrable
envelope independent of the cutoff. -/
theorem windowField_second_moment_error_le_anchor
    (parameters : Parameters) (p : ParticlePresentation s I) (R : ℝ)
    (v : ℂ × Bool) (i j : Fin 4) :
    (∫ γ, ‖presentedGaussianL2 parameters p v γ i j -
      windowField parameters p (-R) R v γ i j‖ ^ 2 ∂iidLaw (markLaw parameters.p) I) ≤
      (8 * (‖(parameters.scale : ℂ)‖ ^ 2 * coefficientSquareEnvelope v)) * ‖s.val.2‖ := by
  let μ := iidLaw (markLaw parameters.p) I
  let L := l2Series μ (fun k => markQuadraticLp parameters.p k i j)
    (fun k => (parameters.scale : ℂ) * particleCoefficient (p.location k) v)
  have heq : (∫ γ, ‖presentedGaussianL2 parameters p v γ i j -
      windowField parameters p (-R) R v γ i j‖ ^ 2 ∂μ) =
      ‖L - windowL2 parameters p R v i j‖ ^ 2 := by
    rw [← integral_norm_sq_L2 μ]
    apply integral_congr_ae
    filter_upwards [windowL2_coe_ae parameters p R v i j,
      Lp.coeFn_sub L (windowL2 parameters p R v i j)] with γ hw hs
    change ‖L γ - windowField parameters p (-R) R v γ i j‖ ^ 2 = _
    rw [hs]
    simp only [Pi.sub_apply,hw]
  rw [heq]
  exact windowL2_error_norm_sq_le_anchor parameters p R v i j

end GeneralizedBulk.Gaussian
