import GeneralizedBulk.Graph.PartialVariance
import GeneralizedBulk.Graph.MicroscopicExterior

/-!
# Complex microscopic remote tails

The finite Poisson estimate is extended from vertical spectral parameters to
arbitrary complex microscopic parameters. All coefficient and covariance
estimates below are deterministic finite spectral calculations.
-/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace GeneralizedBulk.External.RegularSpectralData
open Graph
variable {d : ℕ} {N : ℕ → ℕ} {Ω : Type*} [MeasurableSpace Ω]
variable (D : RegularSpectralData d N Ω) (n : ℕ) (ω : Ω)

private theorem shifted_remote_inverse_square_le (x E shift eta R : ℝ)
    (hR : 0 < R) (hshift : 2 * |shift| ≤ R) (hx : R ≤ |x - E|) :
    (((x - E - shift) ^ 2 + eta ^ 2)⁻¹) ≤
      (8 / R) * realPoissonKernel E R x := by
  have htri : |x - E| ≤ |x - E - shift| + |shift| := by
    convert abs_add (x - E - shift) shift using 1 <;> ring_nf
  have hhalf : |x - E| / 2 ≤ |x - E - shift| := by linarith
  have hsq : (x - E) ^ 2 ≤ 4 * (x - E - shift) ^ 2 := by
    have hh := (sq_le_sq₀ (by positivity : 0 ≤ |x - E| / 2)
      (abs_nonneg (x - E - shift))).mpr hhalf
    rw [div_pow, sq_abs, sq_abs] at hh
    norm_num at hh
    linarith
  have hRsq : R ^ 2 ≤ (x - E) ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ hR.le (abs_nonneg (x - E))).mpr hx
  have hden : 0 < (x - E - shift) ^ 2 + eta ^ 2 := by
    have hh : 0 < (x - E) ^ 2 := by nlinarith
    nlinarith [sq_nonneg eta]
  have hbase : 0 < (x - E) ^ 2 + R ^ 2 := by nlinarith [sq_nonneg (x - E)]
  calc
    _ ≤ 8 / ((x - E) ^ 2 + R ^ 2) := by
      rw [inv_eq_one_div, div_le_div_iff₀ hden hbase]
      nlinarith [sq_nonneg eta]
    _ = _ := by dsimp [realPoissonKernel]; field_simp

/-- The spectral real part may move by at most half the remote cutoff.
The scalar trace remains at the original center and cutoff height. -/
theorem complex_remote_resolvent_coefficient_square_sum_le
    (E shift eta R : ℝ) (hR : 0 < R) (hshift : 2 * |shift| ≤ R) :
    (∑ k ∈ D.remoteEigenvalues n ω E R,
      ‖(N n : ℂ)⁻¹ * ((D.eigenvalue n ω k : ℂ) -
        spectralParameter (E + shift) eta)⁻¹‖ ^ 2) ≤
      (8 / ((N n : ℝ) * R)) *
        (D.scalarResolvent n ω (spectralParameter E R)).im := by
  classical
  have hN : (N n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt (D.size_pos n))
  have htrace : (N n : ℝ) * (D.scalarResolvent n ω (spectralParameter E R)).im =
      ∑ k, realPoissonKernel E R (D.eigenvalue n ω k) := by
    rw [D.scalarResolvent_poisson n ω E R (ne_of_gt hR), ← mul_assoc,
      mul_inv_cancel₀ hN, one_mul]
  have hb : (∑ k ∈ D.remoteEigenvalues n ω E R,
      ‖(N n : ℂ)⁻¹ * ((D.eigenvalue n ω k : ℂ) -
        spectralParameter (E + shift) eta)⁻¹‖ ^ 2) ≤
      (N n : ℝ)⁻¹ ^ 2 * ((8 / R) *
        ∑ k, realPoissonKernel E R (D.eigenvalue n ω k)) := by
    calc
      _ = (N n : ℝ)⁻¹ ^ 2 * (∑ k ∈ D.remoteEigenvalues n ω E R,
          (((D.eigenvalue n ω k - E - shift) ^ 2 + eta ^ 2)⁻¹)) := by
        have hi (k : Fin (N n)) :
            ‖((D.eigenvalue n ω k : ℂ) - spectralParameter (E + shift) eta)⁻¹‖ ^ 2 =
              ((D.eigenvalue n ω k - E - shift) ^ 2 + eta ^ 2)⁻¹ := by
          rw [← Complex.normSq_eq_norm_sq, Complex.normSq_inv,
            normSq_real_sub_spectralParameter]
          congr 2
          ring
        simp_rw [norm_mul, mul_pow, hi]
        rw [norm_inv, Complex.norm_natCast, ← Finset.mul_sum]
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
        calc
          _ ≤ ∑ k ∈ D.remoteEigenvalues n ω E R,
              (8 / R) * realPoissonKernel E R (D.eigenvalue n ω k) := by
            apply Finset.sum_le_sum
            intro k hk
            exact shifted_remote_inverse_square_le _ E shift eta R hR hshift
              (Finset.mem_filter.mp hk).2
          _ ≤ ∑ k, (8 / R) * realPoissonKernel E R (D.eigenvalue n ω k) :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
              (fun k _ _ => mul_nonneg (by positivity)
                (div_nonneg hR.le (by positivity)))
          _ = _ := (Finset.mul_sum _ _ _).symm
  rw [← htrace] at hb
  convert hb using 1 <;> field_simp <;> ring

/-- The literal microscopic remote cutoff has the expected `sigma / R`
normalization. This holds in both spectral half planes. -/
theorem microscopic_remote_resolvent_coefficient_square_sum_le
    (E sigma : ℝ) (hsigma : 0 < sigma) (w : GraphNonreal)
    (R : ℝ) (hR : 0 < R) (hw : 2 * |w.1.re| ≤ R) :
    (∑ k ∈ D.remoteEigenvalues n ω E (microscopicStep (N n) sigma * R),
      ‖(N n : ℂ)⁻¹ * ((D.eigenvalue n ω k : ℂ) -
        (microscopicParameter (N n) (D.size_pos n) E sigma hsigma w).1)⁻¹‖ ^ 2) ≤
      (8 * sigma / R) * (D.scalarResolvent n ω
        (spectralParameter E (microscopicStep (N n) sigma * R))).im := by
  let c := microscopicStep (N n) sigma
  have hc : 0 < c := microscopicStep_pos (N n) (D.size_pos n) sigma hsigma
  have hz : (microscopicParameter (N n) (D.size_pos n) E sigma hsigma w).1 =
      spectralParameter (E + c * w.1.re) (c * w.1.im) := by
    apply Complex.ext <;> simp [microscopicParameter, spectralParameter, c]
  rw [hz]
  have h := D.complex_remote_resolvent_coefficient_square_sum_le n ω E
    (c * w.1.re) (c * w.1.im) (c * R) (mul_pos hc hR) (by
      rw [abs_mul, abs_of_pos hc]
      nlinarith)
  have hfactor : 8 / ((N n : ℝ) * (c * R)) = 8 * sigma / R := by
    dsimp [c, microscopicStep]
    have hN : (N n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt (D.size_pos n))
    field_simp
    ring
  simpa only [hfactor] using h

/-- A weighted selected centered finite resolvent, with the weight evaluated
at each actual finite eigenchannel. -/
def weightedCenteredPartialProposalResolvent (s : Finset (Fin (N n)))
    (theta : Fin (N n) → ℝ) (z : ℂ) (i j : Fin 4)
    (t : ProposalSample (N n) d) : ℂ :=
  ∑ k ∈ s, ((theta k : ℂ) *
    ((N n : ℂ)⁻¹ * ((D.eigenvalue n ω k : ℂ) - z)⁻¹)) *
      (D.centeredProposalQuadratic n ω k i j t : ℂ)

/-- Bounded real cutoff weights preserve the finite covariance estimate. -/
theorem weighted_partial_proposal_variance_le (hd : 0 < d)
    (s : Finset (Fin (N n))) (theta : Fin (N n) → ℝ)
    (htheta : ∀ k ∈ s, |theta k| ≤ 1)
    (C epsilon : ℝ) (hC : 0 ≤ C) (hepsilon : 0 ≤ epsilon) (i j : Fin 4)
    (hcov : ∀ k ∈ s, ∀ l ∈ s, |∫ t, D.centeredProposalQuadratic n ω k i j t *
        D.centeredProposalQuadratic n ω l i j t ∂uniformOrientedProposals (N n) d| ≤
      C * (if k = l then 1 else 0) + epsilon) (z : ℂ) :
    (∫ t, ‖D.weightedCenteredPartialProposalResolvent n ω s theta z i j t‖ ^ 2
      ∂uniformOrientedProposals (N n) d) ≤
      C * (∑ k ∈ s, ‖(N n : ℂ)⁻¹ * ((D.eigenvalue n ω k : ℂ) - z)⁻¹‖ ^ 2) +
        epsilon * (∑ k ∈ s, ‖(N n : ℂ)⁻¹ * ((D.eigenvalue n ω k : ℂ) - z)⁻¹‖) ^ 2 := by
  let a := fun k => (N n : ℂ)⁻¹ * ((D.eigenvalue n ω k : ℂ) - z)⁻¹
  have h := integral_weighted_real_partial_sum_sq_le (uniformOrientedProposals (N n) d)
    (fun k => D.centeredProposalQuadraticLp n ω hd k i j)
    (fun k => D.centeredProposalQuadratic n ω k i j)
    (fun k => (theta k : ℂ) * a k) s C epsilon
    (fun k _ => D.centeredProposalQuadraticLp_ae n ω hd k i j) hcov
  have hn (k) (hk : k ∈ s) : ‖(theta k : ℂ) * a k‖ ≤ ‖a k‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right (htheta k hk) (norm_nonneg (a k))
  have h1 : (∑ k ∈ s, ‖(theta k : ℂ) * a k‖) ≤ ∑ k ∈ s, ‖a k‖ :=
    Finset.sum_le_sum hn
  have h2 : (∑ k ∈ s, ‖(theta k : ℂ) * a k‖ ^ 2) ≤ ∑ k ∈ s, ‖a k‖ ^ 2 := by
    apply Finset.sum_le_sum
    intro k hk
    exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr (hn k hk)
  exact h.trans (add_le_add (mul_le_mul_of_nonneg_left h2 hC)
    (mul_le_mul_of_nonneg_left
      ((sq_le_sq₀ (Finset.sum_nonneg (fun k _ => norm_nonneg _))
        (Finset.sum_nonneg (fun k _ => norm_nonneg _))).mpr h1) hepsilon))

/-- The covariance-controlled weighted remote contribution has a genuine
Poisson-trace tail at an arbitrary nonreal microscopic parameter. -/
theorem weighted_microscopic_remote_variance_le (hd : 0 < d)
    (s : Finset (Fin (N n))) (theta : Fin (N n) → ℝ)
    (htheta : ∀ k ∈ s, |theta k| ≤ 1)
    (E sigma : ℝ) (hsigma : 0 < sigma) (w : GraphNonreal)
    (R : ℝ) (hR : 0 < R) (hw : 2 * |w.1.re| ≤ R)
    (hs : s ⊆ D.remoteEigenvalues n ω E (microscopicStep (N n) sigma * R))
    (C epsilon : ℝ) (hC : 0 ≤ C) (hepsilon : 0 ≤ epsilon) (i j : Fin 4)
    (hcov : ∀ k ∈ s, ∀ l ∈ s, |∫ t, D.centeredProposalQuadratic n ω k i j t *
        D.centeredProposalQuadratic n ω l i j t ∂uniformOrientedProposals (N n) d| ≤
      C * (if k = l then 1 else 0) + epsilon) :
    (∫ t, ‖D.weightedCenteredPartialProposalResolvent n ω s theta
      (microscopicParameter (N n) (D.size_pos n) E sigma hsigma w).1 i j t‖ ^ 2
      ∂uniformOrientedProposals (N n) d) ≤
      C * ((8 * sigma / R) * (D.scalarResolvent n ω
        (spectralParameter E (microscopicStep (N n) sigma * R))).im) +
      epsilon * (∑ k ∈ s, ‖(N n : ℂ)⁻¹ * ((D.eigenvalue n ω k : ℂ) -
        (microscopicParameter (N n) (D.size_pos n) E sigma hsigma w).1)⁻¹‖) ^ 2 := by
  apply (D.weighted_partial_proposal_variance_le n ω hd s theta htheta C epsilon
    hC hepsilon i j hcov _).trans
  apply add_le_add_right
  apply mul_le_mul_of_nonneg_left _ hC
  exact (Finset.sum_le_sum_of_subset_of_nonneg hs (fun k _ _ => sq_nonneg _)).trans
    (D.microscopic_remote_resolvent_coefficient_square_sum_le n ω E sigma hsigma w R hR hw)

end GeneralizedBulk.External.RegularSpectralData
