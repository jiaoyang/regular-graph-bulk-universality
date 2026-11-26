import GeneralizedBulk.Graph.ProposalVariance

/-!
# Bulk windows and remote coefficients in the finite proposal variance

The covariance hypotheses are required only on the selected eigenchannels.
This is useful when the BS limit controls a fixed bulk window, while the
complement is handled deterministically by eigenbasis completeness.
-/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace GeneralizedBulk.Graph

/-- The covariance estimate restricts to any finite collection of channels;
no covariance information about the complement is used. -/
theorem integral_weighted_real_partial_sum_sq_le
    {I Ω : Type*} [DecidableEq I] [MeasurableSpace Ω]
    (mu : Measure Ω) (v : I → Lp ℂ 2 mu) (raw : I → Ω → ℝ) (a : I → ℂ)
    (s : Finset I) (C epsilon : ℝ)
    (hv : ∀ i ∈ s, (v i : Ω → ℂ) =ᵐ[mu] (fun ω => (raw i ω : ℂ)))
    (hcov : ∀ i ∈ s, ∀ j ∈ s, |∫ ω, raw i ω * raw j ω ∂mu| ≤
      C * (if i = j then 1 else 0) + epsilon) :
    (∫ ω, ‖∑ i ∈ s, a i * (raw i ω : ℂ)‖ ^ 2 ∂mu) ≤
      C * (∑ i ∈ s, ‖a i‖ ^ 2) + epsilon * (∑ i ∈ s, ‖a i‖) ^ 2 := by
  have h := integral_weighted_real_sum_sq_le mu
    (fun i : s => v i) (fun i : s => raw i) (fun i : s => a i) C epsilon
    (fun i => hv i i.property)
    (fun i j => by simpa only [Subtype.ext_iff] using hcov i i.property j j.property)
  have hsum (ω : Ω) := Finset.sum_coe_sort s (fun i => a i * (raw i ω : ℂ))
  simp only [hsum, Finset.sum_coe_sort s (fun i => ‖a i‖ ^ 2),
    Finset.sum_coe_sort s (fun i => ‖a i‖)] at h
  exact h

end GeneralizedBulk.Graph

namespace GeneralizedBulk.External.RegularSpectralData
open Graph
variable {d : ℕ} {N : ℕ → ℕ} {Ω : Type*} [MeasurableSpace Ω]
variable (D : RegularSpectralData d N Ω) (n : ℕ) (ω : Ω)

/-- The actual centered finite spectral sum on a selected window. -/
def centeredPartialProposalResolvent (s : Finset (Fin (N n)))
    (z : ℂ) (i j : Fin 4) (t : ProposalSample (N n) d) : ℂ :=
  ∑ k ∈ s, ((N n : ℂ)⁻¹ * ((D.eigenvalue n ω k : ℂ) - z)⁻¹) *
    (D.centeredProposalQuadratic n ω k i j t : ℂ)

/-- Selected-channel covariance gives the actual partial resolvent variance. -/
theorem partial_proposal_resolvent_variance_le (hd : 0 < d)
    (s : Finset (Fin (N n))) (C epsilon : ℝ) (i j : Fin 4)
    (hcov : ∀ k ∈ s, ∀ l ∈ s, |∫ t, D.centeredProposalQuadratic n ω k i j t *
        D.centeredProposalQuadratic n ω l i j t ∂uniformOrientedProposals (N n) d| ≤
      C * (if k = l then 1 else 0) + epsilon) (z : ℂ) :
    (∫ t, ‖D.centeredPartialProposalResolvent n ω s z i j t‖ ^ 2
      ∂uniformOrientedProposals (N n) d) ≤
      C * (∑ k ∈ s, ‖(N n : ℂ)⁻¹ * ((D.eigenvalue n ω k : ℂ) - z)⁻¹‖ ^ 2) +
        epsilon * (∑ k ∈ s, ‖(N n : ℂ)⁻¹ * ((D.eigenvalue n ω k : ℂ) - z)⁻¹‖) ^ 2 := by
  exact integral_weighted_real_partial_sum_sq_le (uniformOrientedProposals (N n) d)
    (fun k => D.centeredProposalQuadraticLp n ω hd k i j)
    (fun k => D.centeredProposalQuadratic n ω k i j)
    (fun k => (N n : ℂ)⁻¹ * ((D.eigenvalue n ω k : ℂ) - z)⁻¹) s C epsilon
    (fun k _ => D.centeredProposalQuadraticLp_ae n ω hd k i j) hcov

/-- The selected diagonal contribution is bounded by the full Ward quantity. -/
theorem partial_proposal_resolvent_variance_le_ward (hd : 0 < d)
    (s : Finset (Fin (N n))) (C epsilon : ℝ) (hC : 0 ≤ C) (i j : Fin 4)
    (hcov : ∀ k ∈ s, ∀ l ∈ s, |∫ t, D.centeredProposalQuadratic n ω k i j t *
        D.centeredProposalQuadratic n ω l i j t ∂uniformOrientedProposals (N n) d| ≤
      C * (if k = l then 1 else 0) + epsilon) (z : ℂ) (hz : z.im ≠ 0) :
    (∫ t, ‖D.centeredPartialProposalResolvent n ω s z i j t‖ ^ 2
      ∂uniformOrientedProposals (N n) d) ≤
      C * ((D.scalarResolvent n ω z).im / ((N n : ℝ) * z.im)) +
        epsilon * (∑ k ∈ s, ‖(N n : ℂ)⁻¹ * ((D.eigenvalue n ω k : ℂ) - z)⁻¹‖) ^ 2 := by
  apply (D.partial_proposal_resolvent_variance_le n ω hd s C epsilon i j hcov z).trans
  apply add_le_add_right
  rw [← D.normalized_resolvent_coefficient_square_sum n ω z hz]
  exact mul_le_mul_of_nonneg_left
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ s)
      (fun k _ _ => sq_nonneg _)) hC

/-- The normalized coefficient square sum on remote channels has the exact
`1 / (N R)` Poisson-trace bound. -/
theorem remote_resolvent_coefficient_square_sum_le (E eta R : ℝ) (hR : 0 < R) :
    (∑ k ∈ D.remoteEigenvalues n ω E R,
      ‖(N n : ℂ)⁻¹ * ((D.eigenvalue n ω k : ℂ) - spectralParameter E eta)⁻¹‖ ^ 2) ≤
      (2 / ((N n : ℝ) * R)) *
        (D.scalarResolvent n ω (spectralParameter E R)).im := by
  have hN : (N n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt (D.size_pos n))
  have hs : (∑ k ∈ D.remoteEigenvalues n ω E R,
      ‖(N n : ℂ)⁻¹ * ((D.eigenvalue n ω k : ℂ) - spectralParameter E eta)⁻¹‖ ^ 2) =
      (N n : ℝ)⁻¹ ^ 2 * (∑ k ∈ D.remoteEigenvalues n ω E R,
        Complex.normSq (((D.eigenvalue n ω k : ℂ) - spectralParameter E eta)⁻¹)) := by
    simp only [norm_mul, mul_pow, norm_inv, Complex.norm_natCast,
      Complex.normSq_eq_norm_sq, ← Finset.mul_sum]
  rw [hs]
  have hb := mul_le_mul_of_nonneg_left (D.remote_spectral_tail_le n ω E eta R hR)
    (sq_nonneg (N n : ℝ)⁻¹)
  convert hb using 1 <;> field_simp <;> ring

/-- A remote portion inside the covariance-controlled bulk window obeys the
Poisson tail estimate. The off-diagonal covariance error is retained. -/
theorem partial_remote_proposal_variance_le (hd : 0 < d)
    (s : Finset (Fin (N n))) (E eta R : ℝ) (hR : 0 < R)
    (hs : s ⊆ D.remoteEigenvalues n ω E R)
    (C epsilon : ℝ) (hC : 0 ≤ C) (i j : Fin 4)
    (hcov : ∀ k ∈ s, ∀ l ∈ s, |∫ t, D.centeredProposalQuadratic n ω k i j t *
        D.centeredProposalQuadratic n ω l i j t ∂uniformOrientedProposals (N n) d| ≤
      C * (if k = l then 1 else 0) + epsilon) :
    (∫ t, ‖D.centeredPartialProposalResolvent n ω s (spectralParameter E eta) i j t‖ ^ 2
      ∂uniformOrientedProposals (N n) d) ≤
      C * ((2 / ((N n : ℝ) * R)) * (D.scalarResolvent n ω (spectralParameter E R)).im) +
        epsilon * (∑ k ∈ s,
          ‖(N n : ℂ)⁻¹ * ((D.eigenvalue n ω k : ℂ) - spectralParameter E eta)⁻¹‖) ^ 2 := by
  apply (D.partial_proposal_resolvent_variance_le n ω hd s C epsilon i j hcov _).trans
  apply add_le_add_right
  apply mul_le_mul_of_nonneg_left _ hC
  exact (Finset.sum_le_sum_of_subset_of_nonneg hs (fun k _ _ => sq_nonneg _)).trans
    (D.remote_resolvent_coefficient_square_sum_le n ω E eta R hR)

end GeneralizedBulk.External.RegularSpectralData
