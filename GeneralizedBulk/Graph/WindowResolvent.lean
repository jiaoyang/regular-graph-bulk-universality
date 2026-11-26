import GeneralizedBulk.Graph.WindowEigenSelection
import GeneralizedBulk.Graph.ProposalMarks
import GeneralizedBulk.Gaussian.WindowLaw

/-! Exact physical finite resolvent truncations in canonical marked-window coordinates. -/
noncomputable section
open MeasureTheory BourgadeHuang
open scoped BigOperators
namespace GeneralizedBulk.External.RegularSpectralData
open Graph GeneralizedBulk.Counting
variable {d : ℕ} {N : ℕ → ℕ} {Ω : Type*} [MeasurableSpace Ω]
variable (D : RegularSpectralData d N Ω) (n : ℕ) (ω : Ω)

theorem microscopic_windowMask_eq_eigenvalueWindow (E sigma R : ℝ) (hsigma : 0 < sigma) :
    maskFinset (windowMask (D.microscopicEigenvalue n ω E sigma) (-R) R) =
      D.eigenvalueWindow n ω E (microscopicStep (N n) sigma * R) := by
  classical
  ext k
  simp only [maskFinset,windowMask,eigenvalueWindow,Finset.mem_filter,Finset.mem_univ,true_and,
    decide_eq_true_eq,Set.mem_Icc,← abs_le]
  have hc : 0 < (N n : ℝ) * sigma := mul_pos (Nat.cast_pos.mpr (D.size_pos n)) hsigma
  rw [microscopicEigenvalue,abs_mul,abs_of_pos hc]
  simpa only [microscopicStep,div_eq_mul_inv,mul_comm] using
    ((le_div_iff₀ hc) : |D.eigenvalue n ω k - E| ≤ R / ((N n : ℝ) * sigma) ↔
      |D.eigenvalue n ω k - E| * ((N n : ℝ) * sigma) ≤ R).symm

/-- The genuine finite covariance-centered window compression is exactly
the finite Gaussian-series polynomial in the actual endpoint marks and
the canonical sorted microscopic occurrences. -/
theorem fixedCovariancePartial_eq_finiteParticleField
    (parameters : Parameters) (E R : ℝ) (w : GraphNonreal)
    (t : ProposalSample (N n) d) (i j : Fin 4) :
    D.fixedCovariancePartialProposalResolvent n ω
      (D.eigenvalueWindow n ω E (microscopicStep (N n) parameters.scale * R)) parameters.p
      (microscopicParameter (N n) (D.size_pos n) E parameters.scale parameters.scale_pos w).val i j t =
      Gaussian.finiteParticleField parameters
        (fun k : Fin (D.windowEigenCount n ω E parameters.scale (-R) R) =>
          windowOccurrence (D.microscopicCountingState n ω E parameters.scale 0).val.1 (-R) R k.val)
        (w.val,false)
        (D.proposalMark n ω (fun k => D.eigenvector n ω
          (D.windowEigenIndex n ω E parameters.scale (-R) R k.val)) t) i j := by
  let x := D.microscopicEigenvalue n ω E parameters.scale
  let sel : Fin (D.windowEigenCount n ω E parameters.scale (-R) R) → Fin (N n) :=
    fun k => D.windowEigenIndex n ω E parameters.scale (-R) R k.val
  let z := (microscopicParameter (N n) (D.size_pos n) E parameters.scale parameters.scale_pos w).val
  let f := fun k : Fin (N n) => ((N n : ℂ)⁻¹ * ((D.eigenvalue n ω k : ℂ) - z)⁻¹) *
    ((D.proposalQuadratic n ω k i j t - covarianceMatrix parameters.p i j : ℝ) : ℂ)
  have hs := sum_rankedWindowIndex (D.size_pos n) x
    (D.microscopicEigenvalue_antitone n ω E parameters.scale parameters.scale_pos) (-R) R f
  rw [D.microscopic_windowMask_eq_eigenvalueWindow n ω E parameters.scale R parameters.scale_pos] at hs
  change (∑ k ∈ D.eigenvalueWindow n ω E (microscopicStep (N n) parameters.scale * R), f k) = _
  rw [← hs]
  apply Finset.sum_congr rfl
  intro k hk
  have hloc := D.windowEigenIndex_matches_occurrence n ω E parameters.scale (-R) R parameters.scale_pos k.val k.isLt
  have hprod := D.proposalMark_product n ω sel k i j t
  change ((N n : ℂ)⁻¹ * ((D.eigenvalue n ω (sel k) : ℂ) - z)⁻¹) *
      ((D.proposalQuadratic n ω (sel k) i j t - covarianceMatrix parameters.p i j : ℝ) : ℂ) =
    (parameters.scale : ℂ) * Gaussian.particleCoefficient
      (windowOccurrence (D.microscopicCountingState n ω E parameters.scale 0).val.1 (-R) R k.val) (w.val,false) *
      (Gaussian.rawQuadratic parameters.p i j (fun a =>
        D.proposalMark n ω (fun k => D.eigenvector n ω (sel k)) t (k,a)) : ℂ)
  rw [← hloc,D.microscopic_coefficient_eq n ω E parameters.scale parameters.scale_pos w (sel k)]
  simp only [Gaussian.particleCoefficient,w.property,ite_false,Bool.false_eq_true,
    Gaussian.rawQuadratic]
  rw [hprod]

end GeneralizedBulk.External.RegularSpectralData
