import GeneralizedBulk.Graph.PartialVariance

/-!
# Deterministic spectral compression away from a fixed bulk window

Completeness of the actual finite eigenbasis bounds any compressed spectral
multiplier by its largest coefficient. Thus the complement of a fixed bulk
window is uniformly bounded, independently of microscopic spectral height.
-/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace GeneralizedBulk.External.RegularSpectralData
open Graph
variable {d : ℕ} {N : ℕ → ℕ} {Ω : Type*} [MeasurableSpace Ω]
variable (D : RegularSpectralData d N Ω) (n : ℕ) (ω : Ω)

/-- Completeness, rather than only column orthonormality, gives a unit row
square sum at every actual graph vertex. -/
theorem eigenvector_row_square_sum (v : Fin (N n)) :
    (∑ k, D.eigenvector n ω k v ^ 2) = 1 := by
  have h := congrArg (fun M : Matrix (Fin (N n)) (Fin (N n)) ℂ => (M v v).re)
    (D.eigenvectorMatrix_mul_transpose n ω)
  simpa only [Matrix.mul_apply, Matrix.transpose_apply, eigenvectorMatrix,
    Complex.re_sum, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, Matrix.one_apply_eq, Complex.one_re, pow_two] using h

/-- The absolute products of any two eigenbasis rows have sum at most one.
The finite-subset version follows without a dimension factor. -/
theorem eigenvector_abs_product_partial_sum_le_one (s : Finset (Fin (N n)))
    (v w : Fin (N n)) :
    (∑ k ∈ s, |D.eigenvector n ω k v * D.eigenvector n ω k w|) ≤ 1 := by
  have hentry (k : Fin (N n)) :
      2 * |D.eigenvector n ω k v * D.eigenvector n ω k w| ≤
        D.eigenvector n ω k v ^ 2 + D.eigenvector n ω k w ^ 2 := by
    rw [abs_mul]
    nlinarith [sq_nonneg (|D.eigenvector n ω k v| - |D.eigenvector n ω k w|),
      sq_abs (D.eigenvector n ω k v), sq_abs (D.eigenvector n ω k w)]
  have hfull : (∑ k, |D.eigenvector n ω k v * D.eigenvector n ω k w|) ≤ 1 := by
    have h := Finset.sum_le_sum (fun k (_ : k ∈ Finset.univ) => hentry k)
    simp only [← Finset.mul_sum, Finset.sum_add_distrib,
      D.eigenvector_row_square_sum n ω v, D.eigenvector_row_square_sum n ω w] at h
    linarith
  exact (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ s)
    (fun k _ _ => abs_nonneg _)).trans hfull

def spectralCompression (s : Finset (Fin (N n))) (a : Fin (N n) → ℂ)
    (v w : Fin (N n)) : ℂ :=
  ∑ k ∈ s, a k * (D.eigenvector n ω k v : ℂ) * (D.eigenvector n ω k w : ℂ)

/-- Any finite spectral multiplier compression is bounded entrywise by the
uniform coefficient bound, with no factor involving the number of channels. -/
theorem spectralCompression_norm_le (s : Finset (Fin (N n)))
    (a : Fin (N n) → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (ha : ∀ k ∈ s, ‖a k‖ ≤ C) (v w : Fin (N n)) :
    ‖D.spectralCompression n ω s a v w‖ ≤ C := by
  calc
    _ ≤ ∑ k ∈ s, ‖a k * (D.eigenvector n ω k v : ℂ) *
        (D.eigenvector n ω k w : ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ k ∈ s, C * |D.eigenvector n ω k v * D.eigenvector n ω k w| := by
      apply Finset.sum_le_sum
      intro k hk
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul]
      simpa only [mul_assoc] using
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (ha k hk)
          (abs_nonneg (D.eigenvector n ω k v))) (abs_nonneg (D.eigenvector n ω k w))
    _ = C * ∑ k ∈ s, |D.eigenvector n ω k v * D.eigenvector n ω k w| :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ C * 1 := mul_le_mul_of_nonneg_left
      (D.eigenvector_abs_product_partial_sum_le_one n ω s v w) hC
    _ = C := mul_one C

/-- A real gap from the spectral center bounds the actual nonreal inverse
coefficient, uniformly in its imaginary part. -/
theorem inverse_spectral_coefficient_le_of_gap (x E eta delta : ℝ) (hdelta : 0 < delta)
    (hx : delta ≤ |x - E|) :
    ‖((x : ℂ) - spectralParameter E eta)⁻¹‖ ≤ delta⁻¹ := by
  have hre : ((x : ℂ) - spectralParameter E eta).re = x - E := by simp [spectralParameter]
  have hnorm : delta ≤ ‖(x : ℂ) - spectralParameter E eta‖ := by
    exact hx.trans (by simpa only [hre] using Complex.abs_re_le_norm ((x : ℂ) - spectralParameter E eta))
  rw [norm_inv]
  exact (inv_le_inv₀ (hdelta.trans_le hnorm) hdelta).mpr hnorm

/-- Every subset of the fixed-cutoff complement has a uniformly bounded
resolvent compression, at all spectral heights. -/
theorem remote_spectralCompression_norm_le (s : Finset (Fin (N n)))
    (E eta delta : ℝ) (hdelta : 0 < delta)
    (hs : s ⊆ D.remoteEigenvalues n ω E delta) (v w : Fin (N n)) :
    ‖D.spectralCompression n ω s
      (fun k => ((D.eigenvalue n ω k : ℂ) - spectralParameter E eta)⁻¹) v w‖ ≤ delta⁻¹ := by
  apply D.spectralCompression_norm_le n ω s _ _ (inv_nonneg.mpr hdelta.le) _ v w
  intro k hk
  exact inverse_spectral_coefficient_le_of_gap _ E eta delta hdelta
    (Finset.mem_filter.mp (hs hk)).2

/-- The selected actual proposal entry before centering. -/
def partialProposalResolvent (s : Finset (Fin (N n))) (z : ℂ) (i j : Fin 4)
    (t : ProposalSample (N n) d) : ℂ :=
  D.spectralCompression n ω s (fun k => ((D.eigenvalue n ω k : ℂ) - z)⁻¹)
    (D.proposalEndpoints n ω t i) (D.proposalEndpoints n ω t j)

theorem partialProposalResolvent_expansion (s : Finset (Fin (N n))) (z : ℂ)
    (i j : Fin 4) (t : ProposalSample (N n) d) :
    D.partialProposalResolvent n ω s z i j t =
      ∑ k ∈ s, ((N n : ℂ)⁻¹ * ((D.eigenvalue n ω k : ℂ) - z)⁻¹) *
        (D.proposalQuadratic n ω k i j t : ℂ) := by
  have hN : (N n : ℂ)⁻¹ * (N n : ℂ) = 1 :=
    inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (Nat.ne_of_gt (D.size_pos n)))
  apply Finset.sum_congr rfl
  intro k hk
  simp only [proposalQuadratic, Complex.ofReal_mul, Complex.ofReal_natCast]
  symm
  calc
    _ = ((N n : ℂ)⁻¹ * (N n : ℂ)) * (((D.eigenvalue n ω k : ℂ) - z)⁻¹ *
        (D.eigenvector n ω k (D.proposalEndpoints n ω t i) : ℂ) *
          (D.eigenvector n ω k (D.proposalEndpoints n ω t j) : ℂ)) := by ring
    _ = _ := by rw [hN, one_mul]

/-- The selected centered expansion is centered by its literal finite
proposal expectation, with no asymptotic replacement of the mean. -/
theorem centeredPartialProposalResolvent_eq (hd : 0 < d)
    (s : Finset (Fin (N n))) (z : ℂ) (i j : Fin 4) (t : ProposalSample (N n) d) :
    D.centeredPartialProposalResolvent n ω s z i j t =
      D.partialProposalResolvent n ω s z i j t -
        ∫ u, D.partialProposalResolvent n ω s z i j u ∂uniformOrientedProposals (N n) d := by
  letI : Nonempty (Fin (N n) × Fin d) := ⟨⟨⟨0, D.size_pos n⟩, ⟨0, hd⟩⟩⟩
  simp_rw [D.partialProposalResolvent_expansion n ω s z i j]
  rw [integral_finset_sum _ (fun k _ =>
    (integrable_finiteUniform_real (D.proposalQuadratic n ω k i j)).ofReal.const_mul _)]
  simp only [centeredPartialProposalResolvent, centeredProposalQuadratic,
    Complex.ofReal_sub, mul_sub, Finset.sum_sub_distrib, integral_const_mul, integral_complex_ofReal]

/-- The centered fixed-cutoff complement is uniformly bounded by `2 / delta`.
This bound does not assert that the complement tends to zero. -/
theorem centered_remote_partialProposalResolvent_norm_le (hd : 0 < d)
    (s : Finset (Fin (N n))) (E eta delta : ℝ) (hdelta : 0 < delta)
    (hs : s ⊆ D.remoteEigenvalues n ω E delta) (i j : Fin 4)
    (t : ProposalSample (N n) d) :
    ‖D.centeredPartialProposalResolvent n ω s (spectralParameter E eta) i j t‖ ≤ 2 / delta := by
  letI := uniformOrientedProposals_isProbability (N n) d (D.size_pos n) hd
  have hb (t : ProposalSample (N n) d) :
      ‖D.partialProposalResolvent n ω s (spectralParameter E eta) i j t‖ ≤ delta⁻¹ :=
    D.remote_spectralCompression_norm_le n ω s E eta delta hdelta hs _ _
  have hmean : ‖∫ u, D.partialProposalResolvent n ω s (spectralParameter E eta) i j u
      ∂uniformOrientedProposals (N n) d‖ ≤ delta⁻¹ := by
    simpa only [measureReal_univ_eq_one, mul_one] using
      norm_integral_le_of_norm_le_const (μ := uniformOrientedProposals (N n) d)
        (Filter.Eventually.of_forall hb)
  rw [D.centeredPartialProposalResolvent_eq n ω hd]
  apply (norm_sub_le _ _).trans
  rw [div_eq_mul_inv]
  linarith [hb t]

/-- In particular its finite second moment is bounded by `4 / delta²`,
uniformly at microscopic heights and without BS input outside the window. -/
theorem centered_remote_partialProposalResolvent_variance_le (hd : 0 < d)
    (s : Finset (Fin (N n))) (E eta delta : ℝ) (hdelta : 0 < delta)
    (hs : s ⊆ D.remoteEigenvalues n ω E delta) (i j : Fin 4) :
    (∫ t, ‖D.centeredPartialProposalResolvent n ω s (spectralParameter E eta) i j t‖ ^ 2
      ∂uniformOrientedProposals (N n) d) ≤ (2 / delta) ^ 2 := by
  letI : Nonempty (Fin (N n) × Fin d) := ⟨⟨⟨0, D.size_pos n⟩, ⟨0, hd⟩⟩⟩
  letI := uniformOrientedProposals_isProbability (N n) d (D.size_pos n) hd
  have hbound (t : ProposalSample (N n) d) :
      ‖D.centeredPartialProposalResolvent n ω s (spectralParameter E eta) i j t‖ ^ 2 ≤
        (2 / delta) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr
      (D.centered_remote_partialProposalResolvent_norm_le n ω hd s E eta delta hdelta hs i j t)
  have h := integral_mono (μ := uniformOrientedProposals (N n) d)
    (integrable_finiteUniform_real (fun t =>
      ‖D.centeredPartialProposalResolvent n ω s (spectralParameter E eta) i j t‖ ^ 2))
    (integrable_const (μ := uniformOrientedProposals (N n) d) ((2 / delta) ^ 2)) hbound
  rw [integral_const] at h
  change _ ≤ (uniformOrientedProposals (N n) d).real Set.univ • (2 / delta) ^ 2 at h
  simpa only [measureReal_univ_eq_one, one_smul] using h

/-- Exact splitting of the full centered finite resolvent into a selected
bulk window and its complement. -/
theorem centered_proposal_resolvent_eq_partial_add_compl (hd : 0 < d)
    (s : Finset (Fin (N n))) (z : ℂ) (hz : z.im ≠ 0) (i j : Fin 4)
    (t : ProposalSample (N n) d) :
    D.resolvent n ω z (D.proposalEndpoints n ω t i) (D.proposalEndpoints n ω t j) -
      D.proposalMean n ω z i j =
      D.centeredPartialProposalResolvent n ω s z i j t +
        D.centeredPartialProposalResolvent n ω sᶜ z i j t := by
  rw [D.centered_proposal_resolvent_expansion n ω hd z hz i j]
  exact (Finset.sum_add_sum_compl s _).symm

/-- The full centered entry is controlled using covariance information only
inside the selected bulk window and a deterministic fixed-gap complement.
The complement contributes a bounded constant and is not claimed to vanish. -/
theorem proposal_resolvent_variance_le_bulk_window (hd : 0 < d)
    (s : Finset (Fin (N n))) (E eta delta : ℝ) (heta : eta ≠ 0) (hdelta : 0 < delta)
    (hs : sᶜ ⊆ D.remoteEigenvalues n ω E delta)
    (C epsilon : ℝ) (hC : 0 ≤ C) (i j : Fin 4)
    (hcov : ∀ k ∈ s, ∀ l ∈ s, |∫ t, D.centeredProposalQuadratic n ω k i j t *
        D.centeredProposalQuadratic n ω l i j t ∂uniformOrientedProposals (N n) d| ≤
      C * (if k = l then 1 else 0) + epsilon) :
    (∫ t, ‖D.resolvent n ω (spectralParameter E eta)
        (D.proposalEndpoints n ω t i) (D.proposalEndpoints n ω t j) -
      D.proposalMean n ω (spectralParameter E eta) i j‖ ^ 2
      ∂uniformOrientedProposals (N n) d) ≤
      2 * (C * ((D.scalarResolvent n ω (spectralParameter E eta)).im / ((N n : ℝ) * eta)) +
        epsilon * (∑ k ∈ s,
          ‖(N n : ℂ)⁻¹ * ((D.eigenvalue n ω k : ℂ) - spectralParameter E eta)⁻¹‖) ^ 2) +
        2 * (2 / delta) ^ 2 := by
  letI : Nonempty (Fin (N n) × Fin d) := ⟨⟨⟨0, D.size_pos n⟩, ⟨0, hd⟩⟩⟩
  letI := uniformOrientedProposals_isProbability (N n) d (D.size_pos n) hd
  have hz : (spectralParameter E eta).im ≠ 0 := by simpa using heta
  let F (t : ProposalSample (N n) d) : ℂ :=
    D.resolvent n ω (spectralParameter E eta)
      (D.proposalEndpoints n ω t i) (D.proposalEndpoints n ω t j) -
        D.proposalMean n ω (spectralParameter E eta) i j
  let G (t : ProposalSample (N n) d) : ℂ :=
    D.centeredPartialProposalResolvent n ω s (spectralParameter E eta) i j t
  let H (t : ProposalSample (N n) d) : ℂ :=
    D.centeredPartialProposalResolvent n ω sᶜ (spectralParameter E eta) i j t
  have hsplit (t : ProposalSample (N n) d) : F t = G t + H t :=
    D.centered_proposal_resolvent_eq_partial_add_compl n ω hd s _ hz i j t
  have hpoint (t : ProposalSample (N n) d) : ‖F t‖ ^ 2 ≤ 2 * ‖G t‖ ^ 2 + 2 * (2 / delta) ^ 2 := by
    have hremote : ‖H t‖ ≤ 2 / delta :=
      D.centered_remote_partialProposalResolvent_norm_le n ω hd sᶜ E eta delta hdelta hs i j t
    have hsqr := (sq_le_sq₀ (norm_nonneg (H t)) (show 0 ≤ 2 / delta by positivity)).mpr hremote
    have hn := (sq_le_sq₀ (norm_nonneg (G t + H t))
      (add_nonneg (norm_nonneg (G t)) (norm_nonneg (H t)))).mpr (norm_add_le (G t) (H t))
    rw [hsplit]
    nlinarith [sq_nonneg (‖G t‖ - ‖H t‖)]
  have hiG : Integrable (fun t => ‖G t‖ ^ 2) (uniformOrientedProposals (N n) d) :=
    integrable_finiteUniform_real _
  have hiConst := integrable_const (μ := uniformOrientedProposals (N n) d) (2 * (2 / delta) ^ 2)
  have hb := integral_mono (μ := uniformOrientedProposals (N n) d)
    (integrable_finiteUniform_real (fun t => ‖F t‖ ^ 2)) ((hiG.const_mul 2).add hiConst) hpoint
  simp only [Pi.add_apply] at hb
  rw [integral_add (hiG.const_mul 2) hiConst, integral_const_mul, integral_const] at hb
  change (∫ t, ‖F t‖ ^ 2 ∂uniformOrientedProposals (N n) d) ≤
    2 * (∫ t, ‖G t‖ ^ 2 ∂uniformOrientedProposals (N n) d) +
      (uniformOrientedProposals (N n) d).real Set.univ • (2 * (2 / delta) ^ 2) at hb
  rw [measureReal_univ_eq_one, one_smul] at hb
  have hv := D.partial_proposal_resolvent_variance_le_ward n ω hd s C epsilon hC i j hcov _ hz
  simp only [spectralParameter_im] at hv
  exact hb.trans (add_le_add_right (mul_le_mul_of_nonneg_left hv (by norm_num : (0 : ℝ) ≤ 2)) _)

end GeneralizedBulk.External.RegularSpectralData
