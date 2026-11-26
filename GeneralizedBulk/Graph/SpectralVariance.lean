import GeneralizedBulk.Gaussian.SeriesBounds
import GeneralizedBulk.Graph.ResolventBounds

/-!
# Centered finite spectral variance from quadratic-mark covariance

The diagonal covariance contributes the coefficient square sum, while the
explicit off-diagonal error contributes the square of the coefficient one
norm. The Ward identity later identifies the diagonal resolvent contribution.
No concentration estimate is assumed as an input.
-/
noncomputable section
open MeasureTheory
open scoped BigOperators ComplexConjugate
namespace GeneralizedBulk.Graph

/-- The finite covariance expansion gives the quantitative Hilbert variance
bound, retaining every off-diagonal covariance error. -/
theorem norm_weighted_sum_sq_le_covariance
    {I E : Type*} [Fintype I] [DecidableEq I]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (v : I → E) (a : I → ℂ) (C epsilon : ℝ)
    (hcov : ∀ i j, ‖@inner ℂ E _ (v i) (v j)‖ ≤
      C * (if i = j then 1 else 0) + epsilon) :
    ‖∑ i, a i • v i‖ ^ 2 ≤ C * (∑ i, ‖a i‖ ^ 2) + epsilon * (∑ i, ‖a i‖) ^ 2 := by
  let S := ∑ i, a i • v i
  have hexpand : @inner ℂ E _ S S =
      ∑ i, ∑ j, @inner ℂ E _ (a i • v i) (a j • v j) := by
    simp only [S, sum_inner, inner_sum]
    exact Finset.sum_comm
  have hentry (i j : I) : ‖@inner ℂ E _ (a i • v i) (a j • v j)‖ ≤
      ‖a i‖ * ‖a j‖ * (C * (if i = j then 1 else 0) + epsilon) := by
    rw [inner_smul_left, inner_smul_right, norm_mul, norm_mul, Complex.norm_conj]
    simpa only [mul_assoc, mul_left_comm, mul_comm] using
      mul_le_mul_of_nonneg_left (hcov i j) (mul_nonneg (norm_nonneg (a i)) (norm_nonneg (a j)))
  have hdelta (i : I) :
      (∑ j, ‖a i‖ * ‖a j‖ * (C * (if i = j then 1 else 0))) = C * ‖a i‖ ^ 2 := by
    simp only [mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq]
    simp only [Finset.mem_univ, ↓reduceIte]
    ring
  have hsum : (∑ i, ∑ j, ‖a i‖ * ‖a j‖ *
      (C * (if i = j then 1 else 0) + epsilon)) =
      C * (∑ i, ‖a i‖ ^ 2) + epsilon * (∑ i, ‖a i‖) ^ 2 := by
    simp only [mul_add, Finset.sum_add_distrib, hdelta]
    rw [← Finset.mul_sum]
    have he : (∑ i, ∑ j, ‖a i‖ * ‖a j‖ * epsilon) = epsilon * (∑ i, ‖a i‖) ^ 2 := by
      simp only [← Finset.sum_mul, ← Finset.mul_sum, pow_two]
      ring
    rw [he]
  calc
    ‖S‖ ^ 2 = (@inner ℂ E _ S S).re := (inner_self_eq_norm_sq (𝕜 := ℂ) S).symm
    _ ≤ ‖@inner ℂ E _ S S‖ := Complex.re_le_norm _
    _ = ‖∑ i, ∑ j, @inner ℂ E _ (a i • v i) (a j • v j)‖ := by rw [hexpand]
    _ ≤ ∑ i, ‖∑ j, @inner ℂ E _ (a i • v i) (a j • v j)‖ := norm_sum_le _ _
    _ ≤ ∑ i, ∑ j, ‖@inner ℂ E _ (a i • v i) (a j • v j)‖ :=
      Finset.sum_le_sum (fun i _ => norm_sum_le _ _)
    _ ≤ ∑ i, ∑ j, ‖a i‖ * ‖a j‖ * (C * (if i = j then 1 else 0) + epsilon) :=
      Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hentry i j))
    _ = _ := hsum

/-- A diagonal second-moment bound and an explicit off-diagonal covariance
bound supply the preceding quantitative estimate. -/
theorem norm_weighted_sum_sq_le_diag_off
    {I E : Type*} [Fintype I] [DecidableEq I]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (v : I → E) (a : I → ℂ) (C epsilon : ℝ) (hepsilon : 0 ≤ epsilon)
    (hdiag : ∀ i, ‖v i‖ ^ 2 ≤ C)
    (hoff : ∀ i j, i ≠ j → ‖@inner ℂ E _ (v i) (v j)‖ ≤ epsilon) :
    ‖∑ i, a i • v i‖ ^ 2 ≤ C * (∑ i, ‖a i‖ ^ 2) + epsilon * (∑ i, ‖a i‖) ^ 2 := by
  apply norm_weighted_sum_sq_le_covariance v a C epsilon
  intro i j
  by_cases hij : i = j
  · subst j
    simp only [↓reduceIte, mul_one]
    have hn : ‖@inner ℂ E _ (v i) (v i)‖ = ‖v i‖ ^ 2 := by
      simp only [inner_self_eq_norm_sq_to_K, norm_pow, RCLike.norm_ofReal, abs_norm]
    rw [hn]
    exact (hdiag i).trans (le_add_of_nonneg_right hepsilon)
  · simpa only [hij, ↓reduceIte, mul_zero, zero_add] using hoff i j hij

private theorem finite_Lp_sum_ae
    {I Ω : Type*} [MeasurableSpace Ω] (mu : Measure Ω)
    (v : I → Lp ℂ 2 mu) (raw : I → Ω → ℂ)
    (hv : ∀ i, (v i : Ω → ℂ) =ᵐ[mu] raw i) (s : Finset I) :
    ((∑ i ∈ s, v i : Lp ℂ 2 mu) : Ω → ℂ) =ᵐ[mu] (fun ω => ∑ i ∈ s, raw i ω) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty, Pi.zero_apply] using Lp.coeFn_zero ℂ 2 mu
  | @insert i s hi ih =>
      simp only [Finset.sum_insert hi]
      filter_upwards [Lp.coeFn_add (v i) (∑ j ∈ s, v j), hv i, ih] with ω ha hi hs
      simpa only [Pi.add_apply, hi, hs] using ha

/-- The Hilbert estimate is the actual finite second moment of the chosen
sample functions, independently of the representatives of their L² classes. -/
theorem integral_weighted_sum_sq_le_covariance
    {I Ω : Type*} [Fintype I] [DecidableEq I] [MeasurableSpace Ω]
    (mu : Measure Ω) (v : I → Lp ℂ 2 mu) (raw : I → Ω → ℂ) (a : I → ℂ)
    (C epsilon : ℝ) (hv : ∀ i, (v i : Ω → ℂ) =ᵐ[mu] raw i)
    (hcov : ∀ i j, ‖@inner ℂ (Lp ℂ 2 mu) _ (v i) (v j)‖ ≤
      C * (if i = j then 1 else 0) + epsilon) :
    (∫ ω, ‖∑ i, a i * raw i ω‖ ^ 2 ∂mu) ≤
      C * (∑ i, ‖a i‖ ^ 2) + epsilon * (∑ i, ‖a i‖) ^ 2 := by
  let S : Lp ℂ 2 mu := ∑ i, a i • v i
  have hterms (i : I) : ((a i • v i : Lp ℂ 2 mu) : Ω → ℂ) =ᵐ[mu]
      (fun ω => a i * raw i ω) := by
    filter_upwards [Lp.coeFn_smul (a i) (v i), hv i] with ω hs hv
    simpa only [Pi.smul_apply, smul_eq_mul, hv] using hs
  have hs := finite_Lp_sum_ae mu (fun i => a i • v i) (fun i ω => a i * raw i ω) hterms Finset.univ
  have he : (fun ω => ‖∑ i, a i * raw i ω‖ ^ 2) =ᵐ[mu] (fun ω => ‖S ω‖ ^ 2) :=
    hs.mono (fun ω h => congrArg (fun z : ℂ => ‖z‖ ^ 2) h.symm)
  rw [integral_congr_ae he, Gaussian.integral_norm_sq_L2]
  exact norm_weighted_sum_sq_le_covariance v a C epsilon hcov

/-- Explicit real quadratic-mark cross covariances supply the complex L²
hypotheses; the concentration bound remains a proved conclusion. -/
theorem integral_weighted_real_sum_sq_le
    {I Ω : Type*} [Fintype I] [DecidableEq I] [MeasurableSpace Ω]
    (mu : Measure Ω) (v : I → Lp ℂ 2 mu) (raw : I → Ω → ℝ) (a : I → ℂ)
    (C epsilon : ℝ) (hv : ∀ i, (v i : Ω → ℂ) =ᵐ[mu] (fun ω => (raw i ω : ℂ)))
    (hcov : ∀ i j, |∫ ω, raw i ω * raw j ω ∂mu| ≤
      C * (if i = j then 1 else 0) + epsilon) :
    (∫ ω, ‖∑ i, a i * (raw i ω : ℂ)‖ ^ 2 ∂mu) ≤
      C * (∑ i, ‖a i‖ ^ 2) + epsilon * (∑ i, ‖a i‖) ^ 2 := by
  apply integral_weighted_sum_sq_le_covariance mu v (fun i ω => (raw i ω : ℂ)) a C epsilon hv
  intro i j
  have hi : @inner ℂ (Lp ℂ 2 mu) _ (v i) (v j) =
      ((∫ ω, raw i ω * raw j ω ∂mu : ℝ) : ℂ) := by
    rw [Gaussian.l2_inner_eq_bilinear_of_ae_real mu (v i) (v j) (raw i) (hv i)]
    have he : (fun ω => v i ω * v j ω) =ᵐ[mu]
        (fun ω => (raw i ω * raw j ω : ℝ)) := by
      filter_upwards [hv i, hv j] with ω hi hj
      simp only [hi, hj, Complex.ofReal_mul]
    rw [integral_congr_ae he, integral_complex_ofReal]
  rw [hi, Complex.norm_real, Real.norm_eq_abs]
  exact hcov i j

end GeneralizedBulk.Graph

namespace GeneralizedBulk.External.RegularSpectralData
open Graph
variable {d : ℕ} {N : ℕ → ℕ} {Ω : Type*} [MeasurableSpace Ω]
variable (D : RegularSpectralData d N Ω) (n : ℕ) (ω : Ω)

/-- The diagonal term in finite spectral variance is exactly the scalar Ward
quantity, retaining the actual `1/N` coefficients. -/
theorem normalized_resolvent_coefficient_square_sum (z : ℂ) (hz : z.im ≠ 0) :
    (∑ i, ‖(N n : ℂ)⁻¹ * ((D.eigenvalue n ω i : ℂ) - z)⁻¹‖ ^ 2) =
      (D.scalarResolvent n ω z).im / ((N n : ℝ) * z.im) := by
  have hN : (N n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt (D.size_pos n))
  have hm : (D.scalarResolvent n ω z).im = (N n : ℝ)⁻¹ * z.im *
      ∑ i, Complex.normSq (((D.eigenvalue n ω i : ℂ) - z)⁻¹) := by
    rw [D.scalarResolvent_im_eq n ω z hz]
    simp only [Complex.normSq_inv, div_eq_mul_inv, ← Finset.mul_sum]
    ring
  have hs : (∑ i, ‖(N n : ℂ)⁻¹ * ((D.eigenvalue n ω i : ℂ) - z)⁻¹‖ ^ 2) =
      (N n : ℝ)⁻¹ ^ 2 * ∑ i, Complex.normSq (((D.eigenvalue n ω i : ℂ) - z)⁻¹) := by
    simp only [norm_mul, mul_pow, norm_inv, Complex.norm_natCast,
      Complex.normSq_eq_norm_sq, ← Finset.mul_sum]
  rw [hs, hm]
  field_simp
  ring

/-- Centered finite marked spectral sums therefore satisfy the Ward variance
bound plus the explicit off-diagonal covariance contribution. -/
theorem integral_centered_spectral_variance_le
    {T : Type*} [MeasurableSpace T] (mu : Measure T)
    (v : Fin (N n) → Lp ℂ 2 mu) (raw : Fin (N n) → T → ℝ)
    (C epsilon : ℝ) (hv : ∀ i, (v i : T → ℂ) =ᵐ[mu] (fun γ => (raw i γ : ℂ)))
    (hcov : ∀ i j, |∫ γ, raw i γ * raw j γ ∂mu| ≤
      C * (if i = j then 1 else 0) + epsilon)
    (z : ℂ) (hz : z.im ≠ 0) :
    (∫ γ, ‖∑ i, ((N n : ℂ)⁻¹ * ((D.eigenvalue n ω i : ℂ) - z)⁻¹) * (raw i γ : ℂ)‖ ^ 2 ∂mu) ≤
      C * ((D.scalarResolvent n ω z).im / ((N n : ℝ) * z.im)) +
        epsilon * (∑ i, ‖(N n : ℂ)⁻¹ * ((D.eigenvalue n ω i : ℂ) - z)⁻¹‖) ^ 2 := by
  have h := integral_weighted_real_sum_sq_le mu v raw
    (fun i => (N n : ℂ)⁻¹ * ((D.eigenvalue n ω i : ℂ) - z)⁻¹) C epsilon hv hcov
  rw [D.normalized_resolvent_coefficient_square_sum n ω z hz] at h
  exact h

end GeneralizedBulk.External.RegularSpectralData
