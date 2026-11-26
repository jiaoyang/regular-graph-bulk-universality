import GeneralizedBulk.Graph.Resolvent

/-!
# Exact finite counting and remote spectral-tail bounds

The normalization is the genuine normalized adjacency trace. HY supplies
only its mesoscopic upper bound; the conversion to local counts and remote
inverse-square tails is proved by finite Poisson-kernel inequalities.
-/
noncomputable section
open scoped BigOperators
open MeasureTheory
namespace GeneralizedBulk.External.RegularSpectralData

variable {d : ℕ} {N : ℕ → ℕ} {Ω : Type*} [MeasurableSpace Ω]
variable (D : RegularSpectralData d N Ω) (n : ℕ) (ω : Ω)

def spectralParameter (E eta : ℝ) : ℂ := (E : ℂ) + (eta : ℂ) * Complex.I

def realPoissonKernel (E eta x : ℝ) : ℝ := eta / ((x - E) ^ 2 + eta ^ 2)

@[simp] theorem spectralParameter_im (E eta : ℝ) : (spectralParameter E eta).im = eta := by
  simp [spectralParameter]

theorem normSq_real_sub_spectralParameter (x E eta : ℝ) :
    Complex.normSq ((x : ℂ) - spectralParameter E eta) = (x - E) ^ 2 + eta ^ 2 := by
  simp [spectralParameter, Complex.normSq_apply, pow_two]

theorem scalarResolvent_im_eq (z : ℂ) (hz : z.im ≠ 0) :
    (D.scalarResolvent n ω z).im = (N n : ℝ)⁻¹ *
      ∑ a, z.im / Complex.normSq ((D.eigenvalue n ω a : ℂ) - z) := by
  rw [D.scalarResolvent_eq_spectral n ω z hz]
  have hcast : ((N n : ℂ)⁻¹) = Complex.ofReal ((N n : ℝ)⁻¹) := by simp
  rw [hcast]
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero,
    Complex.im_sum, Complex.inv_im, Complex.sub_im, zero_sub, neg_neg]

theorem scalarResolvent_poisson (E eta : ℝ) (heta : eta ≠ 0) :
    (D.scalarResolvent n ω (spectralParameter E eta)).im = (N n : ℝ)⁻¹ *
      ∑ a, realPoissonKernel E eta (D.eigenvalue n ω a) := by
  rw [D.scalarResolvent_im_eq n ω _ (by simpa using heta)]
  simp only [spectralParameter_im, normSq_real_sub_spectralParameter, realPoissonKernel]

def eigenvalueWindow (E eta : ℝ) : Finset (Fin (N n)) :=
  Finset.univ.filter (fun a => |D.eigenvalue n ω a - E| ≤ eta)

def eigenvalueWindowCount (E eta : ℝ) : ℕ := (D.eigenvalueWindow n ω E eta).card

private theorem local_poisson_lower (E eta x : ℝ) (heta : 0 < eta)
    (hx : |x - E| ≤ eta) : (2 * eta)⁻¹ ≤ realPoissonKernel E eta x := by
  have hsq : (x - E) ^ 2 ≤ eta ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg (x - E)) heta.le).mpr hx
  have hden : 0 < (x - E) ^ 2 + eta ^ 2 := by nlinarith [sq_nonneg (x - E)]
  rw [realPoissonKernel, inv_eq_one_div, div_le_div_iff₀ (by positivity : 0 < 2 * eta) hden]
  nlinarith only [hsq]

private theorem realPoissonKernel_nonneg (E eta x : ℝ) (heta : 0 ≤ eta) :
    0 ≤ realPoissonKernel E eta x := div_nonneg heta (add_nonneg (sq_nonneg _) (sq_nonneg _))

/-- Finite local eigenvalue counts are controlled by the actual normalized
resolvent trace, with the explicit factor `2 N eta`. -/
theorem eigenvalueWindowCount_le (E eta : ℝ) (heta : 0 < eta) :
    (D.eigenvalueWindowCount n ω E eta : ℝ) ≤
      2 * (N n : ℝ) * eta * (D.scalarResolvent n ω (spectralParameter E eta)).im := by
  classical
  have hb : (D.eigenvalueWindowCount n ω E eta : ℝ) * (2 * eta)⁻¹ ≤
      ∑ a, realPoissonKernel E eta (D.eigenvalue n ω a) := by
    calc
      _ = ∑ a ∈ D.eigenvalueWindow n ω E eta, (2 * eta)⁻¹ := by
        simp [eigenvalueWindowCount, nsmul_eq_mul]
      _ ≤ ∑ a ∈ D.eigenvalueWindow n ω E eta, realPoissonKernel E eta (D.eigenvalue n ω a) := by
        apply Finset.sum_le_sum
        intro a ha
        exact local_poisson_lower E eta _ heta (Finset.mem_filter.mp ha).2
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun a _ _ => realPoissonKernel_nonneg E eta _ heta.le)
  have hN : (N n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt (D.size_pos n))
  have htrace : (N n : ℝ) * (D.scalarResolvent n ω (spectralParameter E eta)).im =
      ∑ a, realPoissonKernel E eta (D.eigenvalue n ω a) := by
    rw [D.scalarResolvent_poisson n ω E eta (ne_of_gt heta), ← mul_assoc,
      mul_inv_cancel₀ hN, one_mul]
  have hh := mul_le_mul_of_nonneg_left hb (show 0 ≤ 2 * eta by positivity)
  have heta0 : 2 * eta ≠ 0 := by positivity
  rw [← mul_assoc, mul_comm (2 * eta) _, mul_assoc, mul_inv_cancel₀ heta0, mul_one] at hh
  rw [← htrace] at hh
  convert hh using 1 <;> ring

/-- A direct HY-to-count adapter. The finite Poisson calculation contributes
no additional spectral assumption. -/
theorem eigenvalueWindowCount_le_of_HY
    {P : Measure Ω} [IsProbabilityMeasure P] {K : Set ℝ} {alpha : ℝ}
    (H : HYMesoscopicInput D P K alpha)
    (hn : H.events.threshold ≤ n) (hω : ω ∈ H.events.good n)
    (E : ℝ) (hE : E ∈ K) (eta : ℝ) (heta : 0 < eta)
    (hmeso : (N n : ℝ) ^ (-1 + alpha) ≤ eta) (hupper : eta ≤ 1) :
    (D.eigenvalueWindowCount n ω E eta : ℝ) ≤
      2 * (N n : ℝ) * eta * H.events.constant := by
  have hm := H.trace_bound n hn ω hω E hE eta heta hmeso hupper
  exact (D.eigenvalueWindowCount_le n ω E eta heta).trans
    (mul_le_mul_of_nonneg_left hm (by positivity))

def remoteEigenvalues (E R : ℝ) : Finset (Fin (N n)) :=
  Finset.univ.filter (fun a => R ≤ |D.eigenvalue n ω a - E|)

private theorem remote_inverse_square_le (x E eta R : ℝ) (hR : 0 < R)
    (hx : R ≤ |x - E|) :
    ((x - E) ^ 2 + eta ^ 2)⁻¹ ≤ (2 / R) * realPoissonKernel E R x := by
  have hsq : R ^ 2 ≤ (x - E) ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ hR.le (abs_nonneg (x - E))).mpr hx
  have hdenEta : 0 < (x - E) ^ 2 + eta ^ 2 := by nlinarith [sq_nonneg eta]
  have hdenR : 0 < (x - E) ^ 2 + R ^ 2 := by nlinarith [sq_nonneg (x - E)]
  calc
    _ ≤ 2 / ((x - E) ^ 2 + R ^ 2) := by
      rw [inv_eq_one_div, div_le_div_iff₀ hdenEta hdenR]
      nlinarith [sq_nonneg eta]
    _ = _ := by
      dsimp [realPoissonKernel]
      field_simp

/-- A remote inverse-square tail at any spectral height is bounded by the
Poisson trace at height `R`. The exact normalized form decays as `1/R`. -/
theorem remote_spectral_tail_le (E eta R : ℝ) (hR : 0 < R) :
    (∑ a ∈ D.remoteEigenvalues n ω E R,
      Complex.normSq (((D.eigenvalue n ω a : ℂ) - spectralParameter E eta)⁻¹)) ≤
      (2 * (N n : ℝ) / R) * (D.scalarResolvent n ω (spectralParameter E R)).im := by
  classical
  have hb : (∑ a ∈ D.remoteEigenvalues n ω E R,
      Complex.normSq (((D.eigenvalue n ω a : ℂ) - spectralParameter E eta)⁻¹)) ≤
      (2 / R) * ∑ a, realPoissonKernel E R (D.eigenvalue n ω a) := by
    calc
      _ ≤ ∑ a ∈ D.remoteEigenvalues n ω E R, (2 / R) * realPoissonKernel E R (D.eigenvalue n ω a) := by
        apply Finset.sum_le_sum
        intro a ha
        rw [Complex.normSq_inv, normSq_real_sub_spectralParameter]
        exact remote_inverse_square_le _ E eta R hR (Finset.mem_filter.mp ha).2
      _ ≤ ∑ a, (2 / R) * realPoissonKernel E R (D.eigenvalue n ω a) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun a _ _ => mul_nonneg (by positivity) (realPoissonKernel_nonneg E R _ hR.le))
      _ = _ := (Finset.mul_sum _ _ _).symm
  have hN : (N n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt (D.size_pos n))
  have htrace : (N n : ℝ) * (D.scalarResolvent n ω (spectralParameter E R)).im =
      ∑ a, realPoissonKernel E R (D.eigenvalue n ω a) := by
    rw [D.scalarResolvent_poisson n ω E R (ne_of_gt hR), ← mul_assoc,
      mul_inv_cancel₀ hN, one_mul]
  rw [← htrace] at hb
  convert hb using 1 <;> ring

/-- HY supplies only the mesoscopic trace estimate in this actual normalized
remote-tail bound. The finite spectral-tail inequality has been proved. -/
theorem normalized_remote_spectral_tail_le_of_HY
    {P : Measure Ω} [IsProbabilityMeasure P] {K : Set ℝ} {alpha : ℝ}
    (H : HYMesoscopicInput D P K alpha)
    (hn : H.events.threshold ≤ n) (hω : ω ∈ H.events.good n)
    (E : ℝ) (hE : E ∈ K) (eta R : ℝ) (hR : 0 < R)
    (hmeso : (N n : ℝ) ^ (-1 + alpha) ≤ R) (hupper : R ≤ 1) :
    (N n : ℝ)⁻¹ * (∑ a ∈ D.remoteEigenvalues n ω E R,
      Complex.normSq (((D.eigenvalue n ω a : ℂ) - spectralParameter E eta)⁻¹)) ≤
      (2 / R) * H.events.constant := by
  have hm := H.trace_bound n hn ω hω E hE R hR hmeso hupper
  have ht := mul_le_mul_of_nonneg_left (D.remote_spectral_tail_le n ω E eta R hR)
    (inv_nonneg.mpr (Nat.cast_nonneg (N n)))
  have hN : (N n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt (D.size_pos n))
  have hs : (N n : ℝ)⁻¹ * ((2 * (N n : ℝ) / R) *
      (D.scalarResolvent n ω (spectralParameter E R)).im) =
      (2 / R) * (D.scalarResolvent n ω (spectralParameter E R)).im := by
    field_simp
    ring
  rw [hs] at ht
  exact ht.trans (mul_le_mul_of_nonneg_left hm (by positivity))

end GeneralizedBulk.External.RegularSpectralData
