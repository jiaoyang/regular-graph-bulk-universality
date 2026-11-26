import GeneralizedBulk.Graph.EmpiricalWhitening
import GeneralizedBulk.Entropy.WhiteningBounds

/-! The external HY coordinate bound gives a proved uniform bound on the
actual normalized empirical signal, with no extra whitening assumption. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace GeneralizedBulk.External.RegularSpectralData
open GeneralizedBulk.Entropy.Channel GeneralizedBulk.Entropy.Mehler

variable {d : ℕ} {N : ℕ → ℕ} {Ω : Type*} [MeasurableSpace Ω]
variable (D : RegularSpectralData d N Ω) (n : ℕ) (ω : Ω)

theorem empiricalPhysicalStar_abs_bound {k : ℕ} (hd : 2 ≤ d) (selection : Fin k → Fin (N n))
    (B : ℝ) (hU : ∀ a v, Real.sqrt (N n) * |D.eigenvector n ω (selection a) v| ≤ B)
    (s : EmpiricalStarSample d (N n)) (a : Fin k) (i : Option (Fin d)) :
    |(D.empiricalPhysicalStar n ω hd selection s a : Physical d) i| ≤ B := by
  cases i with
  | none =>
    change |Real.sqrt (N n) * D.eigenvector n ω (selection a) s.1| ≤ B
    rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
    exact hU a s.1
  | some i =>
    change |Real.sqrt (N n) * D.eigenvector n ω (selection a) (D.neighbor n ω s.1 (s.2 i))| ≤ B
    rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
    exact hU a _

theorem empiricalWhiteStar_component_bound {k : ℕ} (hd : 3 ≤ d)
    (selection : Fin k → Fin (N n))
    (hbulk : ∀ a, (D.eigenvalue n ω (selection a) / d) ^ 2 < 4 * ((d : ℝ) - 1) / (d : ℝ) ^ 2)
    (B : ℝ) (hB : 0 ≤ B)
    (hU : ∀ a v, Real.sqrt (N n) * |D.eigenvector n ω (selection a) v| ≤ B)
    (s : EmpiricalStarSample d (N n)) (a : Fin k) :
    ‖D.empiricalWhiteStar n ω (by omega) selection s a‖ ≤ (d : ℝ) * ((d : ℝ) + 1) * B := by
  let c := D.eigenvalue n ω (selection a) / d
  let x := D.empiricalPhysicalStar n ω (by omega) selection s a
  let y := inverseWhitening d c (rho c) x
  have hrho : rho c ≠ 0 := ne_of_gt (rho_pos c (bulk_rho_lower d hd c (hbulk a)).1)
  have hp : physicalLinearMap d (by omega) c (rho c) y = (x : Physical d) :=
    congrArg Subtype.val (inverseWhitening_right d (by omega) c (rho c) hrho x)
  have hi := bulk_whitening_inverse_norm_le d hd c (hbulk a) y
  rw [hp] at hi
  have hn := physical_norm_le_of_coordinate_bound d (x : Physical d) B hB
    (fun i => D.empiricalPhysicalStar_abs_bound n ω (by omega) selection B hU s a i)
  have hh := hi.trans (mul_le_mul_of_nonneg_left hn (Nat.cast_nonneg d))
  convert hh using 1 <;> dsimp [empiricalWhiteStar, y, c, x, GeneralizedBulk.Gaussian.starRho, rho] <;> ring

theorem empiricalWhiteStar_norm_bound {k : ℕ} (hd : 3 ≤ d)
    (selection : Fin k → Fin (N n))
    (hbulk : ∀ a, (D.eigenvalue n ω (selection a) / d) ^ 2 < 4 * ((d : ℝ) - 1) / (d : ℝ) ^ 2)
    (B : ℝ) (hB : 0 ≤ B)
    (hU : ∀ a v, Real.sqrt (N n) * |D.eigenvector n ω (selection a) v| ≤ B)
    (s : EmpiricalStarSample d (N n)) :
    ‖D.empiricalWhiteStar n ω (by omega) selection s‖ ≤ (k : ℝ) * d * ((d : ℝ) + 1) * B := by
  apply (colored_norm_le_sum d k _).trans
  calc
    _ ≤ ∑ _ : Fin k, (d : ℝ) * ((d : ℝ) + 1) * B :=
      Finset.sum_le_sum (fun a _ => D.empiricalWhiteStar_component_bound n ω hd selection hbulk B hB hU s a)
    _ = _ := by simp; ring

theorem empiricalNormalizedSignal_bound {k : ℕ} (hd : 3 ≤ d)
    (selection : Fin k → Fin (N n)) (hinj : Function.Injective selection)
    (hE : ∀ a, |D.eigenvalue n ω (selection a)| < d)
    (hbulk : ∀ a, (D.eigenvalue n ω (selection a) / d) ^ 2 < 4 * ((d : ℝ) - 1) / (d : ℝ) ^ 2)
    (B : ℝ) (hB : 0 ≤ B)
    (hU : ∀ a v, Real.sqrt (N n) * |D.eigenvector n ω (selection a) v| ≤ B)
    (s : EmpiricalStarSample d (N n)) :
    coordinateL1 ((D.empiricalNormalizedSignal n ω (by omega) selection hinj hE).signal s) ≤
      (Fintype.card (ScalarCoordinate d k) : ℝ) * ((k : ℝ) * d * ((d : ℝ) + 1) * B) := by
  have hnorm := D.empiricalWhiteStar_norm_bound n ω hd selection hbulk B hB hU s
  have hi (i : ScalarCoordinate d k) :
      |(D.empiricalNormalizedSignal n ω (by omega) selection hinj hE).signal s i| ≤
        ‖D.empiricalWhiteStar n ω (by omega) selection s‖ := by
    change |@inner ℝ (ColoredStar d k) _ (scalarAdaptedBasis d k i)
      (D.empiricalWhiteStar n ω (by omega) selection s)| ≤ _
    have h := norm_inner_le_norm (𝕜 := ℝ) (scalarAdaptedBasis d k i) (D.empiricalWhiteStar n ω (by omega) selection s)
    rw [(scalarAdaptedBasis d k).orthonormal.norm_eq_one i, one_mul] at h
    simpa only [Real.norm_eq_abs] using h
  calc
    _ ≤ ∑ _ : ScalarCoordinate d k, ‖D.empiricalWhiteStar n ω (by omega) selection s‖ :=
      Finset.sum_le_sum (fun i _ => hi i)
    _ = (Fintype.card (ScalarCoordinate d k) : ℝ) * ‖D.empiricalWhiteStar n ω (by omega) selection s‖ := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_left hnorm (Nat.cast_nonneg _)

theorem HY_empiricalNormalizedSignal_bound {P : Measure Ω} [IsProbabilityMeasure P]
    {quantile : ∀ n, Fin (N n) → ℝ} (H : HYCoarseInput D P quantile)
    (hn : H.events.threshold ≤ n) (hgood : ω ∈ H.events.good n)
    {k : ℕ} (hd : 3 ≤ d) (selection : Fin k → Fin (N n)) (hinj : Function.Injective selection)
    (hE : ∀ a, |D.eigenvalue n ω (selection a)| < d)
    (hbulk : ∀ a, (D.eigenvalue n ω (selection a) / d) ^ 2 < 4 * ((d : ℝ) - 1) / (d : ℝ) ^ 2)
    (s : EmpiricalStarSample d (N n)) :
    coordinateL1 ((D.empiricalNormalizedSignal n ω (by omega) selection hinj hE).signal s) ≤
      (Fintype.card (ScalarCoordinate d k) : ℝ) *
        ((k : ℝ) * d * ((d : ℝ) + 1) * (H.events.constant * Real.log (N n) ^ H.logPower)) := by
  have hN : (1 : ℝ) ≤ N n := by exact_mod_cast D.size_pos n
  have hB : 0 ≤ H.events.constant * Real.log (N n) ^ H.logPower :=
    mul_nonneg H.events.constant_pos.le (pow_nonneg (Real.log_nonneg hN) _)
  apply D.empiricalNormalizedSignal_bound n ω hd selection hinj hE hbulk _ hB
  intro a v
  apply H.delocalization n hn ω hgood _ (D.eigenvalue n ω (selection a)) ?_ ?_ v
  · simpa only [pow_two, ite_true] using D.orthonormal n ω (selection a) (selection a)
  · exact D.eigen_equation n ω (selection a)

end GeneralizedBulk.External.RegularSpectralData
