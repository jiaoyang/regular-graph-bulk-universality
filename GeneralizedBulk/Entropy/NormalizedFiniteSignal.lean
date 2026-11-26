import GeneralizedBulk.Entropy.FiniteSignalMoments
import GeneralizedBulk.Entropy.UniformSmoothing

/-! Exact finite signal data used by the constructed smoothing estimates. -/
noncomputable section
open MeasureTheory
open scoped BigOperators

namespace GeneralizedBulk.Entropy.Mehler
open GeneralizedBulk.Entropy.Hermite

/-- This records only finite weights, signal values, and exact moments.
Every smoothing density, analytic estimate, and observation law is then
constructed by the theorems below. -/
structure NormalizedFiniteSignal (I S : Type*) [Fintype I] [DecidableEq I] [Fintype S] where
  weight : S → ℝ
  signal : S → I → ℝ
  nonneg : ∀ s, 0 ≤ weight s
  total : ∑ s, weight s = 1
  mean : ∀ i, ∑ s, weight s * signal s i = 0
  covariance : ∀ i j, ∑ s, weight s * signal s i * signal s j = if i = j then 1 else 0

namespace NormalizedFiniteSignal
variable {I S : Type*} [Fintype I] [DecidableEq I] [Fintype S]
variable (D : NormalizedFiniteSignal I S)

def density (a : ℝ) : (I → ℝ) → ℝ := finiteMixtureKernel D.weight D.signal a

theorem density_nonneg (a : ℝ) (z : I → ℝ) : 0 ≤ D.density a z :=
  finiteMixtureKernel_nonneg D.weight D.signal D.nonneg a z

theorem density_continuous (a : ℝ) : Continuous (D.density a) :=
  continuous_finset_sum _ (fun s _ => continuous_const.mul (continuous_vectorKernel a (D.signal s)))

def rotate (O : Matrix I I ℝ) (hO : O * O.transpose = 1) : NormalizedFiniteSignal I S where
  weight := D.weight
  signal s := O.mulVec (D.signal s)
  nonneg := D.nonneg
  total := D.total
  mean := weighted_linear_mean D.weight D.signal D.mean O
  covariance := weighted_orthogonal_covariance D.weight D.signal D.covariance O hO

def restrict (observed : Finset I) : NormalizedFiniteSignal observed S where
  weight := D.weight
  signal s i := D.signal s i
  nonneg := D.nonneg
  total := D.total
  mean i := D.mean i
  covariance i j := by
    simpa only [Subtype.val_inj] using D.covariance i.val j.val

theorem restrict_coordinateL1_le (observed : Finset I) (s : S) :
    coordinateL1 ((D.restrict observed).signal s) ≤ coordinateL1 (D.signal s) := by
  unfold coordinateL1
  change (∑ i : observed, |D.signal s i.val|) ≤ ∑ i : I, |D.signal s i|
  rw [Finset.sum_coe_sort observed (fun i : I => |D.signal s i|)]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ observed)
    (fun _ _ _ => abs_nonneg _)

theorem rotate_coordinateL1_le (O : Matrix I I ℝ) (hO : O * O.transpose = 1) (s : S) :
    coordinateL1 ((D.rotate O hO).signal s) ≤ (Fintype.card I : ℝ) * coordinateL1 (D.signal s) :=
  coordinateL1_orthogonal_le O hO _

theorem density_integral (a : ℝ) (ha : 0 < 1 - a ^ 2) :
    (∫ z, D.density a z ∂standardGaussian I) = 1 :=
  integral_finiteMixtureKernel D.weight D.signal D.total a ha

theorem centered_memLp_three (B a : ℝ) (hB : 0 ≤ B) (ha : 0 ≤ a) (ha1 : a ≤ 1 / 2)
    (hsmall : a * B ≤ 1 / 2) (hsignal : ∀ s, coordinateL1 (D.signal s) ≤ B) :
    MemLp (fun z => D.density a z - 1) 3 (standardGaussian I) :=
  finiteMixture_centered_memLp_three D.weight D.signal D.nonneg D.total D.mean D.covariance
    B a hB ha ha1 hsmall hsignal

theorem density_memLp_two (B a : ℝ) (hB : 0 ≤ B) (ha : 0 ≤ a) (ha1 : a ≤ 1 / 2)
    (hsmall : a * B ≤ 1 / 2) (hsignal : ∀ s, coordinateL1 (D.signal s) ≤ B) :
    MemLp (D.density a) 2 (standardGaussian I) := by
  have hu := D.centered_memLp_three B a hB ha ha1 hsmall hsignal
  have hc : MemLp (fun _ : I → ℝ => (1 : ℝ)) 3 (standardGaussian I) := memLp_const 1
  have h := (hu.add hc).mono_exponent (by norm_num : (2 : ENNReal) ≤ 3)
  convert h using 1
  funext z
  simp only [Pi.add_apply, sub_add_cancel]

theorem entropy_quadratic_bound (B a : ℝ) (hB : 0 ≤ B) (ha : 0 ≤ a) (ha1 : a ≤ 1 / 2)
    (hsmall : a * B ≤ 1 / 2) (hsignal : ∀ s, coordinateL1 (D.signal s) ≤ B) :
    |relativeEntropy (standardGaussian I) (D.density a) -
      (1 / 2 : ℝ) * ∫ z, (D.density a z - 1) ^ 2 ∂standardGaussian I| ≤
      smoothingEntropyConstant I * (1 + B ^ 2) ^ 9 * a ^ 9 :=
  uniform_small_noise_entropy_bound D.weight D.signal D.nonneg D.total D.mean D.covariance
    B a hB ha ha1 hsmall hsignal

end NormalizedFiniteSignal
end GeneralizedBulk.Entropy.Mehler
