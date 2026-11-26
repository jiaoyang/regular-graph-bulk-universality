import GeneralizedBulk.Gaussian.StarLaw
import GeneralizedBulk.Gaussian.FiniteMarks
import GeneralizedBulk.Gaussian.CovarianceTransport
import GeneralizedBulk.Graph.StarGaussianConvergence

/-!
# Two independent star edges give iid four-endpoint Gaussian marks

The first and second star samples are independent. Their root and one ordered
neighbor form two correlated Gaussian pairs in each eigenchannel. Exact
covariance transport identifies the full law with the finite product of the
previously constructed endpoint mark law.
-/
noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology Classical

namespace GeneralizedBulk.Gaussian
open External.RegularSpectralData

def selectionMatrix {ι κ : Type*} (source : κ → ι) : Matrix κ ι ℝ :=
  fun i a => if a = source i then 1 else 0

theorem selectionMatrix_mulVec {ι κ : Type*} [Fintype ι] (source : κ → ι) (x : ι → ℝ) (i : κ) :
    (selectionMatrix source).mulVec x i = x (source i) := by
  simp [selectionMatrix, Matrix.mulVec, dotProduct, ite_mul]

theorem selectionMatrix_conjugate {ι κ : Type*} [Fintype ι]
    (source : κ → ι) (C : Matrix ι ι ℝ) :
    selectionMatrix source * C * (selectionMatrix source).transpose =
      fun i j => C (source i) (source j) := by
  ext i j
  simp [selectionMatrix, Matrix.mul_apply, Matrix.transpose_apply, ite_mul, mul_ite]

def starEndpointSource {d k : ℕ} (leaf : Fin d) (ai : Fin k × Fin 4) :
    Sum (Fin k × Fin (d + 1)) (Fin k × Fin (d + 1)) :=
  ![Sum.inl (ai.1, 0), Sum.inl (ai.1, leaf.succ),
    Sum.inr (ai.1, 0), Sum.inr (ai.1, leaf.succ)] ai.2

def starEndpointRestriction {d k : ℕ} (leaf : Fin d) :
    Matrix (Fin k × Fin 4) (Sum (Fin k × Fin (d + 1)) (Fin k × Fin (d + 1))) ℝ :=
  selectionMatrix (starEndpointSource leaf)

theorem starEndpointRestriction_covariance (d k : ℕ) (E : ℝ) (leaf : Fin d) :
    starEndpointRestriction (k := k) leaf *
      sumCovariance (jointStarCovariance d k E) (jointStarCovariance d k E) *
        (starEndpointRestriction leaf).transpose = finiteMarkCovariance (E / d) k := by
  rw [starEndpointRestriction, selectionMatrix_conjugate]
  ext ai bj
  rcases ai with ⟨a, i⟩
  rcases bj with ⟨b, j⟩
  fin_cases i <;> fin_cases j <;>
    simp [starEndpointSource, sumCovariance, jointStarCovariance, finiteMarkCovariance,
      starWaveCovariance, covarianceMatrix_eq, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.vecHead, Matrix.vecTail]

def twoStarEndpointLaw (d k : ℕ) (hd : 2 ≤ d) (E : ℝ) (leaf : Fin d) :
    Measure ((Fin k × Fin 4) → ℝ) :=
  Measure.map (fun x => (starEndpointRestriction (k := k) leaf).mulVec x)
    (vectorProductLaw (jointStarGaussianLaw d k hd E) (jointStarGaussianLaw d k hd E))

instance (d k : ℕ) (hd : 2 ≤ d) (E : ℝ) (leaf : Fin d) :
    IsProbabilityMeasure (twoStarEndpointLaw d k hd E leaf) := by
  unfold twoStarEndpointLaw
  exact MeasureTheory.isProbabilityMeasure_map
    (measurable_finiteMatrixAction (starEndpointRestriction leaf)).aemeasurable

/-- The entire finite eigenchannel family consists of independent actual
four-endpoint marks, with root/neighbor correlation `p=E/d`. -/
theorem twoStarEndpointLaw_eq_finiteMarkLaw (d k : ℕ) (hd : 2 ≤ d) (E : ℝ)
    (hE : |E| < d) (leaf : Fin d) :
    twoStarEndpointLaw d k hd E leaf = finiteMarkLaw (E / d) k := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hp : |E / (d : ℝ)| < 1 := by
    rw [abs_div, abs_of_pos hdR, div_lt_one hdR]
    exact hE
  have hstar : GaussianCharacteristic (jointStarGaussianLaw d k hd E) (jointStarCovariance d k E) :=
    jointStarGaussianLaw_characteristic d k hd E hE
  have he := (hstar.vectorProductLaw hstar).linearImage (starEndpointRestriction (k := k) leaf)
  rw [starEndpointRestriction_covariance] at he
  apply measure_eq_of_linear_characteristic
  intro t
  exact (he t).trans (finiteMarkLaw_characteristic (E / d) hp k t).symm

theorem continuous_finiteMatrixAction {ι κ : Type*} [Fintype ι]
    (R : Matrix κ ι ℝ) : Continuous (fun x : ι → ℝ => R.mulVec x) := by
  apply continuous_pi
  intro i
  exact continuous_finset_sum _ (fun j hj => continuous_const.mul (continuous_apply j))

theorem weakLaw_linearImage {ι κ : Type*} [Fintype ι] [Fintype κ]
    (μ : ℕ → Measure (ι → ℝ)) (ν : Measure (ι → ℝ)) (R : Matrix κ ι ℝ)
    (hweak : External.WeakLawConverges μ ν) :
    External.WeakLawConverges (fun n => Measure.map (fun x => R.mulVec x) (μ n))
      (Measure.map (fun x => R.mulVec x) ν) := by
  intro F
  have h := hweak (F.compContinuous ⟨_, continuous_finiteMatrixAction R⟩)
  simp only [integral_map (measurable_finiteMatrixAction R).aemeasurable
    F.continuous.aestronglyMeasurable]
  exact h

end GeneralizedBulk.Gaussian

namespace GeneralizedBulk.External.RegularSpectralData

variable {d : ℕ} {N : ℕ → ℕ} {Ω : Type*} [MeasurableSpace Ω]
variable (D : RegularSpectralData d N Ω)

def twoEdgeLaw {k : ℕ} (n : ℕ) (ω : Ω) (a : Fin k → Fin (N n)) (leaf : Fin d) :
    Measure ((Fin k × Fin 4) → ℝ) :=
  let μ := D.starLaw n ω (fun i => D.eigenvector n ω (a i))
  Measure.map (fun x => (Gaussian.starEndpointRestriction (k := k) leaf).mulVec x)
    (Gaussian.vectorProductLaw μ μ)

/-- Two independent sampled edges have actual iid four-endpoint Gaussian
marks across every finite collection of nearby eigenchannels. -/
theorem BS_twoEdgeLaw_weakConverges {k : ℕ} (hk : 0 < k)
    (P : Measure Ω) [IsProbabilityMeasure P] (K : Set ℝ)
    (BS : BSQualitativeInput D P K) (ω : ℕ → Ω)
    (hgood : ∀ᶠ n in atTop, ω n ∈ BS.good k n)
    (a : ∀ n, Fin k → Fin (N n)) (hinj : ∀ n, Function.Injective (a n))
    (hnonconstant : ∀ n i, a n i ≠ ⟨0, D.size_pos n⟩)
    (energy : ℕ → ℝ) (hbulk : ∀ᶠ n in atTop, energy n ∈ K)
    (E : ℝ) (hE : E ∈ K) (henergy : Tendsto energy atTop (𝓝 E))
    (hEig : ∀ i, Tendsto (fun n => D.eigenvalue n (ω n) (a n i)) atTop (𝓝 E))
    (M : ℝ) (hM : ∀ n, (∫ x, ‖x‖ ^ 4 ∂D.starLaw n (ω n)
      (fun i => D.eigenvector n (ω n) (a n i))) ≤ M) (leaf : Fin d) :
    WeakLawConverges (fun n => D.twoEdgeLaw n (ω n) (a n) leaf)
      (Gaussian.finiteMarkLaw (E / d) k) := by
  have hdegree : 2 ≤ d := by have h := BS.degree_ge_three; omega
  let μ := fun n => D.starLaw n (ω n) (fun i => D.eigenvector n (ω n) (a n i))
  let target := Gaussian.jointStarGaussianLaw d k hdegree E
  letI : ∀ n, IsProbabilityMeasure (μ n) := fun n => D.starLaw_isProbability n (ω n) _
  have hw : WeakLawConverges μ target := D.BS_starLaw_weakConverges hk P K BS ω hgood a hinj
    hnonconstant energy hbulk E hE henergy hEig M hM
  have hi (n : ℕ) : Integrable (fun x => ‖x‖ ^ 4) (μ n) :=
    D.integrable_starLaw n (ω n) _ (fun x => ‖x‖ ^ 4)
  have hp := Gaussian.vectorProductLaw_weakConverges μ target μ target hw hw hi hi M M hM hM
  have hm := Gaussian.weakLaw_linearImage _ _ (Gaussian.starEndpointRestriction (k := k) leaf) hp
  change WeakLawConverges (fun n => D.twoEdgeLaw n (ω n) (a n) leaf)
    (Gaussian.twoStarEndpointLaw d k hdegree E leaf) at hm
  rw [Gaussian.twoStarEndpointLaw_eq_finiteMarkLaw d k hdegree E
    (D.BS_bulk_abs_lt_degree P K BS E hE) leaf] at hm
  exact hm

end GeneralizedBulk.External.RegularSpectralData
