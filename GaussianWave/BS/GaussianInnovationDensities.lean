import GaussianWave.BS.ForestLayerIndependence
import GaussianWave.BS.GaussianIntrinsicDensity
import GaussianWave.BS.ConditionalEntropy

/-!
# Positive finite-entropy densities for the actual Gaussian innovations
-/
noncomputable section
open MeasureTheory
namespace GaussianWave.BS

def FiniteEntropyDensity.toPositive {I : Type*} [Fintype I]
    {μ : Measure (I → ℝ)} (f : FiniteEntropyDensity μ)
    (hf : ∀ x, 0 < f.density x) : PositiveEntropyDensity (volume : Measure (I → ℝ)) where
  density := f.density
  measurable := f.measurable
  positive := hf
  integrable := f.integrable
  integral_one := f.integral_eq_one
  integrable_log := f.integrable_log

@[simp] theorem FiniteEntropyDensity.toPositive_law {I : Type*} [Fintype I]
    {μ : Measure (I → ℝ)} (f : FiniteEntropyDensity μ) (hf : ∀ x, 0 < f.density x) :
    (f.toPositive hf).law = μ := f.measure_eq.symm

@[simp] theorem FiniteEntropyDensity.toPositive_entropy {I : Type*} [Fintype I]
    {μ : Measure (I → ℝ)} (f : FiniteEntropyDensity μ) (hf : ∀ x, 0 < f.density x) :
    (f.toPositive hf).entropy = f.entropy := rfl

theorem standardVectorEntropyDensity_positive (I : Type*) [Fintype I] (x : I → ℝ) :
    0 < (standardVectorEntropyDensity I).density x :=
  heatKernel_pos (by norm_num : (0 : ℝ) < 1 / 2) x

theorem FiniteEntropyDensity.linearImage_positive {I : Type*} [Fintype I] [DecidableEq I]
    {μ : Measure (I → ℝ)} [IsProbabilityMeasure μ]
    (f : FiniteEntropyDensity μ) (hf : ∀ x, 0 < f.density x)
    (M : Matrix I I ℝ) (hM : M.det ≠ 0) (x : I → ℝ) :
    0 < (f.linearImage M hM).density x := by
  change 0 < |M.det|⁻¹ * f.density (M⁻¹.mulVec x)
  exact mul_pos (inv_pos.mpr (abs_pos.mpr hM)) (hf _)

theorem linearImageGaussianEntropyDensity_positive {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] (L : Matrix I J ℝ)
    (hL : Function.Surjective L.mulVec) (x : I → ℝ) :
    0 < (linearImageGaussianEntropyDensity L hL).density x :=
  (standardVectorEntropyDensity I).linearImage_positive
    (standardVectorEntropyDensity_positive I) _
    (posDef_sqrt_det_ne_zero _ (rowGram_posDef_of_surjective L hL)) x

def linearImageGaussianPositiveDensity {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] (L : Matrix I J ℝ)
    (hL : Function.Surjective L.mulVec) : PositiveEntropyDensity (volume : Measure (I → ℝ)) :=
  (linearImageGaussianEntropyDensity L hL).toPositive
    (linearImageGaussianEntropyDensity_positive L hL)

@[simp] theorem linearImageGaussianPositiveDensity_law {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] (L : Matrix I J ℝ)
    (hL : Function.Surjective L.mulVec) :
    (linearImageGaussianPositiveDensity L hL).law = linearImageGaussian L :=
  FiniteEntropyDensity.toPositive_law _ _

theorem rawSiblingFactor_surjective (m : ℕ) (scale : ℝ) (hs : scale ≠ 0) :
    Function.Surjective (rawSiblingFactor m scale).mulVec := by
  intro y
  refine ⟨Fin.cases 0 (fun i => y i / scale), ?_⟩
  ext i
  rw [rawSiblingFactor_mulVec]
  simp only [Fin.cases_succ, Fin.cases_zero, sub_zero]
  exact mul_div_cancel₀ _ hs

theorem independentBlockFactor_surjective {A I J : Type*} [Fintype A] [Fintype J]
    [DecidableEq A] (L : Matrix I J ℝ) (hL : Function.Surjective L.mulVec) :
    Function.Surjective (independentBlockFactor (A := A) L).mulVec := by
  intro y
  choose z hz using fun a : A => hL (fun i => y (a, i))
  refine ⟨fun aj => z aj.1 aj.2, ?_⟩
  ext ⟨a, i⟩
  rw [independentBlockFactor_mulVec]
  exact congrFun (hz a) i

def newBranchGaussianPositiveDensity (m k : ℕ) (scale : ℝ) (hs : scale ≠ 0) :
    PositiveEntropyDensity (volume : Measure (NewBranchInnovation m k → ℝ)) :=
  linearImageGaussianPositiveDensity
    (independentBlockFactor (A := BranchLeaf (m + 1) k) (rawSiblingFactor m scale))
    (independentBlockFactor_surjective _ (rawSiblingFactor_surjective m scale hs))

@[simp] theorem newBranchGaussianPositiveDensity_law (m k : ℕ) (scale : ℝ) (hs : scale ≠ 0) :
    (newBranchGaussianPositiveDensity m k scale hs).law = newBranchGaussianLaw m k scale := by
  rw [newBranchGaussianPositiveDensity, linearImageGaussianPositiveDensity_law,
    independentBlockFactor_gaussian_product]
  rfl

theorem forestGaussianInnovation_surjective {A : Type*} [Fintype A]
    (m k : ℕ) (scale : ℝ) (hs : scale ≠ 0) (R : Matrix A A ℝ)
    (hR : Function.Surjective R.mulVec) :
    Function.Surjective (forestGaussianInnovation m k scale R) := by
  intro x
  obtain ⟨root, hroot⟩ := hR (fun a => x (Sum.inl a))
  refine ⟨Sum.elim root (fun aj => branchNoiseRightInverse m k scale
    (fun i => x (Sum.inr (aj.1, i))) aj.2), ?_⟩
  ext j
  cases j with
  | inl a => exact congrFun hroot a
  | inr aj => exact congrFun (branchNoiseInnovation_rightInverse m k scale hs
      (fun i => x (Sum.inr (aj.1, i)))) aj.2

def forestGaussianInnovationMatrix {A : Type*} [Fintype A] [DecidableEq A]
    (m k : ℕ) (scale : ℝ) (R : Matrix A A ℝ) :=
  LinearMap.toMatrix' (forestGaussianInnovation m k scale R)

theorem forestGaussianInnovationMatrix_mulVec {A : Type*} [Fintype A] [DecidableEq A]
    (m k : ℕ) (scale : ℝ) (R : Matrix A A ℝ) :
    (forestGaussianInnovationMatrix m k scale R).mulVec =
      forestGaussianInnovation m k scale R :=
  congrArg DFunLike.coe (Matrix.toLin'_toMatrix' (forestGaussianInnovation m k scale R))

theorem forestGaussianInnovationLaw_eq_linearImage {A : Type*} [Fintype A] [DecidableEq A]
    (m k : ℕ) (scale : ℝ) (R : Matrix A A ℝ) :
    forestGaussianInnovationLaw m k scale R =
      linearImageGaussian (forestGaussianInnovationMatrix m k scale R) := by
  unfold linearImageGaussian forestGaussianInnovationLaw
  rw [forestGaussianInnovationMatrix_mulVec]

def forestGaussianPositiveDensity {A : Type*} [Fintype A] [DecidableEq A]
    (m k : ℕ) (scale : ℝ) (hs : scale ≠ 0) (R : Matrix A A ℝ)
    (hR : Function.Surjective R.mulVec) :
    PositiveEntropyDensity (volume : Measure (ForestInnovation A m k → ℝ)) :=
  linearImageGaussianPositiveDensity (forestGaussianInnovationMatrix m k scale R)
    (by rw [forestGaussianInnovationMatrix_mulVec]
        exact forestGaussianInnovation_surjective m k scale hs R hR)

@[simp] theorem forestGaussianPositiveDensity_law {A : Type*} [Fintype A] [DecidableEq A]
    (m k : ℕ) (scale : ℝ) (hs : scale ≠ 0) (R : Matrix A A ℝ)
    (hR : Function.Surjective R.mulVec) :
    (forestGaussianPositiveDensity m k scale hs R hR).law =
      forestGaussianInnovationLaw m k scale R := by
  rw [forestGaussianPositiveDensity, linearImageGaussianPositiveDensity_law,
    forestGaussianInnovationLaw_eq_linearImage]

end GaussianWave.BS
