import GeneralizedBulk.Graph.WholeQuantizedSampling
import GeneralizedBulk.Entropy.SelectedGaussianBounds

/-! Computed nonsingular Gaussian density factors for the actual whole,
star, and edge observations of one correlated Gaussian noise vector. -/
noncomputable section
open MeasureTheory
open scoped BigOperators Classical

namespace GeneralizedBulk.Graph.Configuration
open ColorProfiles Entropy GeneralizedBulk.Gaussian GeneralizedBulk.Covariance

variable {k N d : ℕ} {J : Type*} [Fintype J]
variable (A : Matrix (Fin k × Fin N) J ℝ) (lo : ℝ) (hlo : 0 < lo)
  (hbound : ∀ x : Fin k × Fin N → ℝ,lo*(∑ i,x i^2) ≤ dotProduct x ((A*A.transpose).mulVec x))

def wholeNoiseFactor : Matrix (Fin (k*N)) (Fin (k*N)) ℝ :=
  selectedGaussianFactor A (flatSelection (id : Fin N → Fin N))
    (flatSelection_injective id Function.injective_id) lo hlo hbound

def starNoiseFactor (G : RegularGraph N d) (z : Fin N × Equiv.Perm (Fin d)) :
    Matrix (Fin (k*(d+1))) (Fin (k*(d+1))) ℝ :=
  selectedGaussianFactor A (flatSelection (starVertexSelection G z))
    (flatSelection_injective _ (starVertexSelection_injective G z)) lo hlo hbound

def edgeNoiseFactor (G : RegularGraph N d) (z : Fin N × Fin d) : Matrix (Fin (k*2)) (Fin (k*2)) ℝ :=
  selectedGaussianFactor A (flatSelection (edgeVertexSelection G z))
    (flatSelection_injective _ (edgeVertexSelection_injective G z)) lo hlo hbound

theorem wholeNoiseFactor_det_ne_zero : (wholeNoiseFactor A lo hlo hbound).det ≠ 0 :=
  selectedGaussianFactor_det_ne_zero _ _ _ _ _ _

theorem starNoiseFactor_det_ne_zero (G : RegularGraph N d) (z : Fin N × Equiv.Perm (Fin d)) :
    (starNoiseFactor A lo hlo hbound G z).det ≠ 0 := selectedGaussianFactor_det_ne_zero _ _ _ _ _ _

theorem edgeNoiseFactor_det_ne_zero (G : RegularGraph N d) (z : Fin N × Fin d) :
    (edgeNoiseFactor A lo hlo hbound G z).det ≠ 0 := selectedGaussianFactor_det_ne_zero _ _ _ _ _ _

theorem realWholeLaw_gaussian (mean : Fin k × Fin N → ℝ) :
    realWholeLaw (linearImageGaussian A) mean =
      affineGaussian (mean ∘ flatSelection (id : Fin N → Fin N)) (wholeNoiseFactor A lo hlo hbound) := by
  have h := projected_shifted_gaussian_law A mean (coordinateSelection (flatSelection (id : Fin N → Fin N)))
    (wholeNoiseFactor A lo hlo hbound) (selectedGaussianFactor_gram A _ _ lo hlo hbound)
  simpa only [coordinateSelection_mulVec] using h

theorem realStarSampleLaw_gaussian (G : RegularGraph N d) (mean : Fin k × Fin N → ℝ) :
    realStarSampleLaw (linearImageGaussian A) G mean =
      gaussianMixtureLaw (uniformSampleWeight (Fin N × Equiv.Perm (Fin d)))
        (fun z => mean ∘ flatSelection (starVertexSelection G z)) (starNoiseFactor A lo hlo hbound G) :=
  finiteSampleLaw_selected_gaussian A mean _ _
    (fun z => flatSelection_injective _ (starVertexSelection_injective G z)) lo hlo hbound

theorem realEdgeSampleLaw_gaussian (G : RegularGraph N d) (mean : Fin k × Fin N → ℝ) :
    realEdgeSampleLaw (linearImageGaussian A) G mean =
      gaussianMixtureLaw (uniformSampleWeight (Fin N × Fin d))
        (fun z => mean ∘ flatSelection (edgeVertexSelection G z)) (edgeNoiseFactor A lo hlo hbound G) :=
  finiteSampleLaw_selected_gaussian A mean _ _
    (fun z => flatSelection_injective _ (edgeVertexSelection_injective G z)) lo hlo hbound

theorem wholeNoiseFactor_coordinateVariance (i : Fin (k*N)) :
    coordinateVariance (wholeNoiseFactor A lo hlo hbound) i =
      coordinateVariance A (flatSelection (id : Fin N → Fin N) i) :=
  selectedGaussianFactor_coordinateVariance _ _ _ _ _ _ i

theorem starNoiseFactor_coordinateVariance (G : RegularGraph N d) (z : Fin N × Equiv.Perm (Fin d))
    (i : Fin (k*(d+1))) : coordinateVariance (starNoiseFactor A lo hlo hbound G z) i =
      coordinateVariance A (flatSelection (starVertexSelection G z) i) :=
  selectedGaussianFactor_coordinateVariance _ _ _ _ _ _ i

theorem edgeNoiseFactor_coordinateVariance (G : RegularGraph N d) (z : Fin N × Fin d) (i : Fin (k*2)) :
    coordinateVariance (edgeNoiseFactor A lo hlo hbound G z) i =
      coordinateVariance A (flatSelection (edgeVertexSelection G z) i) :=
  selectedGaussianFactor_coordinateVariance _ _ _ _ _ _ i

theorem starNoiseFactor_lower (G : RegularGraph N d) (z : Fin N × Equiv.Perm (Fin d))
    (x : Fin (k*(d+1)) → ℝ) : lo*(∑ i,x i^2) ≤
      dotProduct x ((starNoiseFactor A lo hlo hbound G z*(starNoiseFactor A lo hlo hbound G z).transpose).mulVec x) :=
  selectedGaussianFactor_lower _ _ _ _ _ _ x

end GeneralizedBulk.Graph.Configuration
