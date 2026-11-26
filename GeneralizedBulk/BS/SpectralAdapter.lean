import GeneralizedBulk.ExternalInputs
import GaussianWave.Covariance
import GaussianWave.Foundation

/-! Exact finite-model adapters between the two merged libraries. The spectral
data, empirical star laws, and centered Gaussianity convention agree literally. -/
noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace GaussianWave.SiblingBulk

variable {d : ℕ} {N : ℕ → ℕ} {Ω : Type*} [MeasurableSpace Ω]

/-- Select any injective family of actual eigenvectors from the sibling
spectral model.  This requires no BS or HY hypothesis. -/
def selectedEigenData (D : GeneralizedBulk.External.RegularSpectralData d N Ω)
    (n : ℕ) (ω : Ω) {k : ℕ} (selection : Fin k → Fin (N n))
    (hinj : Function.Injective selection) : RegularEigenData d (N n) k where
  size_pos := D.size_pos n
  adjacency := D.adjacency n ω
  eigenvalue := fun a => D.eigenvalue n ω (selection a)
  eigenvector := fun a => D.eigenvector n ω (selection a)
  neighbor := D.neighbor n ω
  symmetric := D.symmetric n ω
  diagonal_zero := D.diagonal_zero n ω
  entry_zero_one := D.entry_zero_one n ω
  regular := D.regular n ω
  neighbor_injective := D.neighbor_injective n ω
  neighbor_exact := D.neighbor_exact n ω
  orthonormal := by
    intro a b
    rw [D.orthonormal n ω]
    simp only [hinj.eq_iff]
  eigen_equation := fun a => D.eigen_equation n ω (selection a)

/-- The two projects use the literal same uniform-root, randomly ordered,
sqrt-N-scaled empirical star law, even for arbitrary vector families. -/
theorem starLaw_eq (D : GeneralizedBulk.External.RegularSpectralData d N Ω)
    (n : ℕ) (ω : Ω) {k l : ℕ} (selection : Fin k → Fin (N n))
    (hinj : Function.Injective selection) (q : Fin l → Fin (N n) → ℝ) :
    (selectedEigenData D n ω selection hinj).starLaw q = D.starLaw n ω q := rfl

/-- No change of Gaussianity convention is needed at the project boundary. -/
theorem centeredGaussianLaw_iff {I : Type*} [Fintype I] (μ : Measure (I → ℝ)) :
    GaussianWave.CenteredGaussianLaw μ ↔ GeneralizedBulk.External.CenteredGaussianLaw μ := Iff.rfl

end GaussianWave.SiblingBulk
