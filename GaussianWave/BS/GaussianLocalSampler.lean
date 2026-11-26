import Mathlib
import GaussianWave.GaussianContinuity
import GaussianWave.BS.FiniteSupportAdjacency

/-! Actual Gaussian local samplers on an arbitrary label set. Every row
has finite support; finite-window laws are literal finite linear images of
independent standard Gaussian labels. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical
namespace GaussianWave.BS

/-- The actual independent Gaussian label field, for any vertex set. -/
def gaussianLabelLaw (V : Type*) : Measure (V → ℝ) :=
  Measure.infinitePi (fun _ : V => gaussianReal 0 1)

instance gaussianLabelLaw_isProbability (V : Type*) : IsProbabilityMeasure (gaussianLabelLaw V) := by
  unfold gaussianLabelLaw
  infer_instance

def finiteSupportGaussianSample {V I : Type*} (a : I → V →₀ ℝ) (ξ : V → ℝ) (i : I) : ℝ :=
  (a i).sum (fun v c => c*ξ v)

theorem measurable_finiteSupportGaussianSample {V I : Type*} (a : I → V →₀ ℝ) :
    Measurable (finiteSupportGaussianSample a) := by
  apply measurable_pi_lambda
  intro i
  unfold finiteSupportGaussianSample Finsupp.sum
  exact Finset.measurable_sum _ (fun v hv => (measurable_pi_apply v).const_mul _)

/-- The union of the actual supports of a finite collection of local rules. -/
def finiteSupportGaussianUnion {V I : Type*} [Fintype I] (a : I → V →₀ ℝ) : Finset V :=
  Finset.univ.biUnion (fun i => (a i).support)

def finiteSupportGaussianMatrix {V I : Type*} [Fintype I] (a : I → V →₀ ℝ) :
    Matrix I (finiteSupportGaussianUnion a) ℝ := fun i v => a i v

theorem finiteSupportGaussianSample_eq_matrix {V I : Type*} [Fintype I]
    (a : I → V →₀ ℝ) (ξ : V → ℝ) :
    finiteSupportGaussianSample a ξ =
      (finiteSupportGaussianMatrix a).mulVec ((finiteSupportGaussianUnion a).restrict ξ) := by
  ext i
  change (a i).sum (fun v c => c*ξ v) =
    ∑ v : finiteSupportGaussianUnion a, a i v.val * ξ v.val
  rw [Finset.sum_coe_sort (finiteSupportGaussianUnion a) (fun v => a i v * ξ v)]
  apply Finsupp.sum_of_support_subset
  · intro v hv
    exact Finset.mem_biUnion.2 ⟨i,Finset.mem_univ _,hv⟩
  · intro v hv
    simp

/-- The actual sampled finite-window law, from the constructed independent
infinite label field. -/
def finiteSupportGaussianLaw {V I : Type*} (a : I → V →₀ ℝ) : Measure (I → ℝ) :=
  Measure.map (finiteSupportGaussianSample a) (gaussianLabelLaw V)

instance finiteSupportGaussianLaw_isProbability {V I : Type*} (a : I → V →₀ ℝ) :
    IsProbabilityMeasure (finiteSupportGaussianLaw a) :=
  isProbabilityMeasure_map (measurable_finiteSupportGaussianSample a).aemeasurable

/-- Gaussianity of every sampled finite window is derived from its literal
finite label restriction, rather than supplied as a premise. -/
theorem finiteSupportGaussianLaw_eq_linearImage {V I : Type*} [Fintype I]
    (a : I → V →₀ ℝ) :
    finiteSupportGaussianLaw a = linearImageGaussian (finiteSupportGaussianMatrix a) := by
  have he : finiteSupportGaussianSample a =
      (finiteSupportGaussianMatrix a).mulVec ∘ (finiteSupportGaussianUnion a).restrict := by
    funext ξ
    exact finiteSupportGaussianSample_eq_matrix a ξ
  unfold finiteSupportGaussianLaw
  rw [he, ← Measure.map_map (measurable_finiteMatrixAction _) (measurable_pi_lambda _ (fun v => measurable_pi_apply v.val))]
  change Measure.map _ (Measure.map _ (Measure.infinitePi (fun _ : V => gaussianReal 0 1))) = _
  rw [Measure.infinitePi_map_restrict]
  rfl

theorem finiteSupportGaussianLaw_gaussian {V I : Type*} [Fintype I]
    (a : I → V →₀ ℝ) : HasGaussianCovariance (finiteSupportGaussianLaw a)
      (finiteSupportGaussianMatrix a*(finiteSupportGaussianMatrix a).transpose) := by
  rw [finiteSupportGaussianLaw_eq_linearImage]
  exact linearImageGaussian_characteristic _


/-- Its matrix Gram entry is exactly the finite coefficient pairing, so
finite-window choices of a common label support introduce no new covariance. -/
theorem finiteSupportGaussianMatrix_gram {V I : Type*} [Fintype I]
    (a : I → V →₀ ℝ) (i j : I) :
    (finiteSupportGaussianMatrix a*(finiteSupportGaussianMatrix a).transpose) i j =
      finsuppPairing (a i) (a j) := by
  change (∑ v : finiteSupportGaussianUnion a, a i v.val*a j v.val)=_
  rw [Finset.sum_coe_sort (finiteSupportGaussianUnion a) (fun v => a i v*a j v),finsuppPairing_apply]
  symm
  apply Finsupp.sum_of_support_subset
  · intro v hv
    exact Finset.mem_biUnion.2 ⟨i,Finset.mem_univ _,hv⟩
  · simp

end GaussianWave.BS
