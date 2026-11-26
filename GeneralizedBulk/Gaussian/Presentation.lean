import GeneralizedBulk.Gaussian.ParticleKernels

/-!
# Fixed-index particle presentations

A presentation records locations with their multiplicities as actual unit
Dirac masses. A fixed label type lets a random scalar state share one independent
Gaussian mark space. No choice of a state-dependent enumeration is asserted to
be measurable.
-/
noncomputable section
open MeasureTheory BourgadeHuang
open scoped Topology BigOperators

namespace GeneralizedBulk.Gaussian

structure ParticlePresentation (s : AnchoredCountingState) (ι : Type*) where
  location : ι → ℝ
  measure_eq : s.val.1.measure = Measure.sum (fun i => Measure.dirac (location i))

namespace ParticlePresentation
variable {ι : Type*} [Countable ι] {s : AnchoredCountingState}

theorem hasSum_observable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    (p : ParticlePresentation s ι) {f : ℝ → V} (hf : Integrable f s.val.1.measure) :
    HasSum (fun i => f (p.location i)) (∫ x, f x ∂s.val.1.measure) := by
  have hi : Integrable f (Measure.sum (fun i => Measure.dirac (p.location i))) := by
    rwa [← p.measure_eq]
  simpa only [integral_dirac, ← p.measure_eq] using hasSum_integral_measure hi

theorem summable_weight (p : ParticlePresentation s ι) :
    Summable (fun i => nevanlinnaWeight (p.location i)) :=
  (p.hasSum_observable s.integrable_weight).summable

theorem summable_coefficient_sq (p : ParticlePresentation s ι) (v : ℂ × Bool) :
    Summable (fun i => ‖particleCoefficient (p.location i) v‖ ^ 2) :=
  (p.hasSum_observable (integrable_particleCoefficient_sq s v)).summable

theorem hasSum_kernel (p : ParticlePresentation s ι) (v u : ℂ × Bool) :
    HasSum (fun i => particleCoefficient (p.location i) v * particleCoefficient (p.location i) u)
      (particleKernel s v u) :=
  p.hasSum_observable (integrable_particleCoefficient_product s v u)

/-- The existing global particle labels always provide a concrete presentation,
including a separate label for each occurrence of a multiple atom. -/
def canonical (s : AnchoredCountingState) : ParticlePresentation s s.val.1.ParticleLabels :=
  ⟨s.val.1.particleLocation, s.val.1.measure_eq_sum_particles⟩

end ParticlePresentation

abbrev PresentedState (ι : Type*) :=
  {p : AnchoredCountingState × (ι → ℝ) //
    p.1.val.1.measure = Measure.sum (fun i => Measure.dirac (p.2 i))}

namespace PresentedState
variable {ι : Type*}

def scalar (s : PresentedState ι) : AnchoredCountingState := s.val.1
def location (s : PresentedState ι) : ι → ℝ := s.val.2
def presentation (s : PresentedState ι) : ParticlePresentation s.scalar ι := ⟨s.location, s.property⟩

theorem measurable_scalar : Measurable (scalar (ι := ι)) :=
  measurable_fst.comp measurable_subtype_coe

theorem measurable_location (i : ι) : Measurable (fun s : PresentedState ι => s.location i) :=
  (measurable_pi_apply i).comp (measurable_snd.comp measurable_subtype_coe)

end PresentedState
end GeneralizedBulk.Gaussian
