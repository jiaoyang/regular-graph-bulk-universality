import GaussianWave.BS.RelativeFiniteSSA
import GaussianWave.BS.GaussianInnovationDensities

/-! Positive finite-entropy witnesses for genuine finite independent
products, including the empty product. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace GaussianWave.BS
namespace PositiveEntropyDensity

def iid {Y : Type*} [MeasurableSpace Y] {my : Measure Y} [SigmaFinite my]
    (p : PositiveEntropyDensity my) (A : Type*) [Fintype A] :
    PositiveEntropyDensity (Measure.pi (fun _ : A => my)) := by
  let f : (A → Y) → ℝ := fun y => ∏ a, p.density (y a)
  have hm : Measurable f :=
    Finset.measurable_prod _ (fun a _ => p.measurable.comp (measurable_pi_apply a))
  have hp : ∀ y, 0 < f y := fun y => Finset.prod_pos (fun _ _ => p.positive _)
  have hi : Integrable f (Measure.pi (fun _ : A => my)) :=
    integrable_pi_product_real my (fun _ : A => p.density) (fun _ => p.integrable)
  have hone : (∫ y, f y ∂Measure.pi (fun _ : A => my)) = 1 := by
    rw [integral_pi_product_real my (fun _ : A => p.density)]
    simp only [p.integral_one, Finset.prod_const_one]
  refine ⟨f, hm, hp, hi, hone, ?_⟩
  have hlog : Integrable (fun y => Real.log (f y)) (Measure.pi (fun _ : A => p.law)) := by
    have hcoord (a : A) : Integrable (fun y : A → Y => Real.log (p.density (y a)))
        (Measure.pi (fun _ : A => p.law)) := by
      apply (integrable_map_measure p.measurable.log.aestronglyMeasurable
        (measurable_pi_apply a).aemeasurable).mp
      rw [probability_pi_eval]
      exact p.integrable_log_law
    have hs := integrable_finset_sum Finset.univ (fun a _ => hcoord a)
    apply hs.congr
    exact ae_of_all _ (fun y => (Real.log_prod Finset.univ
      (fun a => p.density (y a)) (fun a _ => (p.positive _).ne')).symm)
  rw [pi_positiveDensity_law my (fun _ : A => p)] at hlog
  exact (integrable_realDensity_iff (Measure.pi (fun _ : A => my)) f _ hm
    (fun y => (hp y).le)).mp hlog

@[simp] theorem iid_law {Y : Type*} [MeasurableSpace Y] {my : Measure Y} [SigmaFinite my]
    (p : PositiveEntropyDensity my) (A : Type*) [Fintype A] :
    (p.iid A).law = Measure.pi (fun _ : A => p.law) :=
  (pi_positiveDensity_law my (fun _ : A => p)).symm

end PositiveEntropyDensity

theorem finiteStrongSubadditivity_independentReference_zero
    {A Y Z : Type*} [Fintype A] [MeasurableSpace Y] [MeasurableSpace Z]
    (my : Measure Y) (mz : Measure Z) [SigmaFinite my] [SigmaFinite mz]
    (s : PositiveEntropyDensity mz) (q : PositiveEntropyDensity my) :
    (∑ _ : A, (s.prod q).entropy) - (Fintype.card A - 1 : ℝ) * s.entropy -
      (s.prod (q.iid A)).entropy = 0 := by
  apply finiteStrongSubadditivity_productReference_zero my mz
  rw [PositiveEntropyDensity.prod_law, PositiveEntropyDensity.iid_law]

end GaussianWave.BS
