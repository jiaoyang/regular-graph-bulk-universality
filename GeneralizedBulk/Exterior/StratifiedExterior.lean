import GeneralizedBulk.Gaussian.InfiniteStratum
import GeneralizedBulk.ConstructedCriterion

/-! The exterior state of the actual mass-stratified marking and its exact
reduction to the canonical Nat-marked switching criterion after normalization. -/
noncomputable section
open MeasureTheory BourgadeHuang
open scoped ENNReal
namespace GeneralizedBulk.Exterior
open Gaussian Counting Analysis
variable (ν : Measure AnchoredCountingState) [IsProbabilityMeasure ν]
variable (hm1 : Integrable (fun s : AnchoredCountingState => ‖s.val.2‖) ν)

def massExterior (parameters : Parameters) (z : MassMarkedSample ν) : ValueState :=
  gaussianExterior (massStratumLaw ν z.1 : Measure (MassState z.1.val))
    (stratumPresentation z.1.val) (measurable_stratumPresentation z.1.val)
    (massStratum_anchor_integrable ν hm1 z.1) parameters z.2

theorem measurable_massExterior (parameters : Parameters) :
    Measurable (massExterior ν hm1 parameters) := by
  apply measurable_sigma_of_sections
  intro i
  exact measurable_gaussianExterior (massStratumLaw ν i : Measure (MassState i.val))
    (stratumPresentation i.val) (measurable_stratumPresentation i.val)
    (massStratum_anchor_integrable ν hm1 i) parameters

theorem massExterior_infinite_branch
    (hmass : ∀ᵐ s ∂ν, s.val.1.measure Set.univ = ∞)
    (parameters : Parameters) (z : MassState none × (ℕ → Fin 4 → ℝ)) :
    massExterior ν hm1 parameters ⟨infiniteActive ν hmass,z⟩ =
      gaussianExterior (infiniteBranchLaw ν hmass : Measure (MassState none))
        (stratumPresentation none) (measurable_stratumPresentation none)
        (massStratum_anchor_integrable ν hm1 (infiniteActive ν hmass)) parameters z := rfl

theorem massExterior_law_eq_infinite_branch
    (hmass : ∀ᵐ s ∂ν, s.val.1.measure Set.univ = ∞) (parameters : Parameters) :
    Measure.map (massExterior ν hm1 parameters) (massMarkedLaw ν parameters) =
      Measure.map (gaussianExterior (infiniteBranchLaw ν hmass : Measure (MassState none))
        (stratumPresentation none) (measurable_stratumPresentation none)
        (massStratum_anchor_integrable ν hm1 (infiniteActive ν hmass)) parameters)
        ((infiniteBranchLaw ν hmass : Measure (MassState none)).prod
          (iidLaw (markLaw parameters.p) ℕ)) :=
  massMarkedLaw_map_infinite_branch ν hmass parameters _ (measurable_massExterior ν hm1 parameters)

/-- Once the actual graph-limit switching argument and normalization have
been proved, the imported beta-one loop characterization identifies the
original counting marginal. Finite strata are eliminated by a proved law equality. -/
theorem identify_of_mass_exterior_switching
    (parameters : Parameters)
    (hm : ∀ q : ℕ, Integrable (fun s : AnchoredCountingState => ‖s.val.2‖ ^ q) ν)
    (hlinear : ∀ᵐ s ∂ν, anchoredLinearCoefficient s = 0)
    (hmass : ∀ᵐ s ∂ν, s.val.1.measure Set.univ = ∞)
    (hswitch : Measure.map (action GeneralizedSwitching.endpointPermutation)
      (Measure.map (massExterior ν hm1 parameters) (massMarkedLaw ν parameters)) =
      Measure.map (massExterior ν hm1 parameters) (massMarkedLaw ν parameters)) :
    Measure.map (fun s : AnchoredCountingState => s.val.1) ν = sineOneLaw := by
  let P := (infiniteBranchLaw ν hmass : Measure (MassState none))
  have hmap : Measure.map (Subtype.val : MassState none → AnchoredCountingState) P = ν :=
    infinite_branch_scalar_marginal ν hmass
  have hmp (q : ℕ) : Integrable
      (fun s : MassState none => ‖(stratumPresentation none s).scalar.val.2‖ ^ q) P := by
    have hi := hm q
    rw [← hmap] at hi
    exact (integrable_map_measure hi.aestronglyMeasurable
      measurable_subtype_coe.aemeasurable).mp hi
  have hlp : ∀ᵐ s ∂P, anchoredLinearCoefficient (stratumPresentation none s).scalar = 0 := by
    rw [← hmap] at hlinear
    exact ae_of_ae_map measurable_subtype_coe.aemeasurable hlinear
  have hs := hswitch
  rw [massExterior_law_eq_infinite_branch ν hm1 hmass parameters] at hs
  letI : Infinite (MassLabels none) := inferInstanceAs (Infinite ℕ)
  have hid := identify_of_gaussian_exterior_switching P
    (stratumPresentation none) (measurable_stratumPresentation none)
    (massStratum_anchor_integrable ν hm1 (infiniteActive ν hmass)) parameters hmp hlp hs
  have heq : Measure.map (fun s : MassState none => (stratumPresentation none s).scalar.val.1) P =
      Measure.map (fun s : AnchoredCountingState => s.val.1) ν := by
    rw [← hmap,Measure.map_map
      (show Measurable (fun s : AnchoredCountingState => s.val.1) from
        measurable_fst.comp measurable_subtype_coe)
      (show Measurable (Subtype.val : MassState none → AnchoredCountingState) from
        measurable_subtype_coe)]
    rfl
  exact heq.symm.trans hid

end GeneralizedBulk.Exterior
