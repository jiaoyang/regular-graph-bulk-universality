import GeneralizedBulk.Gaussian.StratifiedConstruction

/-! After normalization, the actual mass mixture is precisely its canonical
Nat-marked branch. No new marking law or analytic version is introduced. -/
noncomputable section
open MeasureTheory BourgadeHuang
open scoped ENNReal
namespace GeneralizedBulk.Gaussian
open Counting Analysis
variable (ν : Measure AnchoredCountingState) [IsProbabilityMeasure ν]
variable (hmass : ∀ᵐ s ∂ν, s.val.1.measure Set.univ = ∞)
include hmass

theorem infinite_stratum_mass : ν (stratumSet massClass none) = 1 := by
  apply (mem_ae_iff_prob_eq_one (measurableSet_massClass none)).mp
  exact hmass.mono (fun s hs => (massClass_eq_none_iff s).mpr hs)

def infiniteActive : MassActive ν :=
  ⟨none,by rw [infinite_stratum_mass ν hmass]; exact one_ne_zero⟩

def infiniteBranchLaw : ProbabilityMeasure (MassState none) :=
  massStratumLaw ν (infiniteActive ν hmass)

theorem massActive_eq_infinite (i : MassActive ν) : i = infiniteActive ν hmass := by
  apply Subtype.ext
  by_contra h
  apply i.property
  apply measure_mono_null (t := (stratumSet massClass none)ᶜ)
  · intro s hs hn
    exact h (hs.symm.trans hn)
  · exact ae_iff.mp (hmass.mono (fun s hs => (massClass_eq_none_iff s).mpr hs))

/-- The mixed probability law collapses exactly to the existing independent
Gaussian law on the infinite stratum, with its original common analytic version. -/
theorem massMarkedLaw_eq_infinite_branch (parameters : Parameters) :
    massMarkedLaw ν parameters = Measure.map (Sigma.mk (infiniteActive ν hmass))
      ((infiniteBranchLaw ν hmass : Measure (MassState none)).prod
        (iidLaw (markLaw parameters.p) ℕ)) := by
  classical
  ext A hA
  rw [massMarkedLaw,stratumMarkedLaw,Measure.sum_apply _ hA]
  rw [tsum_eq_single (infiniteActive ν hmass)]
  · simp only [Measure.smul_apply]
    change ν (stratumSet massClass none) •
      ((Measure.map (Sigma.mk (infiniteActive ν hmass))
        ((infiniteBranchLaw ν hmass : Measure (MassState none)).prod
          (iidLaw (markLaw parameters.p) ℕ))) A) = _
    rw [infinite_stratum_mass ν hmass,one_smul]
  · intro i hi
    exact (hi (massActive_eq_infinite ν hmass i)).elim

/-- The scalar law on the canonical infinite branch is the full limit law. -/
theorem infinite_branch_scalar_marginal :
    Measure.map (Subtype.val : MassState none → AnchoredCountingState)
      (infiniteBranchLaw ν hmass : Measure (MassState none)) = ν := by
  have h := mass_smul_map_conditionalSubtypeLaw ν (stratumSet massClass none)
    (measurableSet_massClass none) (infiniteActive ν hmass).property
  rw [infinite_stratum_mass ν hmass,one_smul] at h
  exact h.trans (Measure.restrict_eq_self_of_ae_mem
    (hmass.mono (fun s hs => (massClass_eq_none_iff s).mpr hs)))

theorem infinite_branch_scalar_identDistrib :
    ProbabilityTheory.IdentDistrib (Subtype.val : MassState none → AnchoredCountingState) id
      (infiniteBranchLaw ν hmass : Measure (MassState none)) ν := by
  refine ⟨measurable_subtype_coe.aemeasurable,measurable_id.aemeasurable,?_⟩
  simpa only [Measure.map_id] using infinite_branch_scalar_marginal ν hmass

theorem massCenteredField_infinite_branch
    (hm : Integrable (fun s : AnchoredCountingState => ‖s.val.2‖) ν)
    (parameters : Parameters) (v : ℂ × Bool)
    (z : MassState none × (ℕ → Fin 4 → ℝ)) :
    massCenteredField ν hm parameters v ⟨infiniteActive ν hmass,z⟩ =
      constructedField (infiniteBranchLaw ν hmass : Measure (MassState none))
        (stratumPresentation none) (measurable_stratumPresentation none)
        (massStratum_anchor_integrable ν hm (infiniteActive ν hmass)) parameters v z := rfl

theorem massMarkedLaw_map_infinite_branch {T : Type*} [MeasurableSpace T]
    (parameters : Parameters) (f : MassMarkedSample ν → T) (hf : Measurable f) :
    Measure.map f (massMarkedLaw ν parameters) =
      Measure.map (fun z => f ⟨infiniteActive ν hmass,z⟩)
        ((infiniteBranchLaw ν hmass : Measure (MassState none)).prod
          (iidLaw (markLaw parameters.p) ℕ)) := by
  rw [massMarkedLaw_eq_infinite_branch ν hmass parameters,
    Measure.map_map hf (measurable_sigma_mk _)]
  rfl

end GeneralizedBulk.Gaussian
