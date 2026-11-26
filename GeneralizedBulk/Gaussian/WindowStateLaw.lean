import GeneralizedBulk.Gaussian.StratifiedWindowLaw

/-! Canonical common state/field coordinates for the marked-window limits. -/
noncomputable section
open MeasureTheory BourgadeHuang
open scoped Topology BigOperators
namespace GeneralizedBulk.Gaussian
open Counting
variable {V : Type*} [Fintype V]

abbrev WindowFieldState (V : Type*) := AnchoredCountingState × (V → EndpointMatrix)

def windowPolynomialState {m : ℕ} (parameters : Parameters) (spectral : V → ℂ × Bool)
    (z : WindowData m × ((Fin m × Fin 4) → ℝ)) : WindowFieldState V :=
  (z.1.1,finiteParticleFamily parameters z.1.2.2 spectral z.2)

/-- The finite-window polynomial is continuous jointly in all locations,
Gaussian marks, and the retained scalar state. -/
theorem continuous_windowPolynomialState {m : ℕ} (parameters : Parameters)
    (spectral : V → ℂ × Bool) : Continuous (windowPolynomialState (m := m) parameters spectral) := by
  apply (continuous_fst.comp continuous_fst).prodMk
  apply continuous_pi
  intro v
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  change Continuous (fun z : WindowData m × ((Fin m × Fin 4) → ℝ) =>
    ∑ k : Fin m, (parameters.scale : ℂ) * particleCoefficient (z.1.2.2 k) (spectral v) *
      (rawQuadratic parameters.p i j (fun a => z.2 (k,a)) : ℂ))
  apply continuous_finset_sum
  intro k hk
  have hx : Continuous (fun z : WindowData m × ((Fin m × Fin 4) → ℝ) => z.1.2.2 k) :=
    (continuous_apply k).comp (continuous_snd.comp (continuous_snd.comp continuous_fst))
  have hc := (continuous_particleCoefficient (spectral v)).comp hx
  have hq : Continuous (fun z : WindowData m × ((Fin m × Fin 4) → ℝ) =>
      (rawQuadratic parameters.p i j (fun a => z.2 (k,a)) : ℂ)) := by
    unfold rawQuadratic
    fun_prop
  exact (continuous_const.mul hc).mul hq

variable (ν : Measure AnchoredCountingState) [IsProbabilityMeasure ν]

def massWindowState (parameters : Parameters) (R : ℝ) (spectral : V → ℂ × Bool)
    (z : MassMarkedSample ν) : WindowFieldState V :=
  (massScalarState ν z,massWindowFamily ν parameters R spectral z)

theorem measurable_massWindowState (parameters : Parameters) (R : ℝ) (spectral : V → ℂ × Bool) :
    Measurable (massWindowState ν parameters R spectral) :=
  (measurable_massScalarState ν).prodMk (measurable_massWindowFamily ν parameters R spectral)

/-- The actual mixed state/field window law on a count stratum is exactly the
continuous finite polynomial pushforward of the BS product-law target. -/
theorem massWindowState_restrict_law (parameters : Parameters) (R : ℝ)
    (spectral : V → ℂ × Bool) (m : ℕ) :
    (Measure.map (massWindowState ν parameters R spectral) (massMarkedLaw ν parameters)).restrict
      {z | intervalCount z.1.val.1 (-R) R = m} =
    Measure.map (windowPolynomialState parameters spectral)
      (((Measure.map (windowData m (-R) R) ν).restrict {d : WindowData m | d.2.1=m}).prod
        (finiteMarkLaw parameters.p m)) := by
  let drop : WindowData m × (V → EndpointMatrix) → WindowFieldState V := fun z => (z.1.1,z.2)
  have hdrop : Measurable drop := (measurable_fst.comp measurable_fst).prodMk measurable_snd
  let full := fun z : MassMarkedSample ν =>
    (windowData m (-R) R (massScalarState ν z),massWindowFamily ν parameters R spectral z)
  have hfull : Measurable full :=
    ((measurable_windowData m (-R) R).comp (measurable_massScalarState ν)).prodMk
      (measurable_massWindowFamily ν parameters R spectral)
  have hT : MeasurableSet {d : WindowData m | d.2.1=m} :=
    (measurable_fst.comp measurable_snd) (measurableSet_singleton m)
  have hS : MeasurableSet {z : WindowFieldState V | intervalCount z.1.val.1 (-R) R = m} :=
    (((measurable_intervalCount (-R) R).comp
      (measurable_fst.comp measurable_subtype_coe)).comp measurable_fst) (measurableSet_singleton m)
  have h := congrArg (Measure.map drop) (massWindowFamily_restrict_law ν parameters R spectral m)
  rw [Measure.restrict_map hfull (measurable_fst hT),
    Measure.map_map hdrop hfull] at h
  have hpoly : Measurable (fun z : WindowData m × ((Fin m × Fin 4) → ℝ) =>
      (z.1,finiteParticleFamily parameters z.1.2.2 spectral z.2)) := by
    have hd : Continuous (fun z : WindowData m × ((Fin m × Fin 4) → ℝ) =>
        (z.1,finiteParticleFamily parameters z.1.2.2 spectral z.2)) := by
      exact continuous_fst.prodMk ((continuous_snd.comp (continuous_windowPolynomialState parameters spectral)))
    exact hd.measurable
  rw [Measure.map_map hdrop hpoly] at h
  rw [Measure.restrict_map (measurable_massWindowState ν parameters R spectral) hS]
  exact h

end GeneralizedBulk.Gaussian
