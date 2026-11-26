import GeneralizedBulk.Gaussian.StratifiedWindow
import GeneralizedBulk.Gaussian.WindowFamilyLaw
import GeneralizedBulk.Analysis.StratumKernel
import GeneralizedBulk.Counting.WindowLawConvergence

/-! The actual mixed Gaussian window law has the conditional iid finite-mark kernel. -/
noncomputable section
open MeasureTheory BourgadeHuang
open scoped Topology
namespace GeneralizedBulk.Gaussian
open Counting Analysis
set_option maxHeartbeats 250000
variable {V : Type*}
variable (ν : Measure AnchoredCountingState) [IsProbabilityMeasure ν]

/-- The finite spectral family of the actual pre-normalization window field. -/
def massWindowFamily (parameters : Parameters) (R : ℝ) (spectral : V → ℂ × Bool)
    (z : MassMarkedSample ν) : V → EndpointMatrix :=
  fun v => massWindowField ν parameters R (spectral v) z

theorem measurable_massWindowFamily (parameters : Parameters) (R : ℝ)
    (spectral : V → ℂ × Bool) : Measurable (massWindowFamily ν parameters R spectral) :=
  measurable_pi_lambda _ (fun v => measurable_massWindowField ν parameters R (spectral v))

/-- Conditional on the entire scalar state and on having m retained particles,
the genuine mixed field is evaluated from m independent Gaussian marks. -/
theorem massWindowFamily_kernel_law (parameters : Parameters) (R : ℝ)
    (spectral : V → ℂ × Bool) (m : ℕ) :
    Measure.map (fun z => (windowData m (-R) R (massScalarState ν z),
      massWindowFamily ν parameters R spectral z))
      ((massMarkedLaw ν parameters).restrict
        {z | intervalCount (massScalarState ν z).val.1 (-R) R = m}) =
    Measure.map (fun z : AnchoredCountingState × ((Fin m × Fin 4) → ℝ) =>
      (windowData m (-R) R z.1,
        finiteParticleFamily parameters (fun j => windowOccurrence z.1.val.1 (-R) R j.val) spectral z.2))
      ((ν.restrict {s | intervalCount s.val.1 (-R) R = m}).prod (finiteMarkLaw parameters.p m)) := by
  have hcount : Measurable (fun s : AnchoredCountingState => intervalCount s.val.1 (-R) R) :=
    (measurable_intervalCount (-R) R).comp (measurable_fst.comp measurable_subtype_coe)
  have hS : MeasurableSet {s : AnchoredCountingState | intervalCount s.val.1 (-R) R = m} :=
    hcount (measurableSet_singleton m)
  let K := fun z : AnchoredCountingState × ((Fin m × Fin 4) → ℝ) =>
    finiteParticleFamily parameters (fun j => windowOccurrence z.1.val.1 (-R) R j.val) spectral z.2
  have hmeasure : Measurable (fun s : AnchoredCountingState => s.val.1) :=
    measurable_fst.comp measurable_subtype_coe
  have hlocations : Measurable (fun s : AnchoredCountingState =>
      fun j : Fin m => windowOccurrence s.val.1 (-R) R j.val) :=
    measurable_pi_lambda _ (fun j => (measurable_windowOccurrence (-R) R j.val).comp hmeasure)
  have hK : Measurable K := by
    apply measurable_pi_lambda
    intro v
    change @Measurable _ (Fin 4 → Fin 4 → ℂ) _ (borel _) _
    rw [← @BorelSpace.measurable_eq (Fin 4 → Fin 4 → ℂ) _ MeasurableSpace.pi (by infer_instance)]
    apply measurable_pi_lambda
    intro a
    apply measurable_pi_lambda
    intro b
    change Measurable (fun z : AnchoredCountingState × ((Fin m × Fin 4) → ℝ) =>
      ∑ j : Fin m, (parameters.scale : ℂ) *
        particleCoefficient (windowOccurrence z.1.val.1 (-R) R j.val) (spectral v) *
          (rawQuadratic parameters.p a b (fun k => z.2 (j,k)) : ℂ))
    apply Finset.measurable_sum
    intro j hj
    have hx : Measurable (fun z : AnchoredCountingState × ((Fin m × Fin 4) → ℝ) =>
        windowOccurrence z.1.val.1 (-R) R j.val) :=
      ((measurable_windowOccurrence (-R) R j.val).comp hmeasure).comp measurable_fst
    have hy : Measurable (fun z : AnchoredCountingState × ((Fin m × Fin 4) → ℝ) =>
        fun k : Fin 4 => z.2 (j,k)) :=
      measurable_pi_lambda _ (fun k => (measurable_pi_apply (j,k)).comp measurable_snd)
    exact (((measurable_particleCoefficient (spectral v)).comp hx).const_mul (parameters.scale : ℂ)).mul
      (((measurable_rawQuadratic parameters.p a b).comp hy).complex_ofReal)
  apply stratum_joint_kernel_law ν massClass measurable_massClass
    (MassMarkSpace ν) (fun i => iidLaw (markLaw parameters.p) (MassLabels i.val))
    (finiteMarkLaw parameters.p m) _ hS (windowData m (-R) R) (measurable_windowData m (-R) R)
    (massWindowFamily ν parameters R spectral) (measurable_massWindowFamily ν parameters R spectral) K hK
  intro i s hs
  have hscalar : (stratumPresentation i.val s).scalar = s.val := stratumPresentation_scalar i.val s
  have hfun : (fun y : MassMarkSpace ν i => massWindowFamily ν parameters R spectral ⟨i,(s,y)⟩) =
      windowFamily parameters (stratumPresentation i.val s).presentation (-R) R spectral := by
    funext y v
    exact globalWindowField_eq_windowField (stratumPresentation i.val) parameters R (spectral v) (s,y)
  rw [hfun,windowFamily_law]
  have hs' : intervalCount (stratumPresentation i.val s).scalar.val.1 (-R) R = m := by
    rw [hscalar]
    exact hs
  cases hs'
  simp only [K,hscalar]

/-- In the same WindowData coordinates as the finite BS limit, the restricted
joint Gaussian law is exactly the finite iid-mark product law pushed through
its explicit polynomial field map. -/
theorem massWindowFamily_restrict_law (parameters : Parameters) (R : ℝ)
    (spectral : V → ℂ × Bool) (m : ℕ) :
    (Measure.map (fun z => (windowData m (-R) R (massScalarState ν z),
      massWindowFamily ν parameters R spectral z)) (massMarkedLaw ν parameters)).restrict
        (Prod.fst ⁻¹' {d : WindowData m | d.2.1 = m}) =
    Measure.map (fun z : WindowData m × ((Fin m × Fin 4) → ℝ) =>
      (z.1,finiteParticleFamily parameters z.1.2.2 spectral z.2))
      (((Measure.map (windowData m (-R) R) ν).restrict {d : WindowData m | d.2.1 = m}).prod
        (finiteMarkLaw parameters.p m)) := by
  have hd : Measurable (windowData m (-R) R) := measurable_windowData m (-R) R
  have hT : MeasurableSet {d : WindowData m | d.2.1 = m} :=
    (measurable_fst.comp measurable_snd) (measurableSet_singleton m)
  have hpair : Measurable (fun z => (windowData m (-R) R (massScalarState ν z),
      massWindowFamily ν parameters R spectral z)) :=
    (hd.comp (measurable_massScalarState ν)).prodMk (measurable_massWindowFamily ν parameters R spectral)
  rw [Measure.restrict_map hpair (measurable_fst hT)]
  change Measure.map _ ((massMarkedLaw ν parameters).restrict
    {z | intervalCount (massScalarState ν z).val.1 (-R) R = m}) = _
  rw [massWindowFamily_kernel_law]
  let F := fun z : WindowData m × ((Fin m × Fin 4) → ℝ) =>
    (z.1,finiteParticleFamily parameters z.1.2.2 spectral z.2)
  have hloc : Measurable (fun z : WindowData m × ((Fin m × Fin 4) → ℝ) => z.1.2.2) :=
    measurable_snd.comp (measurable_snd.comp measurable_fst)
  have hFF : Measurable (fun z : WindowData m × ((Fin m × Fin 4) → ℝ) =>
      fun v : V => finiteParticleField parameters z.1.2.2 (spectral v) z.2) := by
    apply measurable_pi_lambda
    intro v
    change @Measurable _ (Fin 4 → Fin 4 → ℂ) _ (borel _) _
    rw [← @BorelSpace.measurable_eq (Fin 4 → Fin 4 → ℂ) _ MeasurableSpace.pi (by infer_instance)]
    apply measurable_pi_lambda
    intro a
    apply measurable_pi_lambda
    intro b
    change Measurable (fun z : WindowData m × ((Fin m × Fin 4) → ℝ) =>
      ∑ j : Fin m, (parameters.scale : ℂ) * particleCoefficient (z.1.2.2 j) (spectral v) *
        (rawQuadratic parameters.p a b (fun k => z.2 (j,k)) : ℂ))
    apply Finset.measurable_sum
    intro j hj
    have hx : Measurable (fun z : WindowData m × ((Fin m × Fin 4) → ℝ) => z.1.2.2 j) :=
      (measurable_pi_apply j).comp hloc
    have hy : Measurable (fun z : WindowData m × ((Fin m × Fin 4) → ℝ) =>
        fun k : Fin 4 => z.2 (j,k)) :=
      measurable_pi_lambda _ (fun k => (measurable_pi_apply (j,k)).comp measurable_snd)
    exact (((measurable_particleCoefficient (spectral v)).comp hx).const_mul (parameters.scale : ℂ)).mul
      (((measurable_rawQuadratic parameters.p a b).comp hy).complex_ofReal)
  have hF : Measurable F := measurable_fst.prodMk hFF
  rw [Measure.restrict_map hd hT]
  have hprod := Measure.map_prod_map
    (ν.restrict ((windowData m (-R) R) ⁻¹' {d : WindowData m | d.2.1 = m}))
    (finiteMarkLaw parameters.p m) hd measurable_id
  rw [Measure.map_id] at hprod
  rw [hprod,Measure.map_map hF (hd.prodMap measurable_id)]
  rfl

end GeneralizedBulk.Gaussian
