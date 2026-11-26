import GeneralizedBulk.Graph.WindowHYFactorization
import GeneralizedBulk.Graph.WindowResolvent
import GeneralizedBulk.Counting.WindowLawConvergence
import GeneralizedBulk.Analysis.WeakTensorFactorization

/-! The genuine joint finite scalar/window/endpoint-mark laws. -/
noncomputable section
open MeasureTheory BourgadeHuang Filter
open scoped Topology
namespace GeneralizedBulk.Counting

def countStratumIndicator (m : ℕ) : BoundedContinuousFunction (WindowData m) ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun z => if z.2.1 = m then 1 else 0)
    ((show Continuous (fun n : ℕ => if n = m then (1 : ℝ) else 0) from continuous_of_discreteTopology).comp
      (continuous_fst.comp continuous_snd)) 1 (fun z => by dsimp only; split_ifs <;> norm_num)

theorem countStratumIndicator_zero_or_one (m : ℕ) (z : WindowData m) :
    countStratumIndicator m z = 0 ∨ countStratumIndicator m z = 1 := by
  change (if z.2.1 = m then (1 : ℝ) else 0) = 0 ∨ (if z.2.1 = m then (1 : ℝ) else 0) = 1
  split_ifs <;> simp

end GeneralizedBulk.Counting
namespace GeneralizedBulk.External.RegularSpectralData
open Graph GeneralizedBulk.Counting GeneralizedBulk.Analysis
variable {d : ℕ} {N : ℕ → ℕ} {Ω : Type*} [MeasurableSpace Ω]
variable (D : RegularSpectralData d N Ω)

def windowMarkSample {m : ℕ} (n : ℕ) (E sigma center R : ℝ)
    (selection : Ω → Fin m → Fin (N n)) (z : Ω × ProposalSample (N n) d) :
    WindowData m × ((Fin m × Fin 4) → ℝ) :=
  (windowData m (-R) R (D.microscopicCountingState n z.1 E sigma center),
    D.proposalMark n z.1 (fun i => D.eigenvector n z.1 (selection z.1 i)) z.2)

theorem measurable_windowMarkSample {m : ℕ} (n : ℕ) (E sigma center R : ℝ)
    (selection : Ω → Fin m → Fin (N n)) (hselection : ∀ i, Measurable (fun ω => selection ω i)) :
    Measurable (D.windowMarkSample n E sigma center R selection) := by
  refine ((measurable_windowData m (-R) R).comp
    ((D.measurable_microscopicCountingState n E sigma center).comp measurable_fst)).prodMk ?_
  apply measurable_pi_lambda
  rintro ⟨a,i⟩
  apply measurable_from_prod_countable
  intro t
  exact (D.measurable_selectedEigenvector n (fun ω => selection ω a)
    (fun ω => D.proposalEndpoints n ω t i) (hselection a)
    (D.measurable_proposalEndpoints n t i)).const_mul _

def windowMarkLaw {m : ℕ} (P : Measure Ω) (n : ℕ) (E sigma center R : ℝ)
    (selection : Ω → Fin m → Fin (N n)) : Measure (WindowData m × ((Fin m × Fin 4) → ℝ)) :=
  Measure.map (D.windowMarkSample n E sigma center R selection)
    (P.prod (uniformOrientedProposals (N n) d))

theorem windowMarkLaw_isProbability {m : ℕ} (P : Measure Ω) [IsProbabilityMeasure P]
    (hd : 0 < d) (n : ℕ) (E sigma center R : ℝ)
    (selection : Ω → Fin m → Fin (N n)) (hselection : ∀ i, Measurable (fun ω => selection ω i)) :
    IsProbabilityMeasure (D.windowMarkLaw P n E sigma center R selection) := by
  letI := uniformOrientedProposals_isProbability (N n) d (D.size_pos n) hd
  exact MeasureTheory.isProbabilityMeasure_map
    (D.measurable_windowMarkSample n E sigma center R selection hselection).aemeasurable

theorem windowMarkLaw_fst {m : ℕ} (P : Measure Ω) (hd : 0 < d) (n : ℕ) (E sigma center R : ℝ)
    (selection : Ω → Fin m → Fin (N n)) (hselection : ∀ i, Measurable (fun ω => selection ω i)) :
    Measure.map Prod.fst (D.windowMarkLaw P n E sigma center R selection) =
      Measure.map (fun ω => windowData m (-R) R (D.microscopicCountingState n ω E sigma center)) P := by
  letI := uniformOrientedProposals_isProbability (N n) d (D.size_pos n) hd
  rw [windowMarkLaw,Measure.map_map measurable_fst (D.measurable_windowMarkSample n E sigma center R selection hselection)]
  change Measure.map ((fun ω => windowData m (-R) R (D.microscopicCountingState n ω E sigma center)) ∘ Prod.fst)
    (P.prod (uniformOrientedProposals (N n) d)) = _
  have hX : Measurable (fun ω => windowData m (-R) R (D.microscopicCountingState n ω E sigma center)) :=
    (measurable_windowData m (-R) R).comp (D.measurable_microscopicCountingState n E sigma center)
  rw [← Measure.map_map hX measurable_fst,Measure.map_fst_prod,measure_univ,one_smul]

/-- Every tensor expectation is exactly its scalar-state integral against
the physical two-edge mark kernel, with no asymptotic sampler replacement. -/
theorem windowMarkLaw_tensor_integral {m : ℕ} (P : Measure Ω) [IsProbabilityMeasure P]
    (hd : 0 < d) (n : ℕ) (E sigma center R : ℝ)
    (selection : Ω → Fin m → Fin (N n)) (hselection : ∀ i, Measurable (fun ω => selection ω i))
    (leaf : Fin d) (G : BoundedContinuousFunction (WindowData m) ℝ)
    (F : BoundedContinuousFunction ((Fin m × Fin 4) → ℝ) ℝ) :
    (∫ z, G z.1 * F z.2 ∂D.windowMarkLaw P n E sigma center R selection) =
      ∫ ω, G (windowData m (-R) R (D.microscopicCountingState n ω E sigma center)) *
        (∫ x, F x ∂D.twoEdgeLaw n ω (selection ω) leaf) ∂P := by
  letI := uniformOrientedProposals_isProbability (N n) d (D.size_pos n) hd
  letI := D.windowMarkLaw_isProbability P hd n E sigma center R selection hselection
  let T : BoundedContinuousFunction (WindowData m × ((Fin m × Fin 4) → ℝ)) ℝ :=
    G.compContinuous ⟨Prod.fst,continuous_fst⟩ * F.compContinuous ⟨Prod.snd,continuous_snd⟩
  have hsample := D.measurable_windowMarkSample n E sigma center R selection hselection
  have hi : Integrable (fun z => T (D.windowMarkSample n E sigma center R selection z))
      (P.prod (uniformOrientedProposals (N n) d)) :=
    (T.integrable (D.windowMarkLaw P n E sigma center R selection)).comp_measurable hsample
  change (∫ z, T z ∂D.windowMarkLaw P n E sigma center R selection) = _
  rw [windowMarkLaw,integral_map hsample.aemeasurable T.continuous.measurable.aestronglyMeasurable,
    integral_prod _ hi]
  apply integral_congr_ae
  filter_upwards [] with ω
  change (∫ t, G (windowData m (-R) R (D.microscopicCountingState n ω E sigma center)) *
    F (D.proposalMark n ω (fun i => D.eigenvector n ω (selection ω i)) t)
    ∂uniformOrientedProposals (N n) d) = _
  rw [integral_const_mul,D.twoEdgeLaw_eq_proposalMarkLaw n ω (selection ω) leaf,proposalMarkLaw,
    integral_map (measurable_of_finite _).aemeasurable F.continuous.measurable.aestronglyMeasurable]

end GeneralizedBulk.External.RegularSpectralData
