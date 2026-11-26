import GaussianWave.BS.LiftedCoverMoments
import GaussianWave.BS.LiftedApproximateEigenrelations

/-! Actual whole-process limits of finite-graph cover colorings from only
empirical root L2 bounds. The limits preserve genuine tree invariance and
convergent-energy eigenrelations, while second moments may decrease. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology BigOperators Classical
namespace GaussianWave.BS
open Reused.Graph Reused.Graph.Configuration

def uniformLiftedTreeProbabilityLaw {N m r : ℕ} (G : RegularGraph N (m+2)) (hN : 0<N)
    (f : Fin r → Fin N → ℝ) : ProbabilityMeasure ((Fin r × RegularTreeVertex (m+2)) → ℝ) :=
  ⟨uniformLiftedTreeLaw G hN f,inferInstance⟩

/-- Empirical root L2 control alone constructs an actual entire-process
weak subsequence of the literal finite-graph cover laws. -/
theorem uniformLiftedTreeLaw_subsequence_of_root_second
    (m r : ℕ) (N : ℕ → ℕ) (G : ∀ n, RegularGraph (N n) (m+2)) (hN : ∀ n, 0<N n)
    (f : ∀ n, Fin r → Fin (N n) → ℝ) (M : Fin r → ℝ)
    (hM : ∀ n a, ((N n : ℝ)⁻¹*∑ v, f n a v^2)≤M a) :
    ∃ (ν : ProbabilityMeasure ((Fin r × RegularTreeVertex (m+2)) → ℝ)) (s : ℕ → ℕ),
      StrictMono s ∧
      Tendsto ((fun n => uniformLiftedTreeProbabilityLaw (G n) (hN n) (f n)) ∘ s) atTop (𝓝 ν) ∧
      ∀ (a : Fin r) (u : RegularTreeVertex (m+2)),
        Integrable (fun x => x (a,u)^2) (ν : Measure ((Fin r × RegularTreeVertex (m+2)) → ℝ)) ∧
        (∫ x, x (a,u)^2 ∂(ν : Measure ((Fin r × RegularTreeVertex (m+2)) → ℝ)))≤M a := by
  let P := fun n => uniformLiftedTreeProbabilityLaw (G n) (hN n) (f n)
  have hi (n : ℕ) (av : Fin r × RegularTreeVertex (m+2)) :
      Integrable (fun x => x av^2) (P n : Measure ((Fin r × RegularTreeVertex (m+2)) → ℝ)) :=
    integrable_uniformLiftedTreeLaw_coordinate (G n) (hN n) (f n) av.1 av.2 (fun x => x^2) (by fun_prop)
  have hb (n : ℕ) (av : Fin r × RegularTreeVertex (m+2)) :
      (∫ x, x av^2 ∂(P n : Measure ((Fin r × RegularTreeVertex (m+2)) → ℝ)))≤M av.1 := by
    change (∫ x, x (av.1,av.2)^2 ∂uniformLiftedTreeLaw (G n) (hN n) (f n))≤_
    rw [integral_uniformLiftedTreeLaw_coordinate (G n) (hN n) (f n) av.1 av.2 (fun x => x^2) (by fun_prop)]
    exact hM n av.1
  obtain ⟨ν,s,hs,hweak⟩ := process_laws_subsequence_of_uniform_coordinate_second P hi (fun av => M av.1) hb
  refine ⟨ν,s,hs,hweak,?_⟩
  intro a u
  exact process_coordinate_second_limit (P ∘ s) ν hweak
    (fun n av => hi (s n) av) (fun av => M av.1) (fun n av => hb (s n) av) (a,u)

/-- Every fixed finite coordinate window of an actual whole-process weak
limit converges weakly as well. -/
theorem process_finiteWindow_weakConverges_of_tendsto
    {I : Type*} [Countable I] (μ : ℕ → ProbabilityMeasure (I → ℝ))
    (ν : ProbabilityMeasure (I → ℝ)) (hweak : Tendsto μ atTop (𝓝 ν))
    {J : Type*} [Fintype J] (site : J → I) :
    WeakLawConverges (fun n => Measure.map (fun x : I → ℝ => fun j => x (site j)) (μ n : Measure _))
      (Measure.map (fun x : I → ℝ => fun j => x (site j)) (ν : Measure _)) := by
  have hC : Continuous (fun x : I → ℝ => fun j => x (site j)) :=
    continuous_pi (fun j => continuous_apply _)
  have h := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous μ ν hweak hC
  exact ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp h

/-- Invariance under an actual continuous relabeling passes to an actual
whole-process weak limit; no limiting-invariance hypothesis is supplied. -/
theorem process_invariance_of_tendsto
    {I : Type*} [Countable I] (μ : ℕ → ProbabilityMeasure (I → ℝ))
    (ν : ProbabilityMeasure (I → ℝ)) (hweak : Tendsto μ atTop (𝓝 ν))
    (T : (I → ℝ) → (I → ℝ)) (hT : Continuous T)
    (hI : ∀ n, Measure.map T (μ n : Measure _)= (μ n : Measure _)) :
    Measure.map T (ν : Measure _)=(ν : Measure _) := by
  have h := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous μ ν hweak hT
  have he (n : ℕ) : (μ n).map hT.measurable.aemeasurable=μ n := Subtype.ext (hI n)
  have hc : Tendsto μ atTop (𝓝 (ν.map hT.measurable.aemeasurable)) :=
    h.congr' (Eventually.of_forall he)
  exact congrArg (fun Q : ProbabilityMeasure (I → ℝ) => (Q : Measure (I → ℝ)))
    (tendsto_nhds_unique hc hweak)


/-- Actual finite-graph joint eigenvectors with only bounded empirical
root second moments have a genuine invariant tree eigenprocess limit along
a subsequence. The channel energies may vary and converge separately. -/
theorem uniformLiftedTreeLaw_eigenprocess_subsequence_of_root_second
    (m r : ℕ) (N : ℕ → ℕ) (G : ∀ n, RegularGraph (N n) (m+2)) (hN : ∀ n, 0<N n)
    (f : ∀ n, Fin r → Fin (N n) → ℝ) (M : Fin r → ℝ)
    (hM : ∀ n a, ((N n : ℝ)⁻¹*∑ v, f n a v^2)≤M a)
    (energies : ℕ → Fin r → ℝ) (energy : Fin r → ℝ)
    (henergies : ∀ a, Tendsto (fun n => energies n a) atTop (𝓝 (energy a)))
    (hf : ∀ n a, GraphEigenrelation (G n) (energies n a) (f n a)) :
    ∃ (ν : ProbabilityMeasure ((Fin r × RegularTreeVertex (m+2)) → ℝ)) (s : ℕ → ℕ),
      StrictMono s ∧
      Tendsto ((fun n => uniformLiftedTreeProbabilityLaw (G n) (hN n) (f n)) ∘ s) atTop (𝓝 ν) ∧
      (∀ (a : Fin r) (u : RegularTreeVertex (m+2)),
        Integrable (fun x => x (a,u)^2) (ν : Measure ((Fin r × RegularTreeVertex (m+2)) → ℝ)) ∧
        (∫ x, x (a,u)^2 ∂(ν : Measure ((Fin r × RegularTreeVertex (m+2)) → ℝ)))≤M a) ∧
      (∀ e : regularWordTree (m+2) ≃g regularWordTree (m+2),
        Measure.map (fun z : (Fin r × RegularTreeVertex (m+2)) → ℝ =>
          fun av : Fin r × RegularTreeVertex (m+2) => z (av.1,e av.2)) (ν : Measure _)= (ν : Measure _)) ∧
      (∀ᵐ x ∂(ν : Measure ((Fin r × RegularTreeVertex (m+2)) → ℝ)),
        ∀ a u, treeEigenResidual (m+2) r energy a u x=0) := by
  obtain ⟨ν,s,hs,hweak,hmom⟩ := uniformLiftedTreeLaw_subsequence_of_root_second m r N G hN f M hM
  let P := fun n => uniformLiftedTreeProbabilityLaw (G n) (hN n) (f n)
  refine ⟨ν,s,hs,hweak,hmom,?_,?_⟩
  · intro e
    apply process_invariance_of_tendsto (P ∘ s) ν hweak _
      (continuous_pi (fun av => continuous_apply (av.1,e av.2)))
    intro n
    exact uniformLiftedTreeLaw_invariant (G (s n)) (hN (s n)) (f (s n)) e
  · have hW : WeakLawConverges (fun n => (P (s n) : Measure ((Fin r × RegularTreeVertex (m+2)) → ℝ)))
        (ν : Measure ((Fin r × RegularTreeVertex (m+2)) → ℝ)) :=
      ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hweak
    apply weak_process_eigenrelations_of_exact (m+2) r _ _ hW (fun n => energies (s n)) energy
      (fun a => (henergies a).comp hs.tendsto_atTop)
      (fun n av => integrable_uniformLiftedTreeLaw_coordinate (G (s n)) (hN (s n)) (f (s n))
        av.1 av.2 (fun x => x^2) (by fun_prop)) (fun av => M av.1)
    · intro n av
      change (∫ x, x (av.1,av.2)^2 ∂uniformLiftedTreeLaw (G (s n)) (hN (s n)) (f (s n)))≤_
      rw [integral_uniformLiftedTreeLaw_coordinate (G (s n)) (hN (s n)) (f (s n))
        av.1 av.2 (fun x => x^2) (by fun_prop)]
      exact hM (s n) av.1
    · intro n
      exact uniformLiftedTreeLaw_eigenrelations (G (s n)) (hN (s n)) (energies (s n)) (f (s n)) (hf (s n))


/-- The same actual process-limit construction for genuinely approximate
finite-graph eigenvectors. The input residual is a literal graph average,
whose equality with the process residual was computed above. -/
theorem uniformLiftedTreeLaw_approximate_eigenprocess_subsequence_of_root_second
    (m r : ℕ) (N : ℕ → ℕ) (G : ∀ n, RegularGraph (N n) (m+2)) (hN : ∀ n, 0<N n)
    (f : ∀ n, Fin r → Fin (N n) → ℝ) (M : Fin r → ℝ)
    (hM : ∀ n a, ((N n : ℝ)⁻¹*∑ v, f n a v^2)≤M a)
    (energies : ℕ → Fin r → ℝ) (energy : Fin r → ℝ)
    (henergies : ∀ a, Tendsto (fun n => energies n a) atTop (𝓝 (energy a)))
    (hres : ∀ a, Tendsto
      (fun n => (N n : ℝ)⁻¹*∑ v, graphEigenResidual (G n) (energies n a) (f n a) v^2)
      atTop (𝓝 0)) :
    ∃ (ν : ProbabilityMeasure ((Fin r × RegularTreeVertex (m+2)) → ℝ)) (s : ℕ → ℕ),
      StrictMono s ∧
      Tendsto ((fun n => uniformLiftedTreeProbabilityLaw (G n) (hN n) (f n)) ∘ s) atTop (𝓝 ν) ∧
      (∀ (a : Fin r) (u : RegularTreeVertex (m+2)),
        Integrable (fun x => x (a,u)^2) (ν : Measure ((Fin r × RegularTreeVertex (m+2)) → ℝ)) ∧
        (∫ x, x (a,u)^2 ∂(ν : Measure ((Fin r × RegularTreeVertex (m+2)) → ℝ)))≤M a) ∧
      (∀ e : regularWordTree (m+2) ≃g regularWordTree (m+2),
        Measure.map (fun z : (Fin r × RegularTreeVertex (m+2)) → ℝ =>
          fun av : Fin r × RegularTreeVertex (m+2) => z (av.1,e av.2)) (ν : Measure _)= (ν : Measure _)) ∧
      (∀ᵐ x ∂(ν : Measure ((Fin r × RegularTreeVertex (m+2)) → ℝ)),
        ∀ a u, treeEigenResidual (m+2) r energy a u x=0) := by
  obtain ⟨ν,s,hs,hweak,hmom⟩ := uniformLiftedTreeLaw_subsequence_of_root_second m r N G hN f M hM
  let P := fun n => uniformLiftedTreeProbabilityLaw (G n) (hN n) (f n)
  refine ⟨ν,s,hs,hweak,hmom,?_,?_⟩
  · intro e
    apply process_invariance_of_tendsto (P ∘ s) ν hweak _
      (continuous_pi (fun av => continuous_apply (av.1,e av.2)))
    intro n
    exact uniformLiftedTreeLaw_invariant (G (s n)) (hN (s n)) (f (s n)) e
  · have hW : WeakLawConverges (fun n => (P (s n) : Measure ((Fin r × RegularTreeVertex (m+2)) → ℝ)))
        (ν : Measure ((Fin r × RegularTreeVertex (m+2)) → ℝ)) :=
      ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hweak
    apply weak_process_eigenrelations_of_residual_second (m+2) r _ _ hW
      (fun n => energies (s n)) energy (fun a => (henergies a).comp hs.tendsto_atTop)
      (fun n av => integrable_uniformLiftedTreeLaw_coordinate (G (s n)) (hN (s n)) (f (s n))
        av.1 av.2 (fun x => x^2) (by fun_prop)) (fun av => M av.1)
    · intro n av
      change (∫ x, x (av.1,av.2)^2 ∂uniformLiftedTreeLaw (G (s n)) (hN (s n)) (f (s n)))≤_
      rw [integral_uniformLiftedTreeLaw_coordinate (G (s n)) (hN (s n)) (f (s n))
        av.1 av.2 (fun x => x^2) (by fun_prop)]
      exact hM (s n) av.1
    · intro a u
      change Tendsto (fun n => ∫ x, treeEigenResidual (m+2) r (energies (s n)) a u x^2
        ∂uniformLiftedTreeLaw (G (s n)) (hN (s n)) (f (s n))) atTop (𝓝 0)
      simp_rw [integral_uniformLiftedTreeLaw_residual_sq]
      exact (hres a).comp hs.tendsto_atTop

end GaussianWave.BS
