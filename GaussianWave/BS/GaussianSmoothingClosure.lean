import GaussianWave.BS.GaussianSmoothingRealizations
import GaussianWave.BS.RationalCharacteristicTests
import GaussianWave.BS.TreeProcessUniqueness
import GaussianWave.BS.LiftedProcessLimits
import GaussianWave.BS.IndependentTreeSum

/-! Genuine graph-limit closure under independent Gaussian-wave addition.
The smoothed entire-process law is realized on a strict subsequence of the
same graphs with a uniform root second-moment bound. -/
noncomputable section
open MeasureTheory Filter
open scoped BigOperators Classical Topology
namespace GaussianWave.BS
open Reused.Graph Lower

/-- A concrete countable convergence-determining family for joint tree laws. -/
def TreeRationalTestIndex (m r : ℕ) :=
  Σ k : ℕ,((Fin r × VertexBallVertex (m+2) k) → ℚ) × Bool

instance (m r : ℕ) : Countable (TreeRationalTestIndex m r) := by
  unfold TreeRationalTestIndex
  infer_instance

instance (m r : ℕ) : Nonempty (TreeRationalTestIndex m r) :=
  ⟨⟨0,(fun _ => 0),false⟩⟩

/-- The smoothed law is obtained as an actual whole-process graph limit.
Inputs are only the original graph limit, a root-L2 bound, local tree-likeness,
and the proved strict-bulk Gaussian blockfactor construction. -/
theorem exists_graph_realization_independent_gaussian_wave_sum
    (N : ℕ → ℕ) (m r : ℕ) (hm : 0 < m)
    (G : ∀ n,RegularGraph (N n) (m+2)) (hN : ∀ n,0 < N n)
    (hsize : Tendsto (fun n => (N n : ℝ)) atTop atTop)
    (f : ∀ n,Fin r → Fin (N n) → ℝ) (S : ℝ)
    (hS : ∀ n,graphMarkRootEnergy (f n) ≤ S)
    (x : ℝ) (hx : |x|<1)
    (P : ProbabilityMeasure ((Fin r × RegularTreeVertex (m+2)) → ℝ))
    (hweak : ∀ k,WeakLawConverges (fun n => finiteVertexCoverLaw (G n) k (f n))
      (Measure.map (fun z : (Fin r × RegularTreeVertex (m+2)) → ℝ =>
        fun av : Fin r × VertexBallVertex (m+2) k => z (av.1,vertexBallEmbedding (m+2) k av.2))
        (P : Measure _)))
    (hbad : ∀ k,Tendsto (fun n => (N n : ℝ)⁻¹*badVertexCoverRootCount (G n) k) atTop (𝓝 0)) :
    ∃ (n : ℕ → ℕ),StrictMono n ∧ ∃ (g : ∀ j,Fin r → Fin (N (n j)) → ℝ),
      (∀ j,graphMarkRootEnergy (g j)<4*S+4*(r : ℝ)+3) ∧
      Tendsto (fun j => uniformLiftedTreeProbabilityLaw (G (n j)) (hN (n j)) (g j)) atTop
        (𝓝 (⟨independentTreeSumLaw (P : Measure _)
          (jointGaussianTreeProcessLaw r m (radialEnergy m x)),inferInstance⟩ :
            ProbabilityMeasure ((Fin r × RegularTreeVertex (m+2)) → ℝ))) := by
  let W (k : ℕ) := fun z : (Fin r × RegularTreeVertex (m+2)) → ℝ =>
    fun av : Fin r × VertexBallVertex (m+2) k => z (av.1,vertexBallEmbedding (m+2) k av.2)
  have hW (k : ℕ) : Measurable (W k) := measurable_pi_lambda _ (fun _ => measurable_pi_apply _)
  let μ (k : ℕ) : ProbabilityMeasure ((Fin r × VertexBallVertex (m+2) k) → ℝ) :=
    ⟨Measure.map (W k) (P : Measure _),isProbabilityMeasure_map (hW k).aemeasurable⟩
  let Q := independentTreeSumLaw (P : Measure _) (jointGaussianTreeProcessLaw r m (radialEnergy m x))
  letI : IsProbabilityMeasure Q := independentTreeSumLaw_probability _ _
  obtain ⟨e,he⟩ := exists_surjective_nat (TreeRationalTestIndex m r)
  let k (i : ℕ) := (e i).1
  let F (i : ℕ) := boundedCharacteristicTest (fun av => (((e i).2.1 av : ℚ) : ℝ)) (e i).2.2
  obtain ⟨n,hn,g,henergy,hconv⟩ := exists_graphGaussian_smoothing_test_realizations
    N m r hm G hN hsize f S hS x hx 1 μ hweak hbad k F
    (fun i z => (boundedCharacteristicTest_bounds _ _ z).1)
    (fun i z => (boundedCharacteristicTest_bounds _ _ z).2)
  have henergy' (j : ℕ) : graphMarkRootEnergy (g j)<4*S+4*(r : ℝ)+3 := by
    simpa only [one_pow,mul_one] using henergy j
  have hselected (u : TreeRationalTestIndex m r) :
      Tendsto (fun j => ∫ z,boundedCharacteristicTest (fun av => ((u.2.1 av : ℚ) : ℝ)) u.2.2 z
        ∂finiteVertexCoverLaw (G (n j)) u.1 (g j)) atTop
        (𝓝 (∫ z,boundedCharacteristicTest (fun av => ((u.2.1 av : ℚ) : ℝ)) u.2.2 z
          ∂Measure.map (W u.1) Q)) := by
    obtain ⟨i,rfl⟩ := he u
    have h := hconv i
    have htarget : Measure.map (W (k i)) Q = independentAddLaw (μ (k i) : Measure _)
        (Measure.map (W (k i)) (jointGaussianTreeProcessLaw r m (radialEnergy m x))) 1 :=
      independentTreeSumLaw_window (P : Measure _)
        (jointGaussianTreeProcessLaw r m (radialEnergy m x)) (vertexBallEmbedding (m+2) (k i))
    rw [← htarget] at h
    exact h
  have hchannel (j : ℕ) (a : Fin r) :
      (N (n j) : ℝ)⁻¹*∑ v,(g j a v)^2 ≤ 4*S+4*(r : ℝ)+3 := by
    have ha : (∑ v : Fin (N (n j)),(g j a v)^2) ≤ ∑ b : Fin r,∑ v : Fin (N (n j)),(g j b v)^2 :=
      Finset.single_le_sum (fun b _ => Finset.sum_nonneg (fun v _ => sq_nonneg _)) (Finset.mem_univ a)
    exact (mul_le_mul_of_nonneg_left ha (by positivity)).trans (henergy' j).le
  obtain ⟨ν,s,hs,hν,hmom⟩ := uniformLiftedTreeLaw_subsequence_of_root_second m r (N ∘ n)
    (fun j => G (n j)) (fun j => hN (n j)) g (fun _ => 4*S+4*(r : ℝ)+3) hchannel
  have hballs (L : ℕ) : Measure.map (W L) (ν : Measure _)=Measure.map (W L) Q := by
    letI : IsProbabilityMeasure (Measure.map (W L) (ν : Measure _)) := isProbabilityMeasure_map (hW L).aemeasurable
    letI : IsProbabilityMeasure (Measure.map (W L) Q) := isProbabilityMeasure_map (hW L).aemeasurable
    apply measure_eq_of_rational_characteristic_tests
    intro q b
    have ht := (hselected ⟨L,q,b⟩).comp hs.tendsto_atTop
    have hw := process_finiteWindow_weakConverges_of_tendsto
      (fun j => uniformLiftedTreeProbabilityLaw (G (n (s j))) (hN (n (s j))) (g (s j))) ν hν
      (fun av : Fin r × VertexBallVertex (m+2) L => (av.1,vertexBallEmbedding (m+2) L av.2))
    have htest := hw (boundedCharacteristicTest (fun av => (q av : ℝ)) b)
    change Tendsto (fun j => ∫ z,boundedCharacteristicTest (fun av => (q av : ℝ)) b z
      ∂Measure.map (W L) (uniformLiftedTreeLaw (G (n (s j))) (hN (n (s j))) (g (s j))))
      atTop (𝓝 (∫ z,boundedCharacteristicTest (fun av => (q av : ℝ)) b z ∂Measure.map (W L) (ν : Measure _))) at htest
    simp only [W,uniformLiftedTreeLaw_ball] at htest
    exact tendsto_nhds_unique htest ht
  have heq : (ν : Measure _)=Q := treeProcessLaw_eq_of_ball_marginals m r (ν : Measure _) Q hballs
  have hνeq : ν=(⟨Q,inferInstance⟩ : ProbabilityMeasure _) := Subtype.ext heq
  rw [hνeq] at hν
  refine ⟨n ∘ s,hn.comp hs,fun j => g (s j),fun j => henergy' (s j),?_⟩
  exact hν

end GaussianWave.BS
