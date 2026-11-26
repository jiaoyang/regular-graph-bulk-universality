import GaussianWave.BS.GaussianTreeProcess
import GaussianWave.BS.TreeBallDistances
import GaussianWave.BS.GaussianVertexBallKernel
import GaussianWave.BS.GaussianBlockFactor
import GaussianWave.BS.GaussianGainAsymptotic

/-! The actual infinite Gaussian process has the actual graph-distance
wave covariance and is invariant under all tree automorphisms. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators Topology Classical
namespace GaussianWave.BS

theorem gaussianTreeProcessLaw_finite_waveFactor
    (m : ℕ) (energy : ℝ) (he : |energy| < (m+2 : ℝ))
    {J : Type*} [Fintype J] (site : J → RegularTreeVertex (m+2)) :
    ∃ (K : Type) (_ : Fintype K) (L : Matrix J K ℝ),
      Measure.map (fun x : RegularTreeVertex (m+2) → ℝ => fun j => x (site j))
        (gaussianTreeProcessLaw m energy : Measure _) = linearImageGaussian L ∧
      L*L.transpose = fun i j => sphericalCovariance (m+2) energy
        ((regularWordTree (m+2)).dist (site i) (site j)) := by
  let S : Finset (RegularTreeVertex (m+2)) := Finset.univ.image site
  let n := finiteTreeDepth S
  let lift : J → VertexBallVertex (m+2) n := fun j => treeBallIndexOfDepth (m+2) n (site j)
    (depth_le_finiteTreeDepth S ⟨site j,Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩⟩)
  have hlift (j) : vertexBallEmbedding (m+2) n (lift j) = site j := treeBallIndexOfDepth_spec _ _ _ _
  let L : Matrix J (VertexGaussianInput m n) ℝ := fun j a => vertexWaveCoefficient m n energy (lift j) a
  refine ⟨VertexGaussianInput m n,inferInstance,L,?_,?_⟩
  · let T := fun x : VertexBallVertex (m+2) n → ℝ => fun j => x (lift j)
    have hT : Measurable T := measurable_pi_lambda _ (fun _ => measurable_pi_apply _)
    have hB : Measurable (fun x : RegularTreeVertex (m+2) → ℝ =>
        fun v => x (vertexBallEmbedding (m+2) n v)) :=
      measurable_pi_lambda _ (fun _ => measurable_pi_apply _)
    have hcomp : (fun x : RegularTreeVertex (m+2) → ℝ => fun j => x (site j)) =
        T ∘ (fun x : RegularTreeVertex (m+2) → ℝ => fun v => x (vertexBallEmbedding (m+2) n v)) := by
      funext x j
      exact congrArg x (hlift j).symm
    rw [hcomp,← Measure.map_map hT hB,gaussianTreeProcessLaw_ball,
      vertexGaussianBallLaw_eq_waveFactor m n energy (ne_of_lt ((le_abs_self _).trans_lt he))]
    unfold linearImageGaussian
    rw [Measure.map_map hT (measurable_finiteMatrixAction _)]
    rfl
  · ext i j
    have h := congrArg (fun A => A (lift i) (lift j)) (vertexWaveCoefficient_gram m n energy he)
    dsimp only at h
    rw [← vertexBallEmbedding_dist m n (lift i) (lift j),hlift,hlift] at h
    exact h

theorem gaussianTreeProcessLaw_finite_wave_kernel
    (m : ℕ) (energy : ℝ) (he : |energy| < (m+2 : ℝ))
    {J : Type*} [Fintype J] (site : J → RegularTreeVertex (m+2)) :
    HasGaussianCovariance (Measure.map
      (fun x : RegularTreeVertex (m+2) → ℝ => fun j => x (site j))
      (gaussianTreeProcessLaw m energy : Measure _))
      (fun i j => sphericalCovariance (m+2) energy ((regularWordTree (m+2)).dist (site i) (site j))) := by
  obtain ⟨K,hK,L,hL,hGram⟩ := gaussianTreeProcessLaw_finite_waveFactor m energy he site
  letI := hK
  rw [hL,← hGram]
  exact linearImageGaussian_characteristic L

theorem gaussianTreeProcessLaw_invariant (m : ℕ) (energy : ℝ) (he : |energy| < (m+2 : ℝ))
    (e : regularWordTree (m+2) ≃g regularWordTree (m+2)) :
    Measure.map (fun z : RegularTreeVertex (m+2) → ℝ => fun v => z (e v))
      (gaussianTreeProcessLaw m energy : Measure _) = (gaussianTreeProcessLaw m energy : Measure _) := by
  let Q : Measure (RegularTreeVertex (m+2) → ℝ) := gaussianTreeProcessLaw m energy
  let T := fun z : RegularTreeVertex (m+2) → ℝ => fun v => z (e v)
  have hT : Measurable T := measurable_pi_lambda _ (fun _ => measurable_pi_apply _)
  let P := fun S : Finset (RegularTreeVertex (m+2)) => Measure.map S.restrict Q
  letI (S : Finset (RegularTreeVertex (m+2))) : IsProbabilityMeasure (P S) :=
    isProbabilityMeasure_map (Finset.measurable_restrict S).aemeasurable
  have hQ : IsProjectiveLimit Q P := fun _ => rfl
  have hTQ : IsProjectiveLimit (Measure.map T Q) P := by
    intro S
    rw [Measure.map_map (Finset.measurable_restrict S) hT]
    change Measure.map (fun z : RegularTreeVertex (m+2) → ℝ => fun i : S => z (e i.val)) Q =
      Measure.map (fun z : RegularTreeVertex (m+2) → ℝ => fun i : S => z i.val) Q
    letI : IsProbabilityMeasure (Measure.map
        (fun z : RegularTreeVertex (m+2) → ℝ => fun i : S => z (e i.val)) Q) :=
      isProbabilityMeasure_map (measurable_pi_lambda _ (fun _ => measurable_pi_apply _)).aemeasurable
    letI : IsProbabilityMeasure (Measure.map
        (fun z : RegularTreeVertex (m+2) → ℝ => fun i : S => z i.val) Q) :=
      isProbabilityMeasure_map (measurable_pi_lambda _ (fun _ => measurable_pi_apply _)).aemeasurable
    have hL := gaussianTreeProcessLaw_finite_wave_kernel m energy he (fun i : S => e i.val)
    have hR := gaussianTreeProcessLaw_finite_wave_kernel m energy he (fun i : S => i.val)
    have hC : (fun i j : S => sphericalCovariance (m+2) energy
          ((regularWordTree (m+2)).dist (e i.val) (e j.val))) =
        (fun i j : S => sphericalCovariance (m+2) energy
          ((regularWordTree (m+2)).dist i.val j.val)) := by
      funext i j
      rw [regularTreeIso_dist]
    rw [hC] at hL
    apply measure_eq_of_linear_characteristic
    intro t
    exact (hL t).trans (hR t).symm
  exact (hQ.unique hTQ).symm

/-- The actual finite-radius iid Gaussian block rules converge on every
finite window to the constructed infinite Gaussian-wave reference. -/
theorem radialGaussianBlockLaw_weakConverges_to_tree_reference
    (m : ℕ) (hm : 0 < m) (x : ℝ) (hx : |x|<1)
    {J : Type*} [Fintype J] [DecidableEq J] (site : J → RegularTreeVertex (m+2)) :
    WeakLawConverges
      (fun k => Measure.map (fun z : RegularTreeVertex (m+2) → ℝ => fun j => z (site j))
        (radialGaussianBlockLaw (m+2) x k))
      (Measure.map (fun z : RegularTreeVertex (m+2) → ℝ => fun j => z (site j))
        (gaussianTreeProcessLaw m (radialEnergy m x) : Measure _)) := by
  let ν := Measure.map (fun z : RegularTreeVertex (m+2) → ℝ => fun j => z (site j))
    (gaussianTreeProcessLaw m (radialEnergy m x) : Measure _)
  letI : IsProbabilityMeasure ν :=
    isProbabilityMeasure_map (measurable_pi_lambda _ (fun _ => measurable_pi_apply _)).aemeasurable
  have he : 2*Real.sqrt (((m+2 : ℕ) : ℝ)-1)*x = radialEnergy m x := by
    unfold radialEnergy
    norm_num only [Nat.cast_add,Nat.cast_ofNat]
    congr 2
    ring
  have h := radialGaussianBlockLaw_finite_weakConverges_to_gaussian
    (m+2) (by omega) x hx site ν
  rw [he] at h
  exact h (gaussianTreeProcessLaw_finite_wave_kernel m _ (abs_radialEnergy_lt_degree m hx) site)

end GaussianWave.BS
