import GaussianWave.BS.ProcessSecondMomentCompactness
import GaussianWave.BS.RegularTree

/-! Joint tree eigenrelations survive actual weak process limits. Only
coordinate L2 control and genuine vanishing residuals are used; Gaussianity
and preservation of the source variance are not assumed. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology BigOperators Classical
namespace GaussianWave.BS

/-- The actual finite-neighbor eigen-equation residual at one channel/site. -/
def treeEigenResidual (d r : ℕ) (energy : Fin r → ℝ) (a : Fin r) (u : RegularTreeVertex d)
    (x : (Fin r × RegularTreeVertex d) → ℝ) : ℝ :=
  (∑ z : (regularWordTree d).neighborSet u, x (a,z.val))-energy a*x (a,u)

theorem continuous_treeEigenResidual (d r : ℕ) (energy : Fin r → ℝ)
    (a : Fin r) (u : RegularTreeVertex d) : Continuous (treeEigenResidual d r energy a u) := by
  apply Continuous.sub
  · exact continuous_finset_sum _ (fun z hz => continuous_apply (a,z.val))
  · exact continuous_const.mul (continuous_apply (a,u))

/-- The residual commutes with every actual tree isomorphism; neighbor-set
reindexing, rather than any port-ordering assumption, proves the identity. -/
theorem treeEigenResidual_equivariant (d r : ℕ) (energy : Fin r → ℝ)
    (a : Fin r) (u : RegularTreeVertex d) (e : regularWordTree d ≃g regularWordTree d)
    (x : (Fin r × RegularTreeVertex d) → ℝ) :
    treeEigenResidual d r energy a u (fun av => x (av.1,e av.2))=
      treeEigenResidual d r energy a (e u) x := by
  unfold treeEigenResidual
  congr 1
  exact Equiv.sum_comp (e.mapNeighborSet u) (fun z => x (a,z.val))

/-- Square-integrability of every actual finite linear residual follows
from the coordinate second moments; no residual integrability is an input. -/
theorem integrable_treeEigenResidual_sq (d r : ℕ) (μ : Measure ((Fin r × RegularTreeVertex d) → ℝ))
    (hi : ∀ av, Integrable (fun x => x av^2) μ) (energy : Fin r → ℝ)
    (a : Fin r) (u : RegularTreeVertex d) : Integrable (fun x => treeEigenResidual d r energy a u x^2) μ := by
  have hcoord (av : Fin r × RegularTreeVertex d) : MemLp (fun x => x av) 2 μ :=
    (memLp_two_iff_integrable_sq (measurable_pi_apply av).aestronglyMeasurable).2 (hi av)
  have hsum := memLp_finset_sum (Finset.univ : Finset ((regularWordTree d).neighborSet u))
    (fun z hz => hcoord (a,z.val))
  have hmem := hsum.sub ((hcoord (a,u)).const_mul (energy a))
  exact (memLp_two_iff_integrable_sq (continuous_treeEigenResidual d r energy a u).aestronglyMeasurable).1 hmem

/-- Actual approximate joint eigenrelations, with convergent channel
energies, pass to a whole-process weak limit from coordinate L2 bounds. -/
theorem weak_process_eigenrelations_of_residual_second
    (d r : ℕ) (μ : ℕ → Measure ((Fin r × RegularTreeVertex d) → ℝ))
    [∀ n, IsProbabilityMeasure (μ n)] (ν : Measure ((Fin r × RegularTreeVertex d) → ℝ))
    [IsProbabilityMeasure ν] (hweak : WeakLawConverges μ ν)
    (energies : ℕ → Fin r → ℝ) (energy : Fin r → ℝ)
    (henergies : ∀ a, Tendsto (fun n => energies n a) atTop (𝓝 (energy a)))
    (hi : ∀ n av, Integrable (fun x => x av^2) (μ n))
    (M : (Fin r × RegularTreeVertex d) → ℝ)
    (hM : ∀ n av, (∫ x, x av^2 ∂μ n)≤M av)
    (hres : ∀ a u, Tendsto (fun n => ∫ x, treeEigenResidual d r (energies n) a u x^2 ∂μ n) atTop (𝓝 0)) :
    ∀ᵐ x ∂ν, ∀ a u, treeEigenResidual d r energy a u x=0 := by
  apply ae_all_iff.mpr
  intro a
  apply ae_all_iff.mpr
  intro u
  have hir (n : ℕ) := integrable_treeEigenResidual_sq d r (μ n) (hi n) energy a u
  have hie (n : ℕ) := integrable_treeEigenResidual_sq d r (μ n) (hi n) (energies n) a u
  have hbound (n : ℕ) : (∫ x, treeEigenResidual d r energy a u x^2 ∂μ n) ≤
      2*(∫ x, treeEigenResidual d r (energies n) a u x^2 ∂μ n)+
        2*(energies n a-energy a)^2*M (a,u) := by
    have hpoint (x) : treeEigenResidual d r energy a u x^2 ≤
        2*treeEigenResidual d r (energies n) a u x^2+2*(energies n a-energy a)^2*x (a,u)^2 := by
      have he : treeEigenResidual d r energy a u x=
          treeEigenResidual d r (energies n) a u x+(energies n a-energy a)*x (a,u) := by
        unfold treeEigenResidual
        ring
      rw [he]
      nlinarith [sq_nonneg (treeEigenResidual d r (energies n) a u x-(energies n a-energy a)*x (a,u))]
    have hh := integral_mono (hir n)
      ((hie n).const_mul 2 |>.add ((hi n (a,u)).const_mul (2*(energies n a-energy a)^2))) hpoint
    dsimp only [Pi.add_apply] at hh
    rw [integral_add ((hie n).const_mul 2) ((hi n (a,u)).const_mul _),integral_const_mul,integral_const_mul] at hh
    have hm := mul_le_mul_of_nonneg_left (hM n (a,u)) (show 0≤2*(energies n a-energy a)^2 by positivity)
    linarith
  have hzero : Tendsto (fun n => ∫ x, treeEigenResidual d r energy a u x^2 ∂μ n) atTop (𝓝 0) := by
    have hdiff := ((henergies a).sub_const (energy a)).pow 2
    simp only [sub_self,zero_pow (by norm_num : (2 : ℕ) ≠ 0)] at hdiff
    have hlim := ((hres a u).const_mul 2).add (hdiff.mul_const (2*M (a,u)))
    simp only [mul_zero,zero_mul,zero_add] at hlim
    apply squeeze_zero (fun n => integral_nonneg (fun x => sq_nonneg _)) hbound
    convert hlim using 1
    funext n
    ring
  exact weak_limit_zero_of_residual_second μ ν hweak (treeEigenResidual d r energy a u)
    (continuous_treeEigenResidual d r energy a u) hir hzero

/-- Exact channelwise eigenvectors are the zero-residual specialization;
only convergence of their energies and coordinate L2 control are needed. -/
theorem weak_process_eigenrelations_of_exact
    (d r : ℕ) (μ : ℕ → Measure ((Fin r × RegularTreeVertex d) → ℝ))
    [∀ n, IsProbabilityMeasure (μ n)] (ν : Measure ((Fin r × RegularTreeVertex d) → ℝ))
    [IsProbabilityMeasure ν] (hweak : WeakLawConverges μ ν)
    (energies : ℕ → Fin r → ℝ) (energy : Fin r → ℝ)
    (henergies : ∀ a, Tendsto (fun n => energies n a) atTop (𝓝 (energy a)))
    (hi : ∀ n av, Integrable (fun x => x av^2) (μ n))
    (M : (Fin r × RegularTreeVertex d) → ℝ)
    (hM : ∀ n av, (∫ x, x av^2 ∂μ n)≤M av)
    (hexact : ∀ n, ∀ᵐ x ∂μ n, ∀ a u, treeEigenResidual d r (energies n) a u x=0) :
    ∀ᵐ x ∂ν, ∀ a u, treeEigenResidual d r energy a u x=0 := by
  apply weak_process_eigenrelations_of_residual_second d r μ ν hweak energies energy henergies hi M hM
  intro a u
  have he (n : ℕ) : (∫ x, treeEigenResidual d r (energies n) a u x^2 ∂μ n)=0 := by
    calc
      _ = ∫ x, (0 : ℝ) ∂μ n := by
        apply integral_congr_ae
        filter_upwards [hexact n] with x hx
        rw [hx a u,zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
      _=0 := by simp
  simpa only [he] using tendsto_const_nhds

end GaussianWave.BS
