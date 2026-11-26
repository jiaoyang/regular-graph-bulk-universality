import BourgadeHuang.CMS.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Defs

/-! A finite asymptotic separation criterion for genuine functions.
This is an intermediate general lemma. Its hypotheses have not yet been
verified for every explicit CMS branch and it is not a CMS basis theorem. -/

noncomputable section
open scoped BigOperators Topology
open Filter

namespace BourgadeHuang.CMS

/-- Distinct limiting evaluation functionals separate a finite family.
No independence assertion appears among the hypotheses. -/
theorem linearIndependent_of_asymptotic_duals
    {ι X T : Type*} [Fintype ι] [DecidableEq ι] (l : Filter T) [NeBot l]
    (f : ι → X → ℂ) (ray : ι → T → X) (normalization : ι → T → ℂ)
    (hlimit : ∀ i j, Tendsto
      (fun t => normalization i t * f j (ray i t)) l
      (nhds (if j = i then (1 : ℂ) else 0))) :
    LinearIndependent ℂ f := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  have hzero : ∀ t, (∑ j, c j * (normalization i t * f j (ray i t))) = 0 := by
    intro t
    have heval := congrFun hc (ray i t)
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at heval
    calc
      _ = normalization i t * ∑ j, c j * f j (ray i t) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = 0 := by rw [heval, mul_zero]
  have htend : Tendsto
      (fun t => ∑ j, c j * (normalization i t * f j (ray i t))) l (nhds (c i)) := by
    simpa [mul_ite] using tendsto_finset_sum Finset.univ
      (fun j _ => tendsto_const_nhds.mul (hlimit i j))
  have hconst : Tendsto (fun _ : T => (0 : ℂ)) l (nhds (c i)) := by
    simpa only [hzero] using htend
  exact tendsto_nhds_unique hconst tendsto_const_nhds

end BourgadeHuang.CMS
