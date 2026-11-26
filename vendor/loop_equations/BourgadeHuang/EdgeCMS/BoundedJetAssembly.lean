import BourgadeHuang.CMS.SectorialRadialSystem
import Mathlib.Analysis.Complex.Liouville

/-! Actual Cauchy estimates for the square-free jets of bounded analytic
functions.  The estimates apply uniformly to a family of dilated functions;
no bounds on derivatives are included among the hypotheses. -/
noncomputable section
open Set Filter
open scoped Topology BigOperators
namespace BourgadeHuang.EdgeCMS
open CMS

def wordCauchyBound (M r : ℝ) : ℕ → ℝ
  | 0 => M
  | n+1 => wordCauchyBound M (r/2) n / (r/2)

theorem wordCauchyBound_nonneg {M r : ℝ} (hM : 0≤M) (hr : 0<r) (n : ℕ) :
    0≤wordCauchyBound M r n := by
  induction n generalizing r with
  | zero => exact hM
  | succ n ih => exact div_nonneg (ih (by positivity)) (by positivity)

private theorem dist_update_self_le {d : ℕ} (z : Point d) (i : Fin d) (w : ℂ) :
    dist (Function.update z i w) z ≤ dist w (z i) := by
  rw [dist_pi_le_iff (dist_nonneg)]
  intro j
  by_cases hj : j=i
  · subst j
    simp
  · simpa [Function.update_of_ne hj] using (dist_nonneg : 0≤dist w (z i))

private theorem analyticAt_slice {d : ℕ} {f : Point d → ℂ} (z : Point d)
    (i : Fin d) (w : ℂ) (hf : AnalyticAt ℂ f (Function.update z i w)) :
    AnalyticAt ℂ (fun v => f (Function.update z i v)) w := by
  apply hf.comp
  apply analyticAt_pi_iff.mpr
  intro j
  by_cases hj : j=i
  · subst j
    simpa using (analyticAt_id : AnalyticAt ℂ (fun v : ℂ => v) w)
  · simpa [Function.update_of_ne hj] using
      (analyticAt_const : AnalyticAt ℂ (fun _ : ℂ => z j) w)

/-- Cauchy's one-variable estimate on an actual coordinate slice. -/
theorem norm_coordDeriv_le_of_ball_bound {d : ℕ} {f : Point d → ℂ}
    {z : Point d} {r M : ℝ} (hr : 0<r)
    (hf : ∀x∈Metric.closedBall z r, AnalyticAt ℂ f x)
    (hb : ∀x∈Metric.closedBall z r, ‖f x‖≤M) (i : Fin d) :
    ‖coordDeriv i f z‖ ≤ M/r := by
  let g := fun w : ℂ => f (Function.update z i w)
  have hmem {w : ℂ} (hw : w∈Metric.closedBall (z i) r) :
      Function.update z i w∈Metric.closedBall z r :=
    (dist_update_self_le z i w).trans hw
  have hg : DiffContOnCl ℂ g (Metric.ball (z i) r) := by
    apply DifferentiableOn.diffContOnCl_ball (U:=Metric.closedBall (z i) r) _ (Subset.refl _)
    intro w hw
    exact (analyticAt_slice z i w (hf _ (hmem hw))).differentiableAt.differentiableWithinAt
  exact Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hr hg
    (fun w hw => hb _ (hmem (Metric.sphere_subset_closedBall hw)))

/-- Uniform bounds of all genuine coordinate-word derivatives follow solely
from a scalar holomorphic bound on a ball. -/
theorem norm_wordDerivative_le_of_ball_bound {d : ℕ} (v : List (Fin d))
    {f : Point d → ℂ} {z : Point d} {r M : ℝ} (hr : 0<r)
    (hf : AnalyticOnNhd ℂ f (Metric.ball z r))
    (hb : ∀x∈Metric.ball z r, ‖f x‖≤M) :
    ‖wordDerivative v f z‖ ≤ wordCauchyBound M r v.length := by
  induction v generalizing z r with
  | nil => exact hb z (Metric.mem_ball_self hr)
  | cons i v ih =>
    have hr2 : 0<r/2 := by positivity
    have hsub {x : Point d} (hx : x∈Metric.closedBall z (r/2)) :
        Metric.ball x (r/2) ⊆ Metric.ball z r := by
      intro y hy
      calc
        dist y z ≤ dist y x + dist x z := dist_triangle _ _ _
        _ < r/2+r/2 := add_lt_add_of_lt_of_le hy hx
        _ = r := by ring
    have hax {x : Point d} (hx : x∈Metric.closedBall z (r/2)) : x∈Metric.ball z r := by
      exact (Metric.mem_closedBall.mp hx).trans_lt (by linarith)
    exact norm_coordDeriv_le_of_ball_bound hr2
      (fun x hx => analyticAt_wordDerivative v (hf x (hax hx)))
      (fun x hx => ih hr2 (hf.mono (hsub hx)) (fun y hy => hb y (hsub hx hy))) i

private theorem coordDeriv_dilation {d : ℕ} {f : Point d → ℂ}
    {z : Point d} (a : ℂ) (hf : AnalyticAt ℂ f (a•z)) (i : Fin d) :
    coordDeriv i (fun w => f (a•w)) z=a*coordDeriv i f (a•z) := by
  have hz : a•Function.update z i (z i)=a•z := by simp
  have hd' := hf.differentiableAt.hasFDerivAt.comp_hasDerivAt_of_eq (z i)
    (((hasDerivAt_update z i (z i)).const_smul a)) hz.symm
  rw [coordDeriv_eq_fderiv hf.differentiableAt]
  simpa only [Function.comp_def,ContinuousLinearMap.map_smul,smul_eq_mul] using hd'.deriv

/-- Exact dilation chain rule for actual coordinate words. -/
theorem wordDerivative_dilation {d : ℕ} (v : List (Fin d)) {f : Point d → ℂ}
    {z : Point d} (a : ℂ) (hf : AnalyticAt ℂ f (a•z)) :
    wordDerivative v (fun w => f (a•w)) z=a^v.length*wordDerivative v f (a•z) := by
  induction v generalizing z with
  | nil => simp [wordDerivative]
  | cons i v ih =>
    have hc : Continuous (fun w : Point d => a•w) := continuous_const.smul continuous_id
    have he : wordDerivative v (fun w => f (a•w)) =ᶠ[𝓝 z]
        fun w => a^v.length*wordDerivative v f (a•w) := by
      filter_upwards [hc.continuousAt.preimage_mem_nhds hf.eventually_analyticAt] with w hw
      exact ih hw
    change coordDeriv i (wordDerivative v (fun w => f (a•w))) z=_
    rw [coordDeriv_congr_nhds he]
    have haw : AnalyticAt ℂ (fun w => wordDerivative v f (a•w)) z :=
      (analyticAt_wordDerivative v hf).comp
        ((analyticAt_id : AnalyticAt ℂ (fun w : Point d => w) z).const_smul (c:=a))
    change coordDeriv i (a^v.length • (fun w => wordDerivative v f (a•w))) z = _
    rw [coordDeriv_smul_analytic haw (a^v.length) i,
      coordDeriv_dilation a (analyticAt_wordDerivative v hf) i]
    simp only [List.length_cons,pow_succ,wordDerivative,smul_eq_mul]
    ring

/-- A bounded analytic function on every dilation of one fixed ball has
uniformly bounded actual scaled square-free jets along its central ray. -/
theorem norm_scaledSquareFree_le_of_dilation_ball_bound {d : ℕ}
    (S : Finset (Fin d)) {f : Point d → ℂ} {z : Point d} {r M : ℝ}
    (hr : 0<r) (t : ℝ)
    (hf : ∀w∈Metric.ball z r, AnalyticAt ℂ f ((t:ℂ)•w))
    (hb : ∀w∈Metric.ball z r, ‖f ((t:ℂ)•w)‖≤M) :
    ‖scaledSquareFree S f ((t:ℂ)•z) t‖≤wordCauchyBound M r S.card := by
  have ha : AnalyticOnNhd ℂ (fun w => f ((t:ℂ)•w)) (Metric.ball z r) := by
    intro w hw
    exact (hf w hw).comp
      ((analyticAt_id : AnalyticAt ℂ (fun w : Point d => w) w).const_smul (c:=(t:ℂ)))
  have h := norm_wordDerivative_le_of_ball_bound S.toList hr ha hb
  rw [wordDerivative_dilation S.toList (t:ℂ) (hf z (Metric.mem_ball_self hr))] at h
  simpa only [Finset.length_toList,scaledSquareFree,squareFreeDerivative] using h

/-- A neighborhood bound, as furnished by the actual normalized observable
estimate, already yields every bounded radial derivative required by the ODE. -/
theorem exists_scaledSquareFree_bound_of_dilation_nhds {d : ℕ}
    (S : Finset (Fin d)) {f : Point d → ℂ} {z : Point d}
    {U : Set (Point d)} (hU : U∈𝓝 z) {M : ℝ}
    (hf : ∀t : ℝ, 0<t → ∀w∈U, AnalyticAt ℂ f ((t:ℂ)•w))
    (hb : ∀t : ℝ, 0<t → ∀w∈U, ‖f ((t:ℂ)•w)‖≤M) :
    ∃B : ℝ, 0<B ∧ ∀t : ℝ, 0<t → ‖scaledSquareFree S f ((t:ℂ)•z) t‖≤B := by
  obtain ⟨r,hr,hsub⟩ := Metric.mem_nhds_iff.mp hU
  refine ⟨|wordCauchyBound M r S.card|+1, by positivity, ?_⟩
  intro t ht
  exact (norm_scaledSquareFree_le_of_dilation_ball_bound S hr t
    (fun w hw => hf t ht w (hsub hw)) (fun w hw => hb t ht w (hsub hw))).trans
    ((le_abs_self _).trans (by linarith))

end BourgadeHuang.EdgeCMS
