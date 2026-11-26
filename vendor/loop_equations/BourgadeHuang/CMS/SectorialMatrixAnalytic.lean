import BourgadeHuang.CMS.SectorialCoefficientAnalytic

/-! Analytic Banach-space lifts of the actual radial matrix entries. -/
noncomputable section
open scoped BigOperators Topology BoundedContinuousFunction
open Set Filter
namespace BourgadeHuang.CMS

lemma exists_analytic_bounded_sum {ι E T : Type*} [Fintype ι]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [TopologicalSpace T]
    (f : ι → E → T → ℂ) {z : E}
    (h : ∀i,∃F : E → (T →ᵇ ℂ),AnalyticAt ℂ F z ∧ ∀ᶠw in 𝓝 z,∀t,F w t=f i w t) :
    ∃F : E → (T →ᵇ ℂ),AnalyticAt ℂ F z ∧ ∀ᶠw in 𝓝 z,∀t,F w t=∑i,f i w t := by
  classical
  choose F hF hEq using h
  refine ⟨fun w => ∑i,F i w,Finset.univ.analyticAt_sum (fun i _ => hF i),?_⟩
  filter_upwards [Filter.eventually_all.mpr hEq] with w hw
  intro t
  simp only [BoundedContinuousFunction.sum_apply,hw]

namespace SquareFreeTerm
variable {d : ℕ} (σ : Fin d → Sign) {z : Point d} {R : ℝ}
  (hR : 0<R) (hz : z∈OrderedDomain d) (hsep : ∀i j,i≠j→R≤‖z i-z j‖)

include hR hz hsep in
theorem exists_analytic_homogeneousEntry_family (ts : List (SquareFreeTerm d))
    (n : ℕ) (T : Finset (Fin d)) :
    ∃F : Point d → (Tail R →ᵇ ℂ),AnalyticAt ℂ F z ∧
      ∀ᶠw in 𝓝 z,∀t : Tail R,F w t=homogeneousEntry ts n T (sectorialRay σ w R t) (t:ℝ) := by
  induction ts with
  | nil => exact ⟨fun _ => 0,analyticAt_const,Filter.Eventually.of_forall (fun _ _ => rfl)⟩
  | cons a ts ih =>
    obtain ⟨G,hG,hGeq⟩ := ih
    by_cases ha : a.target=T ∧ a.weight+a.target.card=n
    · obtain ⟨F,hF,hFeq⟩ := GapExpression.exists_analytic_scaled_eval_family σ hR hz hsep a.homogeneous
      refine ⟨fun w => F w+G w,hF.add hG,?_⟩
      filter_upwards [hFeq,hGeq] with w hw hv
      intro t
      rw [BoundedContinuousFunction.add_apply,hw t,hv t]
      simp only [homogeneousEntry,List.map_cons,List.sum_cons,if_pos ha,scaledCoefficient]
    · refine ⟨G,hG,?_⟩
      filter_upwards [hGeq] with w hw
      intro t
      rw [hw t]
      simp only [homogeneousEntry,List.map_cons,List.sum_cons,if_neg ha,zero_add]

end SquareFreeTerm

namespace SectorialData
variable {d : ℕ} (D : SectorialData d) (σ : Fin d → Sign) {z : Point d} {R : ℝ}
  (hR : 0<R) (hz : z∈OrderedDomain d) (hsep : ∀i j,i≠j→R≤‖z i-z j‖)

include hR hz hsep in
theorem exists_analytic_lowCoordinate_family (ω : Point d) (S T : Finset (Fin d)) (i : Fin d) :
    ∃F : Point d → (Tail R →ᵇ ℂ),AnalyticAt ℂ F z ∧
      ∀ᶠw in 𝓝 z,∀t : Tail R,F w t=D.lowCoordinate ω (sectorialRay σ w R t) (t:ℝ) S T i := by
  by_cases hi : i∈S
  · obtain ⟨F,hF,hEq⟩ := SquareFreeTerm.exists_analytic_homogeneousEntry_family σ hR hz hsep
      (D.correctionRow S i) S.card T
    refine ⟨fun w => -(ω i) • F w,(analyticAt_const (v := -(ω i))).smul hF,?_⟩
    filter_upwards [hEq] with w hw
    intro t
    rw [BoundedContinuousFunction.smul_apply,hw t]
    simp only [lowCoordinate,if_pos hi,smul_eq_mul]
  · exact ⟨fun _ => 0,analyticAt_const,Filter.Eventually.of_forall (fun w t => by simp [lowCoordinate,hi])⟩

include hR hz hsep in
theorem exists_analytic_highCoordinate_family (ω : Point d) (S T : Finset (Fin d)) (i : Fin d) :
    ∃F : Point d → (Tail R →ᵇ ℂ),AnalyticAt ℂ F z ∧
      ∀ᶠw in 𝓝 z,∀t : Tail R,F w t=D.highCoordinate ω (sectorialRay σ w R t) (t:ℝ) S T i := by
  by_cases hi : i∈S
  · obtain ⟨F,hF,hEq⟩ := SquareFreeTerm.exists_analytic_homogeneousEntry_family σ hR hz hsep
      (D.correctionRow S i) (S.card+1) T
    refine ⟨fun w => -(ω i) • F w,(analyticAt_const (v := -(ω i))).smul hF,?_⟩
    filter_upwards [hEq] with w hw
    intro t
    rw [BoundedContinuousFunction.smul_apply,hw t]
    simp only [highCoordinate,if_pos hi,smul_eq_mul]
  · exact ⟨fun _ => BoundedContinuousFunction.const _ (if T=insert i S then ω i else 0),
      analyticAt_const,Filter.Eventually.of_forall (fun w t => by simp [highCoordinate,hi])⟩

include hR hz hsep in
/-- Supremum-norm holomorphy of the actual bounded triangular entries. -/
theorem exists_analytic_principalRemainder_family (ω : Point d) (S T : Finset (Fin d)) :
    ∃F : Point d → (Tail R →ᵇ ℂ),AnalyticAt ℂ F z ∧
      ∀ᶠw in 𝓝 z,∀t : Tail R,F w t=D.principalRemainder ω (sectorialRay σ w R t) (t:ℝ) S T :=
  exists_analytic_bounded_sum _ (D.exists_analytic_lowCoordinate_family σ hR hz hsep ω S T)

include hR hz hsep in
/-- Supremum-norm holomorphy of every reciprocal radial entry. -/
theorem exists_analytic_radialRemainder_family (ω : Point d) (S T : Finset (Fin d)) :
    ∃F : Point d → (Tail R →ᵇ ℂ),AnalyticAt ℂ F z ∧
      ∀ᶠw in 𝓝 z,∀t : Tail R,F w t=D.radialRemainder ω (sectorialRay σ w R t) (t:ℝ) S T := by
  obtain ⟨F,hF,hEq⟩ := exists_analytic_bounded_sum _
    (D.exists_analytic_highCoordinate_family σ hR hz hsep ω S T)
  refine ⟨fun w => BoundedContinuousFunction.const _ (if T=S then (S.card:ℂ) else 0)+F w,
    analyticAt_const.add hF,?_⟩
  filter_upwards [hEq] with w hw
  intro t
  rw [BoundedContinuousFunction.add_apply,hw t]
  rfl

end SectorialData
end BourgadeHuang.CMS
