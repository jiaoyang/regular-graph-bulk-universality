import BourgadeHuang.CMS.SectorialVolterraData

/-! Holomorphic dependence of the actual bounded homogeneous ray coefficients
on the base point, proved by inversion in the Banach algebra of bounded
continuous functions. -/
noncomputable section
open scoped BigOperators Topology BoundedContinuousFunction
open Set Filter
namespace BourgadeHuang.CMS

section BoundedInverse
variable {T : Type*} [TopologicalSpace T]

lemma bounded_inverse_apply {f : T →ᵇ ℂ} (hf : IsUnit f) (t : T) :
    Ring.inverse f t=(f t)⁻¹ := by
  have hh := congrArg (fun g : T →ᵇ ℂ => g t) (Ring.mul_inverse_cancel f hf)
  change f t*Ring.inverse f t=1 at hh
  have hn : f t≠0 := by intro h; simp [h] at hh
  apply mul_left_cancel₀ hn
  rw [hh,mul_inv_cancel₀ hn]

/-- Analytic inverse perturbations are constructed in the actual bounded
function algebra. -/
lemma analyticAt_bounded_inverse_family {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (g h : T →ᵇ ℂ) {δ : E → ℂ} {x : E} (hδ : AnalyticAt ℂ δ x) (hzero : δ x=0) :
    AnalyticAt ℂ (fun y => g*Ring.inverse (1+δ y • h)) x := by
  have hi : AnalyticAt ℂ Ring.inverse (1 : T →ᵇ ℂ) := analyticAt_inverse (1 : (T →ᵇ ℂ)ˣ)
  have hh : AnalyticAt ℂ (fun y => (1 : T →ᵇ ℂ)+δ y • h) x :=
    analyticAt_const.add (hδ.smul analyticAt_const)
  have hx : (1 : T →ᵇ ℂ)+δ x • h=1 := by simp [hzero]
  rw [← hx] at hi
  exact analyticAt_const.mul (hi.comp (f := fun y => (1 : T →ᵇ ℂ)+δ y • h) hh)

lemma eventually_bounded_inverse_family_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (g h : T →ᵇ ℂ) {δ : E → ℂ} {x : E} (hδ : AnalyticAt ℂ δ x) (hzero : δ x=0) :
    ∀ᶠy in 𝓝 x,∀t,(g*Ring.inverse (1+δ y • h)) t=g t*(1+δ y*h t)⁻¹ := by
  have hh : ContinuousAt (fun y => (1 : T →ᵇ ℂ)+δ y • h) x :=
    continuousAt_const.add (hδ.continuousAt.smul continuousAt_const)
  have hx : IsUnit ((1 : T →ᵇ ℂ)+δ x • h) := by simp [hzero]
  filter_upwards [hh.eventually (Units.isOpen.mem_nhds hx)] with y hy
  intro t
  rw [BoundedContinuousFunction.mul_apply,bounded_inverse_apply hy]
  rfl

end BoundedInverse

namespace GapExpression
variable {d : ℕ} (σ : Fin d → Sign) {z : Point d} {R : ℝ}
  (hR : 0<R) (hz : z∈OrderedDomain d) (hsep : ∀i j,i≠j→R≤‖z i-z j‖)

/-- The actual unscaled inverse gap on the entire ray. -/
def boundedRayInverse (i j : Fin d) (hij : i≠j) : Tail R →ᵇ ℂ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun t => ((sectorialRay σ z R t) i-(sectorialRay σ z R t) j)⁻¹)
    (by
      apply Continuous.inv₀
      · change Continuous (fun t : Tail R => z i+((t:ℝ)-R : ℝ)*shiftedDirection σ i-
          (z j+((t:ℝ)-R : ℝ)*shiftedDirection σ j))
        fun_prop
      · intro t
        exact (orderedDomain_collisionFree (sectorialRay_mem σ hz t.property)).sub_ne_zero hij)
    (4/R) (fun t => by
      rw [norm_inv]
      have hh := sectorialRay_separation σ hz hsep t.property i j hij
      have hp : 0<(t:ℝ)/4 := by linarith [t.property]
      calc
        _≤((t:ℝ)/4)⁻¹ := inv_anti₀ hp hh
        _≤(R/4)⁻¹ := inv_anti₀ (by positivity) (by linarith [t.property])
        _=4/R := by field_simp)

/-- The uniformly bounded scaled inverse gap. -/
def boundedScaledRayInverse (i j : Fin d) (hij : i≠j) : Tail R →ᵇ ℂ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun t => (t:ℂ)*((sectorialRay σ z R t) i-(sectorialRay σ z R t) j)⁻¹)
    (by
      have hh := (boundedRayInverse σ hR hz hsep i j hij).continuous
      exact (Complex.continuous_ofReal.comp continuous_subtype_val).mul hh)
    4 (fun t => by
      let a : SquareFreeTerm d := ⟨inverse i j hij,1,∅,Homogeneous.inverse ..⟩
      have hh := a.norm_scaledCoefficient_le (hR.trans_le t.property) (sectorialRay_separation σ hz hsep t.property)
      simpa only [a,SquareFreeTerm.scaledCoefficient,eval,size,pow_one,one_mul] using hh)

include hR hz hsep in
/-- A local analytic family in the supremum norm that agrees with the genuine
scaled inverse gap at every radial parameter. -/
theorem exists_analytic_scaled_inverse_family (i j : Fin d) (hij : i≠j) :
    ∃F : Point d → (Tail R →ᵇ ℂ),AnalyticAt ℂ F z ∧
      ∀ᶠw in 𝓝 z,∀t : Tail R,F w t=
        (t:ℂ)*((sectorialRay σ w R t) i-(sectorialRay σ w R t) j)⁻¹ := by
  let δ : Point d → ℂ := fun w => (w i-w j)-(z i-z j)
  have hδ : AnalyticAt ℂ δ z :=
    (((ContinuousLinearMap.proj (R := ℂ) i).analyticAt z).sub
      ((ContinuousLinearMap.proj (R := ℂ) j).analyticAt z)).sub analyticAt_const
  have hzero : δ z=0 := sub_self _
  let g := boundedScaledRayInverse σ hR hz hsep i j hij
  let h := boundedRayInverse σ hR hz hsep i j hij
  refine ⟨fun w => g*Ring.inverse (1+δ w • h),analyticAt_bounded_inverse_family g h hδ hzero,?_⟩
  filter_upwards [eventually_bounded_inverse_family_apply g h hδ hzero] with w hw
  intro t
  rw [hw t]
  have ha : (sectorialRay σ z R t) i-(sectorialRay σ z R t) j≠0 :=
    (orderedDomain_collisionFree (sectorialRay_mem σ hz t.property)).sub_ne_zero hij
  change ((t:ℂ)*((sectorialRay σ z R t) i-(sectorialRay σ z R t) j)⁻¹)*
      (1+δ w*((sectorialRay σ z R t) i-(sectorialRay σ z R t) j)⁻¹)⁻¹=_
  have he : (sectorialRay σ w R t) i-(sectorialRay σ w R t) j=
      ((sectorialRay σ z R t) i-(sectorialRay σ z R t) j)+δ w := by
    simp only [sectorialRay,shiftedRay,δ]
    ring
  rw [he]
  have hb : 1+δ w*((sectorialRay σ z R t) i-(sectorialRay σ z R t) j)⁻¹=
      (((sectorialRay σ z R t) i-(sectorialRay σ z R t) j)+δ w)*
        ((sectorialRay σ z R t) i-(sectorialRay σ z R t) j)⁻¹ := by field_simp
  rw [hb,mul_inv_rev,inv_inv]
  rw [← mul_assoc,mul_assoc (t:ℂ) _ _,inv_mul_cancel₀ ha,mul_one]


include hR hz hsep in
/-- Every homogeneous rational coefficient has an analytic lift into the
bounded-function Banach algebra. The equality holds uniformly for the whole
half-line on one common neighborhood of the base point. -/
theorem exists_analytic_scaled_eval_family {n : ℕ} {e : GapExpression d} (he : e.Homogeneous n) :
    ∃F : Point d → (Tail R →ᵇ ℂ),AnalyticAt ℂ F z ∧
      ∀ᶠw in 𝓝 z,∀t : Tail R,F w t=(t:ℂ)^n*e.eval (sectorialRay σ w R t) := by
  induction he with
  | const a =>
    exact ⟨fun _ => BoundedContinuousFunction.const _ a,analyticAt_const,
      Filter.Eventually.of_forall (fun w t => by simp [eval])⟩
  | zero n =>
    exact ⟨fun _ => 0,analyticAt_const,Filter.Eventually.of_forall (fun w t => by simp [eval])⟩
  | inverse i j hij =>
    simpa only [pow_one,eval] using exists_analytic_scaled_inverse_family σ hR hz hsep i j hij
  | add he hf ihe ihf =>
    obtain ⟨F,hF,hFeq⟩ := ihe
    obtain ⟨G,hG,hGeq⟩ := ihf
    refine ⟨fun w => F w+G w,hF.add hG,?_⟩
    filter_upwards [hFeq,hGeq] with w hw hv
    intro t
    rw [BoundedContinuousFunction.add_apply,hw t,hv t,eval,mul_add]
  | mul he hf ihe ihf =>
    obtain ⟨F,hF,hFeq⟩ := ihe
    obtain ⟨G,hG,hGeq⟩ := ihf
    refine ⟨fun w => F w*G w,hF.mul hG,?_⟩
    filter_upwards [hFeq,hGeq] with w hw hv
    intro t
    rw [BoundedContinuousFunction.mul_apply,hw t,hv t,eval,pow_add]
    ring

end GapExpression
end BourgadeHuang.CMS
