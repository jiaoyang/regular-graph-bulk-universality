import BourgadeHuang.CMS.GeneralBranchJets

/-! Genuine differentiation of the scaled analytic jets along shifted rays.
These are derivatives of the solution, not independent formal jet variables. -/
noncomputable section
open scoped BigOperators Topology
namespace BourgadeHuang.CMS

theorem analyticAt_coordinateJet {d n : ℕ} {f : Point d → ℂ} {z : Point d}
    (hf : AnalyticAt ℂ f z) (v : Fin n → Fin d) :
    AnalyticAt ℂ (fun w => coordinateJet n f w v) z := by
  have hA : AnalyticOnNhd ℂ f {w | AnalyticAt ℂ f w} := fun _ hw => hw
  exact ((ContinuousMultilinearMap.apply ℂ (fun _ : Fin n => Point d) ℂ
    (fun k => Pi.single (v k) 1)).analyticAt _).comp (hA.iteratedFDeriv n z hf)

theorem coordDeriv_coordinateJet {d n : ℕ} {f : Point d → ℂ} {z : Point d}
    (hf : AnalyticAt ℂ f z) (v : Fin n → Fin d) (i : Fin d) :
    coordDeriv i (fun w => coordinateJet n f w v) z=
      coordinateJet (n+1) f z (Fin.cons i v) := by
  have hA : AnalyticOnNhd ℂ f {w | AnalyticAt ℂ f w} := fun _ hw => hw
  have hD := (hA.iteratedFDeriv n z hf).differentiableAt.hasFDerivAt
  let ev := ContinuousMultilinearMap.apply ℂ (fun _ : Fin n => Point d) ℂ
    (fun k => Pi.single (v k) 1)
  have hh := (ev.hasFDerivAt.comp z hD).comp_hasDerivAt_of_eq (z i)
    (hasDerivAt_update z i (z i)) (Function.update_eq_self i z).symm
  exact hh.deriv

def complexAffineRay {d : ℕ} (z ω : Point d) (t : ℂ) : Point d :=
  fun j => z j+t*ω j

theorem fderiv_apply_eq_sum_coordDeriv {d : ℕ} {f : Point d → ℂ} {z : Point d}
    (hf : DifferentiableAt ℂ f z) (ω : Point d) :
    fderiv ℂ f z ω=∑j,ω j*coordDeriv j f z := by
  have hω : ω=∑j,ω j • (Pi.single j (1:ℂ) : Point d) := by
    ext k
    simp [Finset.sum_apply,Pi.smul_apply,Pi.single_apply]
  conv_lhs => rw [hω,map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [map_smul,coordDeriv_eq_fderiv hf]
  rfl

theorem hasDerivAt_complexAffineRay {d : ℕ} (z ω : Point d) (t : ℂ) :
    HasDerivAt (complexAffineRay z ω) ω t := by
  simpa only [one_smul] using ((hasDerivAt_id t).smul_const ω).const_add z

theorem hasDerivAt_comp_complexAffineRay {d : ℕ} (z ω : Point d) (t : ℂ)
    {f : Point d → ℂ} (hf : AnalyticAt ℂ f (complexAffineRay z ω t)) :
    HasDerivAt (fun r => f (complexAffineRay z ω r))
      (∑j,ω j*coordDeriv j f (complexAffineRay z ω t)) t := by
  rw [← fderiv_apply_eq_sum_coordDeriv hf.differentiableAt]
  exact hf.differentiableAt.hasFDerivAt.comp_hasDerivAt t (hasDerivAt_complexAffineRay z ω t)

/-- Exact unscaled jet derivative in any fixed complex ray direction. -/
theorem hasDerivAt_coordinateJet_ray {d n : ℕ} (z ω : Point d) (t : ℂ)
    {f : Point d → ℂ} (hf : AnalyticAt ℂ f (complexAffineRay z ω t)) (v : Fin n → Fin d) :
    HasDerivAt (fun r => coordinateJet n f (complexAffineRay z ω r) v)
      (∑j,ω j*coordinateJet (n+1) f (complexAffineRay z ω t) (Fin.cons j v)) t := by
  simpa only [coordDeriv_coordinateJet hf] using
    hasDerivAt_comp_complexAffineRay z ω t (analyticAt_coordinateJet hf v)

/-- The scaled radial jet and its actual derivative; this is the unreduced
identity underlying the finite square-free radial system. -/
def scaledRadialJet {d n : ℕ} (f : Point d → ℂ) (z ω : Point d)
    (v : Fin n → Fin d) (t : ℂ) : ℂ := t^n*coordinateJet n f (complexAffineRay z ω t) v

theorem hasDerivAt_scaledRadialJet {d n : ℕ} (z ω : Point d) {t : ℂ}
    (ht : t≠0) {f : Point d → ℂ} (hf : AnalyticAt ℂ f (complexAffineRay z ω t))
    (v : Fin n → Fin d) :
    HasDerivAt (scaledRadialJet f z ω v)
      ((n:ℂ)/t*scaledRadialJet f z ω v t+
        t^n*∑j,ω j*coordinateJet (n+1) f (complexAffineRay z ω t) (Fin.cons j v)) t := by
  have hh := (hasDerivAt_pow n t).mul (hasDerivAt_coordinateJet_ray z ω t hf v)
  convert hh using 1
  unfold scaledRadialJet
  by_cases hn : n=0
  · subst n
    simp
  · have hn' : n-1+1=n := Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hn)
    have hpow : t^n/t=t^(n-1) := by
      nth_rw 1 [← hn']
      rw [pow_succ,mul_div_cancel_right₀ _ ht]
    rw [show (n:ℂ)/t*(t^n*coordinateJet n f (complexAffineRay z ω t) v)=
      (n:ℂ)*(t^n/t)*coordinateJet n f (complexAffineRay z ω t) v by ring,hpow]

/-- The same checked derivative along the actual real radial parameter. -/
theorem hasDerivAt_scaledRadialJet_real {d n : ℕ} (z ω : Point d) {t : ℝ}
    (ht : t≠0) {f : Point d → ℂ} (hf : AnalyticAt ℂ f (complexAffineRay z ω (t:ℂ)))
    (v : Fin n → Fin d) :
    HasDerivAt (fun r : ℝ => scaledRadialJet f z ω v r)
      ((n:ℂ)/(t:ℂ)*scaledRadialJet f z ω v t+
        (t:ℂ)^n*∑j,ω j*coordinateJet (n+1) f (complexAffineRay z ω t) (Fin.cons j v)) t :=
  (hasDerivAt_scaledRadialJet z ω (Complex.ofReal_ne_zero.mpr ht) hf v).comp_ofReal

end BourgadeHuang.CMS
