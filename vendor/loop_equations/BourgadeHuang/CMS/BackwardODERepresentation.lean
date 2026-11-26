import BourgadeHuang.CMS.FreeVolterraODE

/-! A bounded solution of the unstable forward diagonal ODE is necessarily
its actual backward improper integral. This is the reverse implication needed
for uniqueness of normalized radial families. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology BoundedContinuousFunction
namespace BourgadeHuang.CMS
set_option maxHeartbeats 800000

private theorem norm_exp_shift (lam : ℂ) (t s : ℝ) :
    ‖Complex.exp (-lam*((s-t:ℝ):ℂ))‖=Real.exp (-lam.re*(s-t)) := by
  rw [Complex.norm_exp]
  congr 1
  simp

/-- The terminal boundary term really vanishes: positive real part of the
exponent defeats every bounded solution. -/
theorem tendsto_exp_shift_mul_bounded_zero (lam : ℂ) (hlam : 0<lam.re)
    (Y : ℝ →ᵇ ℂ) (t : ℝ) :
    Tendsto (fun s : ℝ => Complex.exp (-lam*((s-t:ℝ):ℂ))*Y s) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have hsub : Tendsto (fun s : ℝ => s-t) atTop atTop := by
    apply tendsto_atTop.mpr
    intro b
    filter_upwards [eventually_ge_atTop (b+t)] with s hs
    linarith
  have he : Tendsto (fun s : ℝ => Real.exp (-(lam.re*(s-t)))) atTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp (hsub.const_mul_atTop hlam)
  have hb : Tendsto (fun s : ℝ => Real.exp (-lam.re*(s-t))*‖Y‖) atTop (𝓝 0) := by
    simpa only [neg_mul,zero_mul] using he.mul_const ‖Y‖
  apply squeeze_zero (fun _ => norm_nonneg _) _ hb
  intro s
  rw [norm_mul,norm_exp_shift]
  exact mul_le_mul_of_nonneg_left (Y.norm_coe_le_norm s) (Real.exp_pos _).le

/-- Bounded forcing is integrable against the actual decaying kernel. -/
theorem integrable_exp_shift_mul_bounded (lam : ℂ) (hlam : 0<lam.re)
    (f : ℝ →ᵇ ℂ) (t : ℝ) :
    IntegrableOn (fun s : ℝ => Complex.exp (-lam*((s-t:ℝ):ℂ))*f s) (Ioi t) := by
  apply ((integrableOn_exp_mul_Ioi (neg_neg_of_pos hlam) t).const_mul
    (Real.exp (lam.re*t)*‖f‖)).mono'
  · exact (by fun_prop : Continuous (fun s : ℝ => Complex.exp (-lam*((s-t:ℝ):ℂ))*f s)).aestronglyMeasurable
  · apply Filter.Eventually.of_forall
    intro s
    rw [norm_mul,norm_exp_shift]
    calc
      _≤Real.exp (-lam.re*(s-t))*‖f‖ :=
        mul_le_mul_of_nonneg_left (f.norm_coe_le_norm s) (Real.exp_pos _).le
      _=(Real.exp (lam.re*t)*‖f‖)*Real.exp (-lam.re*s) := by
        rw [show -lam.re*(s-t)=lam.re*t+ -lam.re*s by ring,Real.exp_add]
        ring

/-- Reverse variation of constants, derived by FTC on the infinite interval. -/
theorem bounded_solution_eq_backward_integral (lam : ℂ) (hlam : 0<lam.re)
    (Y f : ℝ →ᵇ ℂ) {R : ℝ}
    (hY : ∀s,R<s → HasDerivAt Y (lam*Y s+f s) s)
    {t : ℝ} (ht : R≤t) :
    Y t=-(∫s in Ioi t,Complex.exp (-lam*((s-t:ℝ):ℂ))*f s) := by
  have hd (s : ℝ) (hs : s∈Ioi t) :
      HasDerivAt (fun u : ℝ => Complex.exp (-lam*((u-t:ℝ):ℂ))*Y u)
        (Complex.exp (-lam*((s-t:ℝ):ℂ))*f s) s := by
    have he := ((((hasDerivAt_id s).sub_const t).ofReal_comp).const_mul (-lam)).cexp
    convert he.mul (hY s (ht.trans_lt hs)) using 1
    simp only [id_eq,Complex.ofReal_one,mul_one]
    ring
  have hcont : Continuous (fun u : ℝ => Complex.exp (-lam*((u-t:ℝ):ℂ))*Y u) := by fun_prop
  have hh := integral_Ioi_of_hasDerivAt_of_tendsto hcont.continuousAt.continuousWithinAt hd
    (integrable_exp_shift_mul_bounded lam hlam f t)
    (tendsto_exp_shift_mul_bounded_zero lam hlam Y t)
  simp only [sub_self,Complex.ofReal_zero,mul_zero,Complex.exp_zero,one_mul,zero_sub] at hh
  simpa only [neg_neg] using (congrArg Neg.neg hh).symm

/-- Vector-valued reverse variation of constants for the genuine diagonal
operator. -/
theorem bounded_vector_solution_eq_freeBackward
    {J : Type*} [Fintype J] [DecidableEq J] {a : ℝ} (ha : 0<a)
    (lam : J → ℂ) (hlam : ∀i,a≤(lam i).re) (Y f : ℝ →ᵇ (J → ℂ)) {R : ℝ}
    (hY : ∀s,R<s → HasDerivAt Y (complexDiagonalOperator lam (Y s)+f s) s)
    {t : ℝ} (ht : R≤t) : Y t=freeBackwardTail lam f t := by
  have hlam' : ∀i,2*(a/2)≤(lam i).re := by intro i; linarith [hlam i]
  have hi := integrable_principalOperator_tail (R:=t) (half_pos ha) lam
    (0 : Tail t →ᵇ (J → J → ℂ)) 1 hlam' f
  simp only [principalOperator_zero] at hi
  ext i
  let Yi : ℝ →ᵇ ℂ := (ContinuousLinearMap.proj (R:=ℂ) i).compLeftContinuousBounded ℝ Y
  let fi : ℝ →ᵇ ℂ := (ContinuousLinearMap.proj (R:=ℂ) i).compLeftContinuousBounded ℝ f
  have hdi (s : ℝ) (hs : R<s) : HasDerivAt Yi (lam i*Yi s+fi s) s := by
    have hd := (ContinuousLinearMap.proj (R:=ℝ) i).hasFDerivAt.comp_hasDerivAt s (hY s hs)
    exact hd
  have hh := bounded_solution_eq_backward_integral (lam i) (ha.trans_le (hlam i)) Yi fi hdi ht
  change Y t i=-(∫s in Ioi t,Complex.exp (-lam i*((s-t:ℝ):ℂ))*f s i) at hh
  rw [hh]
  unfold freeBackwardTail
  change -(∫s in Ioi t,Complex.exp (-lam i*((s-t:ℝ):ℂ))*f s i)=
    -(∫s in Ioi t,freeDiagonalEvolution lam (s-t) (f s)) i
  exact congrArg Neg.neg ((ContinuousLinearMap.proj (R:=ℝ) i).integral_comp_comm hi)

/-- The empty component is recovered from its terminal value by the actual
improper integral whenever its derivative is integrable. -/
theorem solution_eq_terminal_tail {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (Y f : ℝ →ᵇ E) (e : E) {R : ℝ}
    (hY : ∀s,R<s → HasDerivAt Y (f s) s) (hi : IntegrableOn f (Ioi R))
    (hlim : Tendsto Y atTop (𝓝 e)) {t : ℝ} (ht : R≤t) :
    Y t=e-∫s in Ioi t,f s := by
  have hh := integral_Ioi_of_hasDerivAt_of_tendsto Y.continuous.continuousAt.continuousWithinAt
    (fun s hs => hY s (ht.trans_lt hs)) (hi.mono_set (Ioi_subset_Ioi ht)) hlim
  exact eq_sub_iff_add_eq.mpr (by rw [hh]; abel)

end BourgadeHuang.CMS
