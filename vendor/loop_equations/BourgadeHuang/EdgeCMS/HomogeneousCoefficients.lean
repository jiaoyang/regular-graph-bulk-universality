import BourgadeHuang.CMS.GeneralGauge

/-! Analytic homogeneous coefficients on an open cone.  The values and
derivatives are actual complex functions; the degree certificate expresses
their exact behavior under positive real dilation.  This permits the finite
CMS reduction to be used for the Airy coordinates without assuming rational
inverse-gap formulas. -/
noncomputable section
open Set Filter
open scoped Topology BigOperators

namespace BourgadeHuang.EdgeCMS
open CMS

structure OpenCone (d : ℕ) where
  carrier : Set (Point d)
  isOpen : IsOpen carrier
  scale_mem : ∀ {t : ℝ}, 0 < t → ∀ {z}, z ∈ carrier → (t : ℂ) • z ∈ carrier

structure Coefficient {d : ℕ} (C : OpenCone d) where
  eval : Point d → ℂ
  analytic : AnalyticOnNhd ℂ eval C.carrier

namespace Coefficient
variable {d : ℕ} {C : OpenCone d}

def const (a : ℂ) : Coefficient C := ⟨fun _ => a, analyticOnNhd_const⟩

def add (e f : Coefficient C) : Coefficient C := ⟨fun z => e.eval z + f.eval z, e.analytic.add f.analytic⟩

def mul (e f : Coefficient C) : Coefficient C := ⟨fun z => e.eval z * f.eval z, e.analytic.mul f.analytic⟩

def derivative (e : Coefficient C) (i : Fin d) : Coefficient C :=
  ⟨coordDeriv i e.eval, analyticOnNhd_coordDeriv e.analytic i⟩

@[simp] theorem eval_const (a : ℂ) (z : Point d) : (const (C := C) a).eval z = a := rfl
@[simp] theorem eval_add (e f : Coefficient C) (z : Point d) : (add e f).eval z = e.eval z + f.eval z := rfl
@[simp] theorem eval_mul (e f : Coefficient C) (z : Point d) : (mul e f).eval z = e.eval z * f.eval z := rfl
@[simp] theorem coordDeriv_eval (e : Coefficient C) {z : Point d} (_hz : z ∈ C.carrier) (i : Fin d) :
    coordDeriv i e.eval z = (e.derivative i).eval z := rfl

theorem analyticAt_eval (e : Coefficient C) {z : Point d} (hz : z ∈ C.carrier) :
    AnalyticAt ℂ e.eval z := e.analytic z hz

def Homogeneous (n : ℕ) (e : Coefficient C) : Prop :=
  ∀ {t : ℝ}, 0 < t → ∀ {z}, z ∈ C.carrier →
    e.eval ((t : ℂ) • z) = ((t : ℂ)⁻¹) ^ n * e.eval z

theorem Homogeneous.const (a : ℂ) : Homogeneous 0 (const (C := C) a) := by
  intro t ht z hz
  simp

theorem Homogeneous.zero (n : ℕ) : Homogeneous n (Coefficient.const (C := C) 0) := by
  intro t ht z hz
  simp

theorem Homogeneous.add {n : ℕ} {e f : Coefficient C}
    (he : Homogeneous n e) (hf : Homogeneous n f) : Homogeneous n (add e f) := by
  intro t ht z hz
  simp only [eval_add, he ht hz, hf ht hz, mul_add]

theorem Homogeneous.mul {n m : ℕ} {e f : Coefficient C}
    (he : Homogeneous n e) (hf : Homogeneous m f) : Homogeneous (n + m) (mul e f) := by
  intro t ht z hz
  simp only [eval_mul, he ht hz, hf ht hz, pow_add]
  ring

private theorem slice_derivative {f : Point d → ℂ} {z : Point d}
    (hf : AnalyticAt ℂ f z) (i : Fin d) :
    HasDerivAt (fun w => f (Function.update z i w)) (coordDeriv i f z) (z i) := by
  rw [coordDeriv_eq_fderiv hf.differentiableAt]
  exact hf.differentiableAt.hasFDerivAt.comp_hasDerivAt_of_eq (z i)
    (hasDerivAt_update z i (z i)) (Function.update_eq_self i z).symm

/-- Differentiating the actual dilation identity raises inverse degree by
one.  Thus degree certificates for every finite repeated derivative are
proved from the original coefficient, rather than imposed separately. -/
theorem homogeneous_derivative {n : ℕ} {e : Coefficient C}
    (he : Homogeneous n e) (i : Fin d) : Homogeneous (n + 1) (e.derivative i) := by
  intro t ht z hz
  have ht0 : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
  have htz := C.scale_mem ht hz
  have hupdate (w : ℂ) :
      Function.update ((t : ℂ) • z) i ((t : ℂ) * w) =
        (t : ℂ) • Function.update z i w := by
    ext j
    by_cases hji : j = i
    · subst j
      simp
    · simp [Function.update_of_ne hji]
  have hd := (slice_derivative (e.analytic _ htz) i).comp (z i)
    ((hasDerivAt_id (z i)).const_mul (t : ℂ))
  simp only [Pi.smul_apply, smul_eq_mul, one_mul] at hd
  have hs : HasDerivAt (fun w => e.eval ((t : ℂ) • Function.update z i w))
      ((t : ℂ) * coordDeriv i e.eval ((t : ℂ) • z)) (z i) := by
    convert hd using 1
    · funext w
      simp only [Function.comp_def, id_eq]
      rw [hupdate]
    · ring
  have hr := (slice_derivative (e.analytic _ hz) i).const_mul (((t : ℂ)⁻¹) ^ n)
  have hEq : (fun w => e.eval ((t : ℂ) • Function.update z i w)) =ᶠ[𝓝 (z i)]
      (fun w => ((t : ℂ)⁻¹) ^ n * e.eval (Function.update z i w)) := by
    have hc : Continuous (fun w : ℂ => Function.update z i w) := by
      apply continuous_pi
      intro j
      by_cases hji : j = i
      · subst j
        simpa using (continuous_id : Continuous (fun w : ℂ => w))
      · simpa [Function.update_of_ne hji] using (continuous_const : Continuous (fun _ : ℂ => z j))
    have hm : ∀ᶠ w in 𝓝 (z i), Function.update z i w ∈ C.carrier := by
      apply hc.continuousAt.eventually
      simpa only [Function.update_eq_self] using C.isOpen.mem_nhds hz
    filter_upwards [hm] with w hw
    exact he ht hw
  have h := (hs.congr_of_eventuallyEq hEq.symm).unique hr
  change coordDeriv i e.eval ((t : ℂ) • z) = ((t : ℂ)⁻¹) ^ (n + 1) * coordDeriv i e.eval z
  apply (mul_left_cancel₀ ht0)
  rw [h, pow_succ]
  field_simp [ht0]
  ring

end Coefficient
end BourgadeHuang.EdgeCMS
