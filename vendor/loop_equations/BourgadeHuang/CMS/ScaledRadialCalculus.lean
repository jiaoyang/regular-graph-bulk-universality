import BourgadeHuang.CMS.FullSubsetRadial

/-! Differential equivalence of scaled and unscaled radial connections and
exact covariance under a positive shift of the ray base point. -/
noncomputable section
open scoped BigOperators
namespace BourgadeHuang.CMS
set_option maxHeartbeats 1000000

/-- Logarithmic-derivative form of the usual power rule. -/
theorem hasDerivAt_power_logarithmic (n : ℕ) {t : ℂ} (ht : t≠0) :
    HasDerivAt (fun r : ℂ => r^n) ((n:ℂ)/t*t^n) t := by
  convert hasDerivAt_pow n t using 1
  cases n with
  | zero => simp
  | succ n =>
    rw [Nat.add_sub_cancel,pow_succ]
    field_simp
    ring

/-- Real differentiation of a complex radial power. -/
theorem hasDerivAt_real_power (n : ℕ) {t : ℝ} (ht : t≠0) :
    HasDerivAt (fun r : ℝ => (r:ℂ)^n) ((n:ℂ)/(t:ℂ)*(t:ℂ)^n) t :=
  (hasDerivAt_power_logarithmic n (Complex.ofReal_ne_zero.mpr ht)).comp_ofReal

theorem hasDerivAt_real_power_mul (n : ℕ) {f : ℝ → ℂ} {f' : ℂ} {t : ℝ}
    (ht : t≠0) (hf : HasDerivAt f f' t) :
    HasDerivAt (fun r : ℝ => (r:ℂ)^n*f r)
      ((n:ℂ)/(t:ℂ)*((t:ℂ)^n*f t)+(t:ℂ)^n*f') t := by
  convert (hasDerivAt_real_power n ht).mul hf using 1 <;> ring

theorem hasDerivAt_real_power_inv_mul (n : ℕ) {f : ℝ → ℂ} {f' : ℂ} {t : ℝ}
    (ht : t≠0) (hf : HasDerivAt f f' t) :
    HasDerivAt (fun r : ℝ => ((r:ℂ)^n)⁻¹*f r)
      (((t:ℂ)^n)⁻¹*(f'-(n:ℂ)/(t:ℂ)*f t)) t := by
  have htc : (t:ℂ)≠0 := Complex.ofReal_ne_zero.mpr ht
  have hd := ((hasDerivAt_power_logarithmic n htc).inv (pow_ne_zero _ htc)).comp_ofReal.mul hf
  convert hd using 1
  field_simp
  ring

namespace SectorialData
variable {d : ℕ} (D : SectorialData d)

/-- The original finite connection contracted against a constant direction. -/
def radialConnectionAction (ω z : Point d) (X : Finset (Fin d) → ℂ)
    (S : Finset (Fin d)) : ℂ := ∑i,ω i*∑T : Finset (Fin d),D.connection i z S T*X T

/-- Removing the degree weights gives the actual first-order connection. -/
theorem hasDerivAt_unscale_radial (ω z : Point d) (Y : ℝ → Finset (Fin d) → ℂ)
    {t : ℝ} (ht : t≠0) (S : Finset (Fin d))
    (hY : HasDerivAt (fun r => Y r S) (D.scaledRadialAction ω z t (Y t) S) t) :
    HasDerivAt (fun r : ℝ => ((r:ℂ)^S.card)⁻¹*Y r S)
      (D.radialConnectionAction ω z (fun T => ((t:ℂ)^T.card)⁻¹*Y t T) S) t := by
  have htc : (t:ℂ)≠0 := Complex.ofReal_ne_zero.mpr ht
  let X := fun T : Finset (Fin d) => ((t:ℂ)^T.card)⁻¹*Y t T
  have hsc : ∀T,(t:ℂ)^T.card*X T=Y t T := by
    intro T
    dsimp only [X]
    rw [←mul_assoc,mul_inv_cancel₀ (pow_ne_zero _ htc),one_mul]
  have he := D.scaled_connection_action ω z S X htc
  simp_rw [hsc] at he
  change (S.card:ℂ)/(t:ℂ)*Y t S+(t:ℂ)^S.card*D.radialConnectionAction ω z X S=
    D.scaledRadialAction ω z t (Y t) S at he
  have hd := hasDerivAt_real_power_inv_mul S.card ht hY
  convert hd using 1
  rw [←he]
  dsimp only [X]
  field_simp

/-- Conversely, degree weights produce exactly the scaled radial equations. -/
theorem hasDerivAt_scale_radial (ω z : Point d) (X : ℝ → Finset (Fin d) → ℂ)
    {t : ℝ} (ht : t≠0) (S : Finset (Fin d))
    (hX : HasDerivAt (fun r => X r S) (D.radialConnectionAction ω z (X t) S) t) :
    HasDerivAt (fun r : ℝ => (r:ℂ)^S.card*X r S)
      (D.scaledRadialAction ω z t (fun T => (t:ℂ)^T.card*X t T) S) t := by
  have hd := hasDerivAt_real_power_mul S.card ht hX
  have he := D.scaled_connection_action ω z S (X t) (Complex.ofReal_ne_zero.mpr ht)
  rw [show D.scaledRadialAction ω z t (fun T => (t:ℂ)^T.card*X t T) S=
    (S.card:ℂ)/(t:ℂ)*((t:ℂ)^S.card*X t S)+(t:ℂ)^S.card*D.radialConnectionAction ω z (X t) S from he.symm]
  exact hd

end SectorialData

/-- Translating the ray origin by h translates its time parameter by h. -/
theorem sectorialRay_shift {d : ℕ} (σ : Fin d → Sign) (z : Point d) (R t h : ℝ) :
    sectorialRay σ (shiftedRay σ z h) R t=sectorialRay σ z R (t+h) := by
  funext i
  simp only [sectorialRay,shiftedRay,Complex.ofReal_sub,Complex.ofReal_add]
  ring

namespace SectorialData
variable {d : ℕ} (D : SectorialData d)

/-- Exact shift covariance of the scaled radial differential system. -/
theorem hasDerivAt_translate_scaled_radial (σ : Fin d → Sign) (z : Point d) (R h : ℝ)
    (Y : ℝ → Finset (Fin d) → ℂ) {t : ℝ} (ht : t≠0) (hth : t+h≠0)
    (hY : ∀S,HasDerivAt (fun r => Y r S)
      (D.scaledRadialAction (shiftedDirection σ) (sectorialRay σ z R (t+h)) ((t+h:ℝ):ℂ) (Y (t+h)) S) (t+h))
    (S : Finset (Fin d)) :
    HasDerivAt (fun r : ℝ => ((r:ℂ)/((r:ℂ)+(h:ℂ)))^S.card*Y (r+h) S)
      (D.scaledRadialAction (shiftedDirection σ) (sectorialRay σ (shiftedRay σ z h) R t) t
        (fun T => ((t:ℂ)/((t:ℂ)+(h:ℂ)))^T.card*Y (t+h) T) S) t := by
  let X := fun r (T : Finset (Fin d)) => (((r+h:ℝ):ℂ)^T.card)⁻¹*Y (r+h) T
  have hx : ∀T,HasDerivAt (fun r => X r T)
      (D.radialConnectionAction (shiftedDirection σ)
        (sectorialRay σ (shiftedRay σ z h) R t) (X t) T) t := by
    intro T
    have hd := (D.hasDerivAt_unscale_radial (shiftedDirection σ)
      (sectorialRay σ z R (t+h)) Y hth T (hY T)).scomp t ((hasDerivAt_id t).add_const h)
    simpa only [sectorialRay_shift,mul_one,one_smul] using hd
  have hd := D.hasDerivAt_scale_radial (shiftedDirection σ)
    (sectorialRay σ (shiftedRay σ z h) R t) X ht S (hx S)
  simpa only [X,Complex.ofReal_add,div_pow,div_eq_mul_inv,mul_pow,inv_pow,mul_assoc] using hd

end SectorialData
end BourgadeHuang.CMS
