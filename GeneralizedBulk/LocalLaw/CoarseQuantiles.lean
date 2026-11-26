import GeneralizedBulk.Spectral.KestenMcKayFiniteQuantile
import SpectralConsequences.KestenMcKayQuantiles

noncomputable section
open scoped Classical Topology
open Set MeasureTheory

namespace GeneralizedBulk.LocalLawBridge
open SpectralConsequences LocalLaw

theorem kestenMcKay_density_scaling (d : ℕ) (hd : 3 ≤ d) {x : ℝ}
    (hx : x ∈ Icc (-2 : ℝ) 2) :
    Real.sqrt ((d : ℝ)-1) * KestenMcKay.rawDensity d (Real.sqrt ((d : ℝ)-1)*x) =
      LocalLaw.kestenMcKayDensity d x := by
  let s : ℝ := Real.sqrt ((d : ℝ)-1)
  have hdr : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hs : 0 < s := Real.sqrt_pos.mpr (by linarith)
  have hss : s^2 = (d : ℝ)-1 := Real.sq_sqrt (by linarith)
  have hnat : ((d-1 : ℕ) : ℝ) = (d : ℝ)-1 := by rw [Nat.cast_sub (by omega : 1 ≤ d),Nat.cast_one]
  have hradius : KestenMcKay.radius d = 2*s := rfl
  have hraw : 0 < (d : ℝ)^2-(s*x)^2 := KestenMcKay.rawDenominator_pos d hdr
    (by rw [hradius]; constructor <;> nlinarith [hx.1,hx.2])
  have hnorm : 0 < (d : ℝ)^2/s^2-x^2 := by
    have h := SpectralConsequences.kestenMcKay_denominator_pos d hd hx
    simpa only [LocalLaw.kestenMcKayExterior, hnat, div_pow] using h
  have hrad : 4*((d : ℝ)-1)-(s*x)^2 = s^2*(4-x^2) := by rw [←hss]; ring
  have hsqrt : Real.sqrt (4*((d : ℝ)-1)-(s*x)^2) = s*Real.sqrt (4-x^2) := by
    rw [hrad, Real.sqrt_mul (sq_nonneg s), Real.sqrt_sq hs.le]
  change s*KestenMcKay.rawDensity d (s*x) = _
  rw [KestenMcKay.rawDensity, hsqrt, LocalLaw.kestenMcKayDensity_eq_rational d hd]
  unfold LocalLaw.semicircleDensity LocalLaw.kestenMcKayExterior
  rw [hnat, div_pow]
  change s*((d : ℝ)*(s*Real.sqrt (4-x^2))/(2*Real.pi*((d : ℝ)^2-(s*x)^2))) =
    (d : ℝ)*(Real.sqrt (4-x^2)/(2*Real.pi))/((d : ℝ)^2/s^2-x^2)
  let A := (d : ℝ)^2-(s*x)^2
  have hA : A ≠ 0 := hraw.ne'
  have hden : (d : ℝ)^2/s^2-x^2 = A/s^2 := by
    dsimp [A]
    field_simp
    ring
  rw [hden]
  change s*((d : ℝ)*(s*Real.sqrt (4-x^2))/(2*Real.pi*A)) =
    (d : ℝ)*(Real.sqrt (4-x^2)/(2*Real.pi))/(A/s^2)
  field_simp only [hA,hs.ne',Real.pi_ne_zero,two_ne_zero]
  ring

theorem kestenMcKay_cdf_scaling (d : ℕ) (hd : 3 ≤ d) {x : ℝ}
    (hx : x ∈ Icc (-2 : ℝ) 2) :
    KestenMcKay.cdf d (Real.sqrt ((d : ℝ)-1)*x) = SpectralConsequences.kestenMcKayCDF d x := by
  let s : ℝ := Real.sqrt ((d : ℝ)-1)
  have hdr : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hs : 0 < s := Real.sqrt_pos.mpr (by linarith)
  rw [SpectralConsequences.kestenMcKayCDF, SpectralConsequences.kestenMcKayClip_eq hx]
  change (∫ t in -(2*s)..s*x, KestenMcKay.rawDensity d t) = _
  calc
    _ = ∫ u in (-2 : ℝ)..x, s*KestenMcKay.rawDensity d (s*u) := by
      rw [intervalIntegral.integral_const_mul]
      have hh := intervalIntegral.smul_integral_comp_mul_left
        (f := KestenMcKay.rawDensity d) (a := (-2 : ℝ)) (b := x) s
      simpa only [smul_eq_mul, mul_neg, mul_comm s 2] using hh.symm
    _ = _ := by
      apply intervalIntegral.integral_congr
      intro u hu
      apply kestenMcKay_density_scaling d hd
      rw [uIcc_of_le hx.1] at hu
      exact ⟨hu.1,hu.2.trans hx.2⟩

end GeneralizedBulk.LocalLawBridge

namespace GeneralizedBulk.LocalLawBridge
open SpectralConsequences

theorem finiteQuantile_source_error (d : ℕ) (hd : 3 ≤ d) (M : ℕ) (hM : 0 < M)
    (i : Fin M) :
    |KestenMcKay.finiteQuantile d (by exact_mod_cast hd) M hM i / Real.sqrt ((d : ℝ)-1) -
        SpectralConsequences.classicalLocation d hd i| ≤
      (12*Real.pi)^(2/3 : ℝ) * (M : ℝ)^(-(2/3 : ℝ)) := by
  let s : ℝ := Real.sqrt ((d : ℝ)-1)
  let q := KestenMcKay.finiteQuantile d (by exact_mod_cast hd) M hM i
  have hdr : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hs : 0 < s := Real.sqrt_pos.mpr (by linarith)
  have hMr : (0 : ℝ) < M := Nat.cast_pos.mpr hM
  have hq : q ∈ Icc (-KestenMcKay.radius d) (KestenMcKay.radius d) :=
    KestenMcKay.quantile_mem d (by exact_mod_cast hd) _
  have hradius : KestenMcKay.radius d = 2*s := rfl
  have hqn : q/s ∈ Icc (-2 : ℝ) 2 := by
    rw [hradius] at hq
    constructor
    · apply (le_div_iff₀ hs).mpr
      linarith [hq.1]
    · apply (div_le_iff₀ hs).mpr
      linarith [hq.2]
  have hFq : SpectralConsequences.kestenMcKayCDF d (q/s) = 1-(i.val : ℝ)/M := by
    rw [← kestenMcKay_cdf_scaling d hd hqn]
    have hsimp : s*(q/s)=q := by field_simp
    change KestenMcKay.cdf d (s*(q/s)) = _
    rw [hsimp]
    exact KestenMcKay.cdf_finiteQuantile d (by exact_mod_cast hd) M hM i
  have hFi : SpectralConsequences.kestenMcKayCDF d (SpectralConsequences.classicalLocation d hd i) =
      1-((i.val : ℝ)+1)/M := by
    rw [SpectralConsequences.cdf_classicalLocation]
    linarith [SpectralConsequences.one_sub_sourceQuantileLevel i]
  have herror : |SpectralConsequences.kestenMcKayCDF d (q/s) -
      SpectralConsequences.kestenMcKayCDF d (SpectralConsequences.classicalLocation d hd i)| ≤ 1/(M : ℝ) := by
    rw [hFq,hFi]
    have he : (1-(i.val : ℝ)/M) - (1-((i.val : ℝ)+1)/M) = 1/(M : ℝ) := by ring
    rw [he,abs_of_nonneg (by positivity)]
  have hb := (SpectralConsequences.kestenMcKaySquareRootCDF d hd).inverse_modulus
    (q/s) (SpectralConsequences.classicalLocation d hd i) (1/(M : ℝ)) hqn
    (SpectralConsequences.classicalLocation_mem d hd i) (by positivity) herror
  change |q/s-SpectralConsequences.classicalLocation d hd i| ≤ _
  apply hb.trans_eq
  change ((1/(M : ℝ))/(1/(12*Real.pi)))^(2/3 : ℝ) = _
  have hrat : (1/(M : ℝ))/(1/(12*Real.pi)) = (12*Real.pi)/(M : ℝ) := by
    field_simp
  rw [hrat,Real.div_rpow (by positivity) hMr.le,
    div_eq_mul_inv, ←Real.rpow_neg hMr.le]

end GeneralizedBulk.LocalLawBridge
