import GeneralizedBulk.Spectral.CavityRadial
import GeneralizedBulk.Spectral.KestenMcKayPotentialStability

/-! A quantitative bulk evaluation of the literal regularized Kesten–McKay
potential, proved by contracting its actual cavity boundary parameter. -/
noncomputable section
namespace GeneralizedBulk.KestenMcKay

def bulkPotential (d E : ℝ) : ℝ :=
  (d - 1) / 2 * Real.log (d - 1) - (d - 2) / 4 * Real.log (d ^ 2 - E ^ 2)

def bulkHeightScale (d E : ℝ) : ℝ := (d - 1) * (cavityBoundary d E).im

theorem bulkHeightScale_pos (d E : ℝ) (hd : 3 ≤ d) (hbulk : E ^ 2 < 4 * (d - 1)) :
    0 < bulkHeightScale d E := mul_pos (by linarith) (cavityBoundary_im_pos d E hd hbulk)

/-- The genuine density potential differs from its closed bulk value by an
explicit O(eta) bound. No singular-boundary integral interchange is assumed. -/
theorem regularizedPotential_bulk_error (d E : ℝ) (hd : 3 ≤ d)
    (hbulk : E ^ 2 < 4 * (d - 1)) (eta : ℝ) (heta : 0 < eta)
    (heta' : eta ≤ bulkHeightScale d E) :
    |regularizedPotential d E eta - bulkPotential d E| ≤
      (d / bulkHeightScale d E + |E| / bulkHeightScale d E ^ 2) * eta := by
  let beta := bulkHeightScale d E
  let r := radialContraction (eta / beta)
  let g0 := cavityBoundary d E
  let z := treeSpectralPoint d ((r : ℂ) * g0)
  have hb : 0 < beta := bulkHeightScale_pos d E hd hbulk
  have hh : 0 < eta / beta := div_pos heta hb
  obtain ⟨hrp, hru, hquad⟩ := radialContraction_spec (eta / beta) hh.le
  change 0 < r at hrp
  change r ≤ 1 at hru
  have hrh : 1 / 2 ≤ r := radialContraction_ge_half (eta / beta) hh.le ((div_le_one hb).mpr heta')
  have hrl : r < 1 := radialContraction_lt_one (eta / beta) hh
  have he : 1 - r ≤ eta / beta := one_sub_radialContraction_le (eta / beta) hh.le
  have hrec : r⁻¹ - r = eta / beta := radialContraction_reciprocal (eta / beta) hh.le
  have hzim : z.im = eta := by
    dsimp only [z, g0]
    rw [treeSpectralPoint_radial_im d E hd hbulk r hrp.ne']
    change beta * (r⁻¹ - r) = eta
    rw [hrec]
    field_simp
  have hgne : (r : ℂ) * g0 ≠ 0 := mul_ne_zero (Complex.ofReal_ne_zero.mpr hrp.ne')
    (cavityBoundary_ne_zero d E hd hbulk)
  have hu : ‖treeLogParameter d ((r : ℂ) * g0)‖ < 1 := by
    dsimp only [g0]
    rw [treeLogParameter_radial_norm d E hd hbulk r hrp.le]
    exact hrl
  have hpot := regularizedPotential_treeSpectralPoint d hd ((r : ℂ) * g0) hgne hu
    (by simpa only [hzim] using heta : 0 < z.im)
  change regularizedPotential d z.re z.im = treePrimitive d ((r : ℂ) * g0) at hpot
  rw [hzim] at hpot
  have hprim := treePrimitive_radial_bound d hd g0 (cavityBoundary_ne_zero d E hd hbulk)
    (cavityBoundary_norm_sq_le_half d E hd hbulk) r hrh hru
  have hprim' : |treePrimitive d ((r : ℂ) * g0) - treePrimitive d g0| ≤ d * eta / beta := by
    exact hprim.trans (by convert mul_le_mul_of_nonneg_left he (by linarith : 0 ≤ d) using 1 <;> ring)
  have henergy : |E - z.re| ≤ |E| * (1 - r) ^ 2 := by
    rw [abs_sub_comm]
    change |(treeSpectralPoint d ((r : ℂ) * cavityBoundary d E)).re - E| ≤ _
    rw [treeSpectralPoint_radial_re d E hd hbulk r hrp.ne']
    exact radial_energyShift_bound E r hrh
  have he2 : (1 - r) ^ 2 ≤ (eta / beta) ^ 2 :=
    (sq_le_sq₀ (by linarith : 0 ≤ 1 - r) hh.le).mpr he
  have hshift : eta⁻¹ * |E - z.re| ≤ |E| * eta / beta ^ 2 := by
    calc
      _ ≤ eta⁻¹ * (|E| * (eta / beta) ^ 2) :=
        mul_le_mul_of_nonneg_left (henergy.trans (mul_le_mul_of_nonneg_left he2 (abs_nonneg E))) (inv_nonneg.mpr heta.le)
      _ = _ := by field_simp; ring
  have hlip := (regularizedPotential_energy_lipschitz d hd E z.re eta heta).trans hshift
  have htri := abs_sub_le (regularizedPotential d E eta) (regularizedPotential d z.re eta) (treePrimitive d g0)
  rw [hpot] at htri hlip
  have hboundary : treePrimitive d g0 = bulkPotential d E := treePrimitive_cavityBoundary d E hd hbulk
  rw [← hboundary]
  have hbnd := htri.trans (add_le_add hlip hprim')
  convert hbnd using 1 <;> dsimp [beta] <;> ring

end GeneralizedBulk.KestenMcKay
