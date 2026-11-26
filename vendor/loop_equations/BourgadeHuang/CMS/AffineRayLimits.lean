import BourgadeHuang.CMS.RayIndependence
import BourgadeHuang.CMS.OriginalBasis

/-! Genuine limits of the affine factors appearing in shifted CMS rays. -/
noncomputable section
open scoped Topology BigOperators
open Filter
namespace BourgadeHuang.CMS

lemma tendsto_complex_real_inv_atTop :
    Tendsto (fun R : ℝ => (R:ℂ)⁻¹) atTop (nhds (0:ℂ)) := by
  simpa only [Function.comp_def,Complex.ofReal_inv,Complex.ofReal_zero] using
    (Complex.continuous_ofReal.tendsto (0:ℝ)).comp tendsto_inv_atTop_zero

lemma tendsto_affine_div_atTop (a b : ℂ) :
    Tendsto (fun R : ℝ => (a+(R:ℂ)*b)/(R:ℂ)) atTop (nhds b) := by
  have h := (tendsto_complex_real_inv_atTop.const_mul a).add_const b
  apply (show Tendsto (fun R : ℝ => a*(R:ℂ)⁻¹+b) atTop (nhds b) by simpa using h).congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with R hR
  have hRc : (R:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hR.ne'
  field_simp
  ring

lemma tendsto_mul_affine_inv_atTop (a b : ℂ) (hb : b ≠ 0) :
    Tendsto (fun R : ℝ => (R:ℂ)*(a+(R:ℂ)*b)⁻¹) atTop (nhds b⁻¹) := by
  simpa only [div_eq_mul_inv,mul_inv_rev,inv_inv] using (tendsto_affine_div_atTop a b).inv₀ hb

theorem tendsto_affine_product_div_pow {ι : Type*} (S : Finset ι) (a b : ι → ℂ) :
    Tendsto (fun R : ℝ => (S.prod (fun i => a i+(R:ℂ)*b i))/(R:ℂ)^S.card)
      atTop (nhds (∏ i ∈ S,b i)) := by
  have h := tendsto_finset_prod S (fun i _ => tendsto_affine_div_atTop (a i) (b i))
  simpa only [Finset.prod_div_distrib,Finset.prod_const] using h

theorem tendsto_pow_mul_affine_inv_product {ι : Type*} (S : Finset ι)
    (a b : ι → ℂ) (hb : ∀ i ∈ S,b i ≠ 0) :
    Tendsto (fun R : ℝ => (R:ℂ)^S.card*(∏ i ∈ S,(a i+(R:ℂ)*b i)⁻¹))
      atTop (nhds (∏ i ∈ S,(b i)⁻¹)) := by
  have h := tendsto_finset_prod S (fun i hi => tendsto_mul_affine_inv_atTop (a i) (b i) (hb i hi))
  simpa only [Finset.prod_mul_distrib,Finset.prod_const] using h

end BourgadeHuang.CMS
