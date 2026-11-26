import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-! Logarithmic derivatives of real-power repulsion factors away from collisions. -/
noncomputable section
open MeasureTheory Filter Set
open scoped BigOperators Topology
namespace BourgadeHuang.RationalBulk

theorem hasDerivAt_abs_rpow_logarithmic (β a t : ℝ) (hta : t ≠ a) :
    HasDerivAt (fun x : ℝ => |x - a| ^ β)
      (β / (t - a) * |t - a| ^ β) t := by
  have hne : t - a ≠ 0 := sub_ne_zero.mpr hta
  rcases lt_or_gt_of_ne hne with hneg | hpos
  · have habs : HasDerivAt (fun x : ℝ => |x - a|) (-1) t := by
      apply (((hasDerivAt_id t).sub_const a).neg).congr_of_eventuallyEq
      filter_upwards [((continuous_id.sub continuous_const).continuousAt.eventually
        (gt_mem_nhds hneg))] with x hx
      exact abs_of_neg hx
    have hd := habs.rpow_const (p := β) (Or.inl (abs_ne_zero.mpr hne))
    convert hd using 1
    rw [Real.rpow_sub (abs_pos.mpr hne), Real.rpow_one]
    rw [abs_of_neg hneg]
    field_simp [hne, sub_ne_zero.mpr hta.symm]
    <;> ring
  · have habs : HasDerivAt (fun x : ℝ => |x - a|) 1 t := by
      apply ((hasDerivAt_id t).sub_const a).congr_of_eventuallyEq
      filter_upwards [((continuous_id.sub continuous_const).continuousAt.eventually
        (lt_mem_nhds hpos))] with x hx
      exact abs_of_pos hx
    have hd := habs.rpow_const (p := β) (Or.inl (abs_ne_zero.mpr hne))
    convert hd using 1
    rw [Real.rpow_sub (abs_pos.mpr hne), Real.rpow_one]
    rw [abs_of_pos hpos]
    field_simp [hne, sub_ne_zero.mpr hta.symm]
    <;> ring

/-- A finite product version that keeps the full density as a common factor. -/
theorem hasDerivAt_finset_prod_logarithmic
    {ι : Type*} [DecidableEq ι] (S : Finset ι) (f df : ι → ℝ → ℝ) (t : ℝ)
    (hd : ∀ i ∈ S, HasDerivAt (f i) (df i t * f i t) t) :
    HasDerivAt (fun x => ∏ i ∈ S, f i x)
      ((∑ i ∈ S, df i t) * ∏ i ∈ S, f i t) t := by
  induction S using Finset.induction_on with
  | empty => simpa using hasDerivAt_const t (1 : ℝ)
  | @insert i S hi ih =>
    simp only [Finset.mem_insert, forall_eq_or_imp] at hd
    have h := hd.1.mul (ih hd.2)
    simpa only [Finset.prod_insert hi, Finset.sum_insert hi, add_mul, mul_add,
      mul_assoc, mul_left_comm] using h

theorem hasDerivAt_repulsion_product {ι : Type*} [Fintype ι]
    (β : ℝ) (a : ι → ℝ) (t : ℝ) (ht : ∀ i, t ≠ a i) :
    HasDerivAt (fun x : ℝ => ∏ i, |x - a i| ^ β)
      ((β * ∑ i, (t - a i)⁻¹) * ∏ i, |t - a i| ^ β) t := by
  classical
  have h := hasDerivAt_finset_prod_logarithmic Finset.univ
    (fun i x => |x - a i| ^ β) (fun i x => β / (x - a i)) t
    (fun i _ => hasDerivAt_abs_rpow_logarithmic β (a i) t (ht i))
  simpa only [div_eq_mul_inv, ← Finset.mul_sum] using h

theorem HasDerivAt.abs_rpow_logarithmic {f : ℝ → ℝ} {df t : ℝ}
    (h : HasDerivAt f df t) (β : ℝ) (hf : f t ≠ 0) :
    HasDerivAt (fun x => |f x| ^ β) (β * df / f t * |f t| ^ β) t := by
  have hd := (hasDerivAt_abs_rpow_logarithmic β 0 (f t) hf).comp t h
  convert hd using 1
  · ext x
    simp
  · simp only [sub_zero]
    ring

/-- The singularity in the density derivative is locally integrable for every
positive beta; the Gaussian also controls both tails. -/
theorem integrable_abs_rpow_mul_gaussian {c s : ℝ} (hc : 0 < c) (hs : -1 < s) :
    Integrable (fun x : ℝ => |x| ^ s * Real.exp (-c * x ^ 2)) := by
  have hpos : IntegrableOn (fun x : ℝ => |x| ^ s * Real.exp (-c * x ^ 2)) (Ioi 0) := by
    apply (integrableOn_rpow_mul_exp_neg_mul_sq hc hs).congr_fun _ measurableSet_Ioi
    intro x hx
    simp [abs_of_pos (show 0 < x from hx)]
  rw [← integrableOn_univ, ← @Iio_union_Ici _ _ (0 : ℝ), integrableOn_union,
    integrableOn_Ici_iff_integrableOn_Ioi]
  refine ⟨?_, hpos⟩
  rw [← (Measure.measurePreserving_neg (volume : Measure ℝ)).integrableOn_comp_preimage
    (Homeomorph.neg ℝ).measurableEmbedding]
  simpa only [Function.comp_def, abs_neg, neg_sq, neg_preimage, neg_Iio, neg_neg,
    neg_zero] using hpos

theorem integrable_shifted_abs_rpow_mul_gaussian {c s : ℝ}
    (hc : 0 < c) (hs : -1 < s) (a : ℝ) :
    Integrable (fun x : ℝ => |x - a| ^ s * Real.exp (-c * x ^ 2)) := by
  have hi := ((integrable_abs_rpow_mul_gaussian (by linarith : 0 < c / 2) hs).comp_sub_right a).const_mul (Real.exp (c * a ^ 2))
  apply hi.mono'
  · exact (((continuous_id.sub continuous_const).abs.measurable).pow measurable_const).mul
      (((measurable_id.pow_const 2).const_mul (-c)).exp) |>.aestronglyMeasurable
  · filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have he : Real.exp (-c * x ^ 2) ≤
        Real.exp (c * a ^ 2) * Real.exp (-(c / 2) * (x - a) ^ 2) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      nlinarith [sq_nonneg (x + a), mul_nonneg hc.le (sq_nonneg (x + a))]
    calc
      _ ≤ |x - a| ^ s *
          (Real.exp (c * a ^ 2) * Real.exp (-(c / 2) * (x - a) ^ 2)) :=
        mul_le_mul_of_nonneg_left he (Real.rpow_nonneg (abs_nonneg _) _)
      _ = _ := by ring

end BourgadeHuang.RationalBulk
