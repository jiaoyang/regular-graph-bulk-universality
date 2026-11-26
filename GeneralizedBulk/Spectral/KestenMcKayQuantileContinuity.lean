import GeneralizedBulk.Spectral.KestenMcKayFiniteQuantile

/-! The actual Kesten--McKay CDF and quantile are inverse order
homeomorphisms of their compact support intervals. -/
noncomputable section
open Set
open scoped Topology
namespace GeneralizedBulk.KestenMcKay

def cdfOrderIso (d : ℝ) (hd : 3 ≤ d) : Icc (-radius d) (radius d) ≃o Icc (0 : ℝ) 1 where
  toFun x := ⟨cdf d x, by
    constructor
    · have hh := (strictMonoOn_cdf d hd).monotoneOn (show -radius d ∈ Icc (-radius d) (radius d) by
        constructor <;> linarith [radius_pos d hd]) x.property x.property.1
      simpa only [cdf_lower] using hh
    · have hh := (strictMonoOn_cdf d hd).monotoneOn x.property
        (show radius d ∈ Icc (-radius d) (radius d) by constructor <;> linarith [radius_pos d hd]) x.property.2
      simpa only [cdf_upper d hd] using hh⟩
  invFun u := ⟨quantile d hd u, quantile_mem d hd u⟩
  left_inv x := by
    apply Subtype.ext
    apply (strictMonoOn_cdf d hd).injOn (quantile_mem d hd _) x.property
    exact cdf_quantile d hd _
  right_inv u := Subtype.ext (cdf_quantile d hd u)
  map_rel_iff' := by
    intro x y
    change cdf d x ≤ cdf d y ↔ (x : ℝ) ≤ y
    constructor
    · intro h
      by_contra hn
      have hs := strictMonoOn_cdf d hd y.property x.property (lt_of_not_ge hn)
      exact (not_lt_of_ge h) hs
    · exact (strictMonoOn_cdf d hd).monotoneOn x.property y.property

theorem continuous_quantile (d : ℝ) (hd : 3 ≤ d) : Continuous (quantile d hd) := by
  exact continuous_subtype_val.comp (cdfOrderIso d hd).symm.continuous

theorem cdf_mem_Ioo (d : ℝ) (hd : 3 ≤ d) (E : ℝ) (hE : E ∈ Ioo (-radius d) (radius d)) :
    cdf d E ∈ Ioo (0 : ℝ) 1 := by
  have hR := radius_pos d hd
  constructor
  · have hh := strictMonoOn_cdf d hd (show -radius d ∈ Icc (-radius d) (radius d) by
      constructor <;> linarith) ⟨hE.1.le,hE.2.le⟩ hE.1
    simpa only [cdf_lower] using hh
  · have hh := strictMonoOn_cdf d hd ⟨hE.1.le,hE.2.le⟩
      (show radius d ∈ Icc (-radius d) (radius d) by constructor <;> linarith) hE.2
    simpa only [cdf_upper d hd] using hh

theorem quantile_cdf (d : ℝ) (hd : 3 ≤ d) (E : ℝ) (hE : E ∈ Icc (-radius d) (radius d)) :
    quantile d hd (cdfOrderIso d hd ⟨E,hE⟩) = E := by
  exact congrArg Subtype.val ((cdfOrderIso d hd).left_inv ⟨E,hE⟩)

end GeneralizedBulk.KestenMcKay
