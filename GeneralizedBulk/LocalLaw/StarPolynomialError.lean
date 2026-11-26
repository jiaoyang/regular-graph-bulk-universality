import LocalLaw.SourceLocalLawIdentifiers
import LocalLaw.ParameterGrowth
import LocalLaw.ReferenceBounds
import LocalLaw.SourceUniformNominalReduction

/-! Polynomial control of the actual source error at a power height. -/
noncomputable section
open Filter
open scoped Topology

namespace GeneralizedBulk.LocalLawBridge
open LocalLaw

private theorem source_variance_power_bound (x X β I : ℝ) (hx : 0 < x)
    (hX : 2*x^(2*β) ≤ X) (hI : I ≤ 2) :
    Real.sqrt (I/X) ≤ x^(-β) := by
  have hXp : 0 < X := lt_of_lt_of_le (by positivity) hX
  apply Real.sqrt_le_iff.mpr
  refine ⟨(Real.rpow_pos_of_pos hx _).le, ?_⟩
  apply (div_le_iff₀ hXp).mpr
  have h := mul_le_mul_of_nonneg_left hX (sq_nonneg (x^(-β)))
  have he : (x^(-β))^2 * (2*x^(2*β))=2 := by
    rw [← Real.rpow_mul_natCast hx.le]
    rw [mul_left_comm, ←Real.rpow_add hx]
    convert (by norm_num : (2 : ℝ)*x^(0 : ℝ)=2) using 1 <;> congr 2 <;> ring
  rw [he] at h
  linarith

private theorem source_fractional_power_bound (x X β : ℝ) (hx : 1 ≤ x)
    (hβ : 0 ≤ β) (hX : 2*x^(2*β) ≤ X) :
    (X^(2/3 : ℝ))⁻¹ ≤ x^(-β) := by
  have hxp : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hp : 1 ≤ x^(2*β) := Real.one_le_rpow hx (by positivity)
  have hXone : 1 ≤ X := by linarith
  have hXX : x^(2*β) ≤ X := by linarith
  have hs := Real.sqrt_le_sqrt hXX
  have hsx : Real.sqrt (x^(2*β))=x^β := by
    rw [Real.sqrt_eq_rpow, ←Real.rpow_mul hxp.le]
    congr 1
    ring
  rw [hsx] at hs
  have he := Real.rpow_le_rpow_of_exponent_le hXone (by norm_num : (1/2 : ℝ) ≤ 2/3)
  have hden : x^β ≤ X^(2/3 : ℝ) := hs.trans (by simpa only [Real.sqrt_eq_rpow] using he)
  rw [Real.rpow_neg hxp.le]
  simpa only [one_div] using one_div_le_one_div_of_le (Real.rpow_pos_of_pos hxp β) hden

/-- The complete source error, including its threshold inflation and scalar
stability, has a fixed polynomial rate at every height N^(-c), c<1/2.
The estimate is uniform in the real spectral coordinate. -/
theorem eventually_source_star_error (d : ℕ) (hd : 3 ≤ d)
    (c : ℝ) (hc : 0 < c) (hc1 : c < 1/2) :
    ∀ᶠ N : ℕ in atTop, ∀ z : ℂ,
      z.im = (N : ℝ)^(-c)/Real.sqrt ((d : ℝ)-1) →
      0 < z.im ∧ Real.log (N : ℝ)^300/(N : ℝ) ≤ z.im ∧
      (sourceUniformLawConstant d / Real.sqrt ((d : ℝ)-1)) *
        scalarScale (spectralScale z)
          (realSourcePaperError 12 d N (logarithmicRadius (1/128) d N) z) ≤
        (N : ℝ)^(-(1/1024 : ℝ)) := by
  let s : ℝ := Real.sqrt ((d : ℝ)-1)
  let β : ℝ := 1/128
  let A : ℝ := ((d-1 : ℕ) : ℝ)+2
  let C : ℝ := sourceUniformLawConstant d/s
  have hdr : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hs : 0 < s := Real.sqrt_pos.mpr (by linarith)
  have hβ : 0 < β := by norm_num [β]
  have hgap : 0 < 1-c-2*β := by dsimp [β]; linarith
  have hC : 0 ≤ C := div_nonneg ((by norm_num : (0 : ℝ) ≤ 4).trans
    (sourceUniformLawConstant_ge_four d)) hs.le
  have hbudget := eventually_const_mul_log_rpow_le (2*s) 0 (1-c-2*β) hgap
  have hlog := eventually_const_mul_log_rpow_le A 100 (β/2) (by positivity)
  have hconstant := eventually_const_mul_log_rpow_le C 0 (β/8) (by positivity)
  have hcut := eventually_const_mul_log_rpow_le s 300 (1-c) (by linarith)
  filter_upwards [hbudget,hlog,hconstant,hcut,eventually_log_ge_nat 1,
    eventually_ge_atTop 1] with N hbudget hlog hconstant hcut hL hN
  intro z hzim
  have hn : (0 : ℝ) < N := Nat.cast_pos.mpr (by omega)
  have hnone : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hz : 0 < z.im := by rw [hzim]; exact div_pos (Real.rpow_pos_of_pos hn _) hs
  have hX : 2*(N : ℝ)^(2*β) ≤ (N : ℝ)*z.im := by
    have hb : 2*s ≤ (N : ℝ)^(1-c-2*β) := by simpa using hbudget
    rw [hzim]
    change 2*(N : ℝ)^(2*β) ≤ (N : ℝ)*((N : ℝ)^(-c)/s)
    rw [←mul_div_assoc (N : ℝ) ((N : ℝ)^(-c)) s]
    apply (le_div_iff₀ hs).mpr
    have hh := mul_le_mul_of_nonneg_right hb (Real.rpow_nonneg hn.le (2*β))
    rw [←Real.rpow_add hn] at hh
    have he : (1-c-2*β)+(2*β)=1-c := by ring
    rw [he] at hh
    have hpow : (N : ℝ)*(N : ℝ)^(-c)=(N : ℝ)^(1-c) := by
      conv_lhs => lhs; rw [←Real.rpow_one (N : ℝ)]
      rw [←Real.rpow_add hn]
      rfl
    rw [hpow]
    nlinarith
  have hfloor : Real.log (N : ℝ)^300/(N : ℝ) ≤ z.im := by
    rw [hzim]
    change Real.log (N : ℝ)^300/(N : ℝ) ≤ (N : ℝ)^(-c)/s
    apply (div_le_div_iff₀ hn hs).mpr
    have hh : s*Real.log (N : ℝ)^300 ≤ (N : ℝ)^(1-c) := by
      simpa only [show (300 : ℝ)=((300 : ℕ) : ℝ) by norm_num,Real.rpow_natCast] using hcut
    have he : (N : ℝ)^(-c)*(N : ℝ)=(N : ℝ)^(1-c) := by
      conv_lhs => rhs; rw [←Real.rpow_one (N : ℝ)]
      rw [←Real.rpow_add hn]
      congr 1
      ring
    rw [he]
    simpa only [mul_comm] using hh
  have hI : (kestenMcKayStieltjes d z).im ≤ 2 := by
    rw [kestenMcKayStieltjes_eq_transform d hd z hz]
    exact (Complex.im_le_norm _).trans (kestenMcKayTransform_norm_le_two d hd z hz)
  have hterms : baseErrorTerms d N (logarithmicRadius β d N) z.im
      (kestenMcKayStieltjes d z).im ≤ A*(N : ℝ)^(-β) := by
    have hloc := logarithmicRadius_inverse_bound β d N hd hN
    have hvar := source_variance_power_bound (N : ℝ) _ β _ hn hX hI
    have hfrac := source_fractional_power_bound (N : ℝ) _ β hnone hβ.le hX
    have hloc' : ((((d-1 : ℕ) : ℝ)^logarithmicRadius β d N))⁻¹ ≤
        ((d-1 : ℕ) : ℝ)*(N : ℝ)^(-β) := by
      simpa only [Real.rpow_neg hn.le, div_eq_mul_inv] using hloc
    dsimp [baseErrorTerms,A]
    linarith
  have herror : realSourcePaperError 12 d N (logarithmicRadius β d N) z ≤
      (N : ℝ)^(-(β/2)) := by
    have hbase : 0 ≤ Real.log (N : ℝ)^(8*(12 : ℝ))*
        baseErrorTerms d N (logarithmicRadius β d N) z.im (kestenMcKayStieltjes d z).im := by
      exact mul_nonneg (Real.rpow_nonneg (by linarith) _)
        (baseErrorTerms_nonnegative _ _ _ _ _ hz.le)
    apply ((inflateError_bounds hL hbase).2).trans
    have hl : A*Real.log (N : ℝ)^100 ≤ (N : ℝ)^(β/2) := by
      simpa only [show (100 : ℝ)=((100 : ℕ) : ℝ) by norm_num,Real.rpow_natCast] using hlog
    have he : Real.log (N : ℝ)^4 * (Real.log (N : ℝ)^(8*(12 : ℝ))*
        baseErrorTerms d N (logarithmicRadius β d N) z.im (kestenMcKayStieltjes d z).im) =
        Real.log (N : ℝ)^100 * baseErrorTerms d N (logarithmicRadius β d N) z.im
          (kestenMcKayStieltjes d z).im := by
      rw [show (8*(12 : ℝ))=((96 : ℕ) : ℝ) by norm_num,Real.rpow_natCast]
      rw [←mul_assoc,←pow_add]
    rw [he]
    calc
      _ ≤ Real.log (N : ℝ)^100*(A*(N : ℝ)^(-β)) :=
        mul_le_mul_of_nonneg_left hterms (by positivity)
      _ ≤ (N : ℝ)^(β/2)*(N : ℝ)^(-β) := by
        simpa only [mul_assoc,mul_comm,mul_left_comm] using
          mul_le_mul_of_nonneg_right hl (Real.rpow_nonneg hn.le (-β))
      _ = _ := by rw [←Real.rpow_add hn]; congr 1; ring
  have hε : 0 ≤ realSourcePaperError 12 d N (logarithmicRadius β d N) z := by
    unfold realSourcePaperError
    apply inflateError_nonnegative
    exact mul_nonneg (Real.rpow_nonneg (by linarith) _)
      (baseErrorTerms_nonnegative _ _ _ _ _ hz.le)
  have hsc := scalarScale_le_sqrt (spectralScale_pos hz) hε
  have hsc' : scalarScale (spectralScale z)
      (realSourcePaperError 12 d N (logarithmicRadius β d N) z) ≤
      (N : ℝ)^(-(β/4)) := by
    apply hsc.trans
    apply (Real.sqrt_le_sqrt herror).trans_eq
    rw [Real.sqrt_eq_rpow, ←Real.rpow_mul hn.le]
    congr 1
    ring
  have hconst : C ≤ (N : ℝ)^(β/8) := by simpa using hconstant
  refine ⟨hz,hfloor,?_⟩
  have hh := (mul_le_mul_of_nonneg_left hsc' hC).trans
    (mul_le_mul_of_nonneg_right hconst (Real.rpow_nonneg hn.le _))
  have he : (N : ℝ)^(β/8)*(N : ℝ)^(-(β/4))=(N : ℝ)^(-(1/1024 : ℝ)) := by
    rw [←Real.rpow_add hn]
    norm_num [β]
  simpa only [he,C,β,s] using hh

end GeneralizedBulk.LocalLawBridge
