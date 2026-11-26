import BourgadeHuang.RationalBulk.RatioPaths
import BourgadeHuang.RationalBulk.ChargedObservables
import BourgadeHuang.OrthogonalMixedNormalization
import BourgadeHuang.OrthogonalRatioRayGrowth

/-! Growth of the genuine rational-charge observables from the beta-dependent
centered local law, with cancellation of the common reflected base point. -/
noncomputable section
open scoped BigOperators Topology
open MeasureTheory Filter
namespace BourgadeHuang.RationalBulk

theorem nevanlinnaPathPrimitive_re_upper (s : AnchoredCountingState) {u v : ℂ}
    (h : SameOpenHalfPlane u v) :
    (nevanlinnaPathPrimitive s (upperRepresentative u) (upperRepresentative v)).re =
      (nevanlinnaPathPrimitive s u v).re := by
  rcases h with h | h
  · rw [upperRepresentative_eq u h.1.le, upperRepresentative_eq v h.2.le]
  · rw [upperRepresentative_eq_conj u h.1.le, upperRepresentative_eq_conj v h.2.le,
      nevanlinnaPathPrimitive_conj, Complex.conj_re]

theorem norm_chargedFactor_real (c : ℝ) (s : AnchoredCountingState) {z b : ℂ}
    (hz : z.im ≠ 0) (hb : b.im ≠ 0)
    (hc : (c : ℂ) ≠ -1 → SameOpenHalfPlane z b) :
    ‖chargedFactor (c : ℂ) s z b‖ =
      Real.exp (c * (nevanlinnaPathPrimitive s (upperRepresentative z) (upperRepresentative b)).re) := by
  by_cases h : (c : ℂ) = -1
  · have hcr : c = -1 := by exact_mod_cast h
    simp only [chargedFactor, if_pos h]
    rw [← norm_entireCharacteristicRatio_upper s z b,
      entireCharacteristicRatio_eq_anchored s (Or.inl ⟨by simpa using abs_pos.mpr hz,
        by simpa using abs_pos.mpr hb⟩), anchoredCharacteristicRatio_eq_exp_primitive,
      Complex.norm_exp, Complex.neg_re, hcr, neg_one_mul]
  · simp only [chargedFactor, if_neg h, Complex.norm_exp, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    rw [nevanlinnaPathPrimitive_re_upper s (hc h)]

theorem norm_chargedObservable_rebase {d : ℕ} (c : Fin d → ℝ)
    (b z : Fin d → ℂ) (s : AnchoredCountingState)
    (hz : ∀ j, (z j).im ≠ 0) (hd : ChargedDomain (fun j => (c j : ℂ)) b z)
    (hneutral : ∑ j, c j = 0) {B H : ℂ} (hB : 0 < B.im) (hH : 0 < H.im)
    (hb : ∀ j, upperRepresentative (b j) = B) :
    ‖chargedObservable (fun j => (c j : ℂ)) b s z‖ =
      Real.exp (∑ j, c j * (nevanlinnaPathPrimitive s (upperRepresentative (z j)) H).re) := by
  simp only [chargedObservable, norm_prod, norm_chargedFactor_real _ _ (hz _) (hd.1 _) (hd.2 _), hb]
  rw [← Real.exp_sum]
  congr 1
  have hc j := nevanlinnaPathPrimitive_cocycle s
    (Or.inl ⟨show 0 < (upperRepresentative (z j)).im by simpa using abs_pos.mpr (hz j),hB⟩)
    (Or.inl ⟨hH,hB⟩)
  have he j : (nevanlinnaPathPrimitive s (upperRepresentative (z j)) B).re =
      (nevanlinnaPathPrimitive s (upperRepresentative (z j)) H).re +
        (nevanlinnaPathPrimitive s H B).re := by
    have hh := congrArg Complex.re (hc j)
    simp only [Complex.sub_re] at hh
    linarith
  simp_rw [he, mul_add]
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, hneutral, zero_mul, add_zero]

/-- The upper straight path centered source used in the rate bound. -/
def upperCenteredPrimitive (s : AnchoredCountingState) (u v : ℂ) : ℂ :=
  compactCenteredSource ratioIntervalMeasure
    (fun t : RatioInterval => ratioPath u v t) (fun _ => -(u-v)) s

lemma ratioPath_im_pos {u v : ℂ} (hu : 0<u.im) (hv : 0<v.im)
    (t : RatioInterval) : 0 < (ratioPath u v t).im := by
  have heq : (ratioPath u v t).im=(1-(t:ℝ))*v.im+(t:ℝ)*u.im := by simp [ratioPath]; ring
  rw [heq]
  have ht := t.property
  nlinarith [mul_nonneg (sub_nonneg.mpr ht.2) (sub_nonneg.mpr (min_le_right u.im v.im)),
    mul_nonneg ht.1 (sub_nonneg.mpr (min_le_left u.im v.im)), lt_min hu hv]

theorem measurable_upperCenteredPrimitive {u v : ℂ} (hu : 0 < u.im) (hv : 0 < v.im) :
    Measurable (fun s => upperCenteredPrimitive s u v) :=
  measurable_compactCenteredSource ratioIntervalMeasure _ _
    ((continuous_ratioPath u v).comp continuous_subtype_val) continuous_const
    (fun t => ratioPath_im_pos hu hv t)

theorem upperCenteredPrimitive_exp_bound
    (ν : Measure AnchoredCountingState) [IsProbabilityMeasure ν] (β : ℝ)
    (hh : ExactHierarchy ν β) {a : ℝ} (ha : 0<a)
    (he : Integrable (fun s : AnchoredCountingState => Real.exp (a*‖s.val.2‖^2)) ν)
    {u v : ℂ} (hu : 0<u.im) (hv : 0<v.im) {D L : ℝ}
    (hD : 0≤D) (hL : 0≤L) (hcost : ‖u-v‖≤D*min u.im v.im) :
    Integrable (fun s => Real.exp (L*‖upperCenteredPrimitive s u v‖)) ν ∧
      (∫ s,Real.exp (L*‖upperCenteredPrimitive s u v‖) ∂ν) ≤
        2*Real.exp ((L*D)^2/(4*bulkExponentialScale β)) := by
  apply compactCenteredSource_exp_bound ratioIntervalMeasure
    (fun t : RatioInterval => ratioPath u v t) (fun _ => -(u-v))
    ((continuous_ratioPath u v).comp continuous_subtype_val) continuous_const
    (fun t => ratioPath_im_pos hu hv t) ν β hh ha he hD hL
  intro t
  rw [norm_neg]
  apply hcost.trans
  apply mul_le_mul_of_nonneg_left _ hD
  have heq : (ratioPath u v t).im=(1-(t:ℝ))*v.im+(t:ℝ)*u.im := by simp [ratioPath]; ring
  rw [heq]
  nlinarith [mul_le_mul_of_nonneg_left (min_le_left u.im v.im) t.property.1,
    mul_le_mul_of_nonneg_left (min_le_right u.im v.im) (sub_nonneg.mpr t.property.2)]


theorem measurable_chargedObservable {d : ℕ} (c b z : Fin d → ℂ)
    (hd : ChargedDomain c b z) : Measurable (fun s => chargedObservable c b s z) := by
  apply Finset.measurable_prod
  intro j _
  by_cases hc : c j = -1
  · simpa only [chargedFactor, if_pos hc] using measurable_entireCharacteristicRatio (z j) (b j)
  · simpa only [chargedFactor, if_neg hc] using
      Complex.measurable_exp.comp ((measurable_nevanlinnaPathPrimitive (hd.2 j hc)).const_mul (c j))

theorem norm_chargedObservable_le_centered_product {d : ℕ} (c : Fin d → ℝ)
    (b z : Fin d → ℂ) (s : AnchoredCountingState)
    (hz : ∀ j, (z j).im ≠ 0) (hd : ChargedDomain (fun j => (c j : ℂ)) b z)
    (hneutral : ∑ j, c j = 0) {B H : ℂ} (hB : 0 < B.im) (hH : 0 < H.im)
    (hb : ∀ j, upperRepresentative (b j) = B) :
    ‖chargedObservable (fun j => (c j : ℂ)) b s z‖ ≤
      Real.exp (-∑ j,c j*|(z j).im|) *
        ∏ j,Real.exp (|c j| *‖upperCenteredPrimitive s (upperRepresentative (z j)) H‖) := by
  rw [norm_chargedObservable_rebase c b z s hz hd hneutral hB hH hb,
    ← Real.exp_sum, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hc j := nevanlinnaPathPrimitive_centered s
    (show 0 < (upperRepresentative (z j)).im by simpa using abs_pos.mpr (hz j)) hH
  have he j : c j * (nevanlinnaPathPrimitive s (upperRepresentative (z j)) H).re =
      -c j*|(z j).im|+c j*H.im-c j*(upperCenteredPrimitive s (upperRepresentative (z j)) H).re := by
    rw [hc]
    simp only [Complex.sub_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      mul_zero, mul_one, zero_sub, Complex.sub_im, upperRepresentative_im]
    dsimp [upperCenteredPrimitive]
    ring
  simp_rw [he]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.sum_mul, hneutral,
    zero_mul, add_zero]
  simp only [neg_mul, Finset.sum_neg_distrib]
  have hsum : -(∑ j,c j*(upperCenteredPrimitive s (upperRepresentative (z j)) H).re) ≤
      ∑ j,|c j| *‖upperCenteredPrimitive s (upperRepresentative (z j)) H‖ := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_le_sum
    intro j _
    exact (neg_le_abs _).trans (by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm _) (abs_nonneg _))
  linarith

theorem expectedChargedObservable_growth {d : ℕ} (hdim : 0<d)
    (ν : Measure AnchoredCountingState) [IsProbabilityMeasure ν] (β : ℝ)
    (hh : ExactHierarchy ν β) {a : ℝ} (ha : 0<a)
    (he : Integrable (fun s : AnchoredCountingState => Real.exp (a*‖s.val.2‖^2)) ν)
    (c : Fin d → ℝ) (b z : Fin d → ℂ)
    (hz : ∀ j, (z j).im ≠ 0) (hd : ChargedDomain (fun j => (c j : ℂ)) b z)
    (hneutral : ∑ j, c j = 0) {B H : ℂ} (hB : 0 < B.im) (hH : 0 < H.im)
    (hb : ∀ j, upperRepresentative (b j) = B) {D K : ℝ} (hD : 0≤D) (hK : 0≤K)
    (hcoef : ∀ j,|c j|≤K)
    (hcost : ∀ j,‖upperRepresentative (z j)-H‖≤D*min |(z j).im| H.im) :
    ‖expectedChargedObservable ν (fun j => (c j : ℂ)) b z‖ ≤
      ((d:ℝ)*(2*Real.exp (((d:ℝ)*K*D)^2/(4*bulkExponentialScale β)))) *
        Real.exp (-∑ j,c j*|(z j).im|) := by
  let f := fun j s => Real.exp (|c j| *‖upperCenteredPrimitive s (upperRepresentative (z j)) H‖)
  let C := 2*Real.exp (((d:ℝ)*K*D)^2/(4*bulkExponentialScale β))
  have hup j : 0<(upperRepresentative (z j)).im := by simpa using abs_pos.mpr (hz j)
  have hf (j) : Integrable (fun s => (f j s)^d) ν ∧ (∫s,(f j s)^d ∂ν) ≤ C := by
    have h := upperCenteredPrimitive_exp_bound ν β hh ha he (hup j) hH hD
      (show 0≤(d:ℝ)*|c j| by positivity) (by simpa only [upperRepresentative_im] using hcost j)
    have heq s : (f j s)^d = Real.exp (((d:ℝ)*|c j|)*‖upperCenteredPrimitive s (upperRepresentative (z j)) H‖) := by
      simp only [f, ← Real.exp_nat_mul]
      congr 1
      ring
    refine ⟨by simpa only [heq] using h.1, ?_⟩
    simp only [heq]
    apply h.2.trans
    dsimp [C]
    gcongr
    · exact mul_nonneg (by norm_num) (bulkExponentialScale_pos β).le
    · exact hcoef j
  obtain ⟨hpi,hpb⟩ := finite_product_integral_bound hdim ν f
    (fun j => Real.continuous_exp.measurable.comp
      (measurable_const.mul (measurable_upperCenteredPrimitive (hup j) hH).norm))
    (fun _ _ => (Real.exp_pos _).le) (fun j => (hf j).1) C (fun j => (hf j).2)
  let M := Real.exp (-∑j,c j*|(z j).im|)
  have hpoint s : ‖chargedObservable (fun j => (c j : ℂ)) b s z‖ ≤ M*∏j,f j s :=
    norm_chargedObservable_le_centered_product c b z s hz hd hneutral hB hH hb
  have hi : Integrable (fun s => chargedObservable (fun j => (c j : ℂ)) b s z) ν :=
    (hpi.const_mul M).mono' (measurable_chargedObservable _ _ _ hd).aestronglyMeasurable
      (Eventually.of_forall hpoint)
  calc
    _ ≤ ∫s,‖chargedObservable (fun j => (c j : ℂ)) b s z‖ ∂ν := norm_integral_le_integral_norm _
    _ ≤ ∫s,M*∏j,f j s ∂ν := integral_mono hi.norm (hpi.const_mul M) hpoint
    _ = M*∫s,∏j,f j s ∂ν := integral_const_mul _ _
    _ ≤ M*((d:ℝ)*C) := mul_le_mul_of_nonneg_left hpb (Real.exp_pos _).le
    _ = _ := by dsimp [M,C]; ring


theorem expectedChargedObservable_homogeneous_growth {d : ℕ}
    (ν : Measure AnchoredCountingState) [IsProbabilityMeasure ν] (β : ℝ)
    (hh : ExactHierarchy ν β) {a : ℝ} (ha : 0<a)
    (he : Integrable (fun s : AnchoredCountingState => Real.exp (a*‖s.val.2‖^2)) ν)
    (c : Fin d → ℝ) (b z : Fin d → ℂ)
    (hz : ∀ j, (z j).im ≠ 0) (hd : ChargedDomain (fun j => (c j : ℂ)) b z)
    (hneutral : ∑ j, c j = 0) {B : ℂ} (hB : 0 < B.im)
    (hb : ∀ j, upperRepresentative (b j) = B) :
    ∃ C : ℝ, 0≤C ∧ ∀r : ℝ, 0<r →
      ‖expectedChargedObservable ν (fun j => (c j : ℂ)) b (fun j => (r:ℂ)*z j)‖ ≤
        C * Real.exp (r*(-∑ j,c j*|(z j).im|)) := by
  by_cases hd0 : d=0
  · subst d
    refine ⟨1,zero_le_one,?_⟩
    intro r hr
    simp [expectedChargedObservable,chargedObservable]
  have hdim := Nat.pos_of_ne_zero hd0
  let cost := fun j => ‖upperRepresentative (z j)-Complex.I‖/min |(z j).im| 1
  let D := ∑j,cost j
  let K := ∑j,|c j|
  have hmin j : 0<min |(z j).im| 1 := lt_min (abs_pos.mpr (hz j)) zero_lt_one
  have hcost0 j : 0≤cost j := div_nonneg (norm_nonneg _) (hmin j).le
  have hD : 0≤D := Finset.sum_nonneg (fun j _ => hcost0 j)
  have hK : 0≤K := Finset.sum_nonneg (fun j _ => abs_nonneg _)
  have hcost j : ‖upperRepresentative (z j)-Complex.I‖≤D*min |(z j).im| 1 := by
    apply (div_le_iff₀ (hmin j)).mp
    exact Finset.single_le_sum (fun j _ => hcost0 j) (Finset.mem_univ j)
  have hcoef j : |c j|≤K := Finset.single_le_sum (f := fun j => |c j|) (fun j _ => abs_nonneg _) (Finset.mem_univ j)
  refine ⟨(d:ℝ)*(2*Real.exp (((d:ℝ)*K*D)^2/(4*bulkExponentialScale β))),by positivity,?_⟩
  intro r hr
  have hzr j : (((r:ℂ)*z j):ℂ).im≠0 := by simpa using mul_ne_zero hr.ne' (hz j)
  have hdom : ChargedDomain (fun j => (c j : ℂ)) b (fun j => (r:ℂ)*z j) := by
    refine ⟨hd.1,?_⟩
    intro j hj
    rcases hd.2 j hj with h | h
    · exact Or.inl ⟨by simpa using mul_pos hr h.1,h.2⟩
    · exact Or.inr ⟨by simpa using mul_neg_of_pos_of_neg hr h.1,h.2⟩
  have hratio j : ‖upperRepresentative ((r:ℂ)*z j)-(r:ℂ)*Complex.I‖≤
      D*min |(((r:ℂ)*z j):ℂ).im| (((r:ℂ)*Complex.I):ℂ).im := by
    have h := reflected_ratio_cost_real_mul hr.le
      (show ‖upperRepresentative (z j)-upperRepresentative Complex.I‖≤
        D*min |(z j).im| |Complex.I.im| by simpa [upperRepresentative] using hcost j)
    simpa [upperRepresentative_real_mul _ hr.le, upperRepresentative, abs_of_pos hr, mul_comm Complex.I] using h
  have h := expectedChargedObservable_growth hdim ν β hh ha he c b
    (fun j => (r:ℂ)*z j) hzr hdom hneutral hB
    (show 0 < (((r:ℂ)*Complex.I):ℂ).im by simpa) hb hD hK hcoef hratio
  convert h using 1
  congr 2
  simp only [Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,add_zero,
    abs_mul,abs_of_pos hr,Finset.mul_sum, Finset.sum_neg_distrib]
  rw [mul_neg, neg_inj, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

end BourgadeHuang.RationalBulk
