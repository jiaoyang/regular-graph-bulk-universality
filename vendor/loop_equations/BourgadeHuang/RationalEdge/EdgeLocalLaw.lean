import BourgadeHuang.RationalEdge.EdgeQuadratic
import BourgadeHuang.RationalEdge.EdgeStability

/-! The genuine general-beta edge local law. The single-derivative hierarchy term is
absorbed with an explicit constant depending on the two loop coefficients. -/
noncomputable section
open scoped BigOperators
open MeasureTheory
namespace BourgadeHuang.RationalEdge

/-- The quadratic moment satisfies a scalar self-consistency estimate.
Only the exact hierarchy and one actual exponential-square anchor moment enter. -/
theorem edgeQuadratic_moment_bootstrap
    (ν : Measure AnchoredCountingState) [IsProbabilityMeasure ν] (β : ℝ)
    (hh : ExactHierarchy ν β) {a : ℝ} (ha : 0<a)
    (he : Integrable (fun s : AnchoredCountingState => Real.exp (a*‖s.val.2‖^2)) ν)
    {w : ℂ} (hw : 0<w.im) (n : ℕ) :
    let A := ∫ s, ‖edgeQuadratic s w‖^(2*(n+1)) ∂ν
    A ≤ 2 * (8*localLawConstant β*((n:ℝ)+1)/w.im^2)^(n+1) * (‖w‖^(n+1)+Real.sqrt A) := by
  have hconstant : 0 ≤ localLawConstant β := (localLawConstant_pos β).le
  let A := ∫ s, ‖edgeQuadratic s w‖^(2*(n+1)) ∂ν
  let C := localLawConstant β*((n:ℝ)+1)/w.im^2
  have hC : 0≤C := by dsimp [C]; positivity
  have hQ (k : ℕ) := integrable_norm_pow_of_anchoredGrowth ν ha he
    (continuous_edgeQuadratic hw.ne') (anchoredGrowth_edgeQuadratic hw.ne') k
  have hS (k : ℕ) := integrable_norm_pow_of_anchoredGrowth ν ha he
    (continuous_anchoredNevanlinna hw.ne') (anchoredGrowth_nevanlinna hw.ne') k
  have hM : Integrable (fun s => ‖anchoredNevanlinna s w‖^2 * ‖edgeQuadratic s w‖^(2*n)) ν := by
    simpa only [norm_mul,norm_pow] using (integrable_of_anchoredGrowth ν ha he
      (((continuous_anchoredNevanlinna hw.ne').pow 2).mul ((continuous_edgeQuadratic hw.ne').pow (2*n)))
      (((anchoredGrowth_nevanlinna hw.ne').pow 2).mul ((anchoredGrowth_edgeQuadratic hw.ne').pow (2*n)))).norm
  have hpoint (s : AnchoredCountingState) :
      C*(‖anchoredNevanlinna s w‖^2 * ‖edgeQuadratic s w‖^(2*n)) ≤
      ‖edgeQuadratic s w‖^(2*(n+1))/2 +
        (2*C)^(n+1)*‖anchoredNevanlinna s w‖^(2*(n+1)) := by
    have ht := localLaw_young_nat n (mul_nonneg hC (sq_nonneg ‖anchoredNevanlinna s w‖))
      (sq_nonneg ‖edgeQuadratic s w‖)
    convert ht using 1 <;> simp only [mul_pow,pow_mul] <;> ring
  have hyoung := integral_mono (hM.const_mul C)
    ((hQ (2*(n+1))).div_const 2 |>.add ((hS (2*(n+1))).const_mul ((2*C)^(n+1)))) hpoint
  simp only [Pi.add_apply] at hyoung
  rw [integral_const_mul,integral_add ((hQ (2*(n+1))).div_const 2)
    ((hS (2*(n+1))).const_mul ((2*C)^(n+1))),integral_div,integral_const_mul] at hyoung
  have hboot0 := integral_edgeQuadratic_even_le_mixed ν β hh ha he hw n
  change A ≤ C*(∫ s, ‖anchoredNevanlinna s w‖^2 * ‖edgeQuadratic s w‖^(2*n) ∂ν) at hboot0
  have hboot1 : A ≤ 2*(2*C)^(n+1)*(∫ s, ‖anchoredNevanlinna s w‖^(2*(n+1)) ∂ν) := by
    dsimp only [A] at *
    linarith
  have hsbound : (∫ s, ‖anchoredNevanlinna s w‖^(2*(n+1)) ∂ν) ≤
      4^(n+1)*(‖w‖^(n+1)+∫ s, ‖edgeQuadratic s w‖^(n+1) ∂ν) := by
    calc
      _ ≤ ∫ s, 4^(n+1)*(‖w‖^(n+1)+‖edgeQuadratic s w‖^(n+1)) ∂ν := by
        apply integral_mono (hS (2*(n+1))) (((integrable_const (‖w‖^(n+1))).add (hQ (n+1))).const_mul _)
        exact fun s => edge_resolvent_even_power_le (anchoredNevanlinna s w) w (n+1)
      _ = _ := by rw [integral_const_mul,integral_add (integrable_const (‖w‖^(n+1))) (hQ (n+1))]; simp
  have hcs : (∫ s, ‖edgeQuadratic s w‖^(n+1) ∂ν) ≤ Real.sqrt A := by
    have ht := integral_le_sqrt_integral_sq ν (hQ (n+1))
      (show Integrable (fun s => (‖edgeQuadratic s w‖^(n+1))^2) ν from
        by simpa only [← pow_mul, Nat.mul_comm (n+1) 2] using hQ (2*(n+1)))
      (fun s => by positivity)
    simpa only [A,← pow_mul,Nat.mul_comm (n+1) 2] using ht
  calc
    A ≤ 2*(2*C)^(n+1)*(4^(n+1)*(‖w‖^(n+1)+∫ s, ‖edgeQuadratic s w‖^(n+1) ∂ν)) :=
      hboot1.trans (mul_le_mul_of_nonneg_left hsbound (by positivity))
    _ ≤ 2*(2*C)^(n+1)*(4^(n+1)*(‖w‖^(n+1)+Real.sqrt A)) := by gcongr
    _ = 2*((2*C)*4)^(n+1)*(‖w‖^(n+1)+Real.sqrt A) := by simp only [mul_pow]; ring
    _ = _ := by
      have hc : (2*C)*4 = 8*localLawConstant β*((n:ℝ)+1)/w.im^2 := by dsimp [C]; ring
      rw [hc]

/-- One constant simultaneously controls both edge stability regimes. -/
def edgeStabilityConstant (K : ℝ) : ℝ := 1 + 2*K + K^2

theorem edgeStabilityConstant_pos {K : ℝ} (hK : 0 ≤ K) :
    0 < edgeStabilityConstant K := by
  unfold edgeStabilityConstant
  positivity

/-- The edge local law on any fixed root sector.  The root is specified
algebraically, so the statement does not depend on a square-root API or branch
notation.  Its positive imaginary part selects the Nevanlinna-compatible root. -/
theorem edge_localLaw_even_moment
    (ν : Measure AnchoredCountingState) [IsProbabilityMeasure ν] (β : ℝ)
    (hh : ExactHierarchy ν β) {a : ℝ} (ha : 0<a)
    (he : Integrable (fun s : AnchoredCountingState => Real.exp (a*‖s.val.2‖^2)) ν)
    {w r : ℂ} {K : ℝ} (hw : 0<w.im) (hr2 : r^2=w)
    (hr : 0<r.im) (hK : 0≤K) (hsector : ‖r‖≤K*r.im) (n : ℕ) :
    Integrable (fun s => ‖anchoredNevanlinna s w-r‖^(2*(n+1))) ν ∧
    (∫ s, ‖anchoredNevanlinna s w-r‖^(2*(n+1)) ∂ν) ≤
      (32*localLawConstant β*edgeStabilityConstant K*((n:ℝ)+1))^(n+1)/
        w.im^(2*(n+1)) := by
  have hconstant : 0 ≤ localLawConstant β := (localLawConstant_pos β).le
  let A := ∫ s, ‖edgeQuadratic s w‖^(2*(n+1)) ∂ν
  let B := ∫ s, ‖anchoredNevanlinna s w-r‖^(2*(n+1)) ∂ν
  let D := 2*(8*localLawConstant β*((n:ℝ)+1)/w.im^2)^(n+1)
  let J := edgeStabilityConstant K
  have hJ : 0≤J := (edgeStabilityConstant_pos hK).le
  have hD : 0≤D := by dsimp [D]; positivity
  have hA : 0≤A := integral_nonneg (fun s => by positivity)
  have hQ (k : ℕ) := integrable_norm_pow_of_anchoredGrowth ν ha he
    (continuous_edgeQuadratic hw.ne') (anchoredGrowth_edgeQuadratic hw.ne') k
  have hBint := integrable_norm_pow_of_anchoredGrowth ν ha he
    ((continuous_anchoredNevanlinna hw.ne').sub continuous_const)
    ((anchoredGrowth_nevanlinna hw.ne').sub
      ((AnchoredGrowth.const r).mono (by omega))) (2*(n+1))
  refine ⟨hBint, ?_⟩
  have hBA : B*r.im^(2*(n+1))≤A := by
    have hp (s : AnchoredCountingState) :
        ‖anchoredNevanlinna s w-r‖^(2*(n+1))*r.im^(2*(n+1)) ≤
          ‖edgeQuadratic s w‖^(2*(n+1)) := by
      rw [← mul_pow]
      apply pow_le_pow_left₀ (mul_nonneg (norm_nonneg _) hr.le)
      exact (le_div_iff₀ hr).mp
        (edge_linear_stability (anchoredNevanlinna_im_nonneg s hw) hr hr2)
    have hi := integral_mono (hBint.mul_const _) (hQ (2*(n+1))) hp
    simpa only [integral_mul_const] using hi
  have hcs : (∫ s, ‖edgeQuadratic s w‖^(n+1) ∂ν) ≤ Real.sqrt A := by
    have ht := integral_le_sqrt_integral_sq ν (hQ (n+1))
      (show Integrable (fun s => (‖edgeQuadratic s w‖^(n+1))^2) ν from
        by simpa only [← pow_mul, Nat.mul_comm (n+1) 2] using hQ (2*(n+1)))
      (fun s => by positivity)
    simpa only [A,← pow_mul,Nat.mul_comm (n+1) 2] using ht
  have hBR : B≤J^(n+1)*Real.sqrt A := by
    have hp (s : AnchoredCountingState) :
        ‖anchoredNevanlinna s w-r‖^(2*(n+1)) ≤
          J^(n+1)*‖edgeQuadratic s w‖^(n+1) := by
      have hb : ‖anchoredNevanlinna s w-r‖^2 ≤ J*‖edgeQuadratic s w‖ := by
        apply (edge_quadratic_stability (anchoredNevanlinna_im_nonneg s hw)
          hK hsector hr2).trans
        exact mul_le_mul_of_nonneg_right
          (by dsimp [J,edgeStabilityConstant]; nlinarith [sq_nonneg K]) (norm_nonneg _)
      have hp := pow_le_pow_left₀ (sq_nonneg _) hb (n+1)
      simpa only [pow_mul,mul_pow] using hp
    calc
      B ≤ ∫ s, J^(n+1)*‖edgeQuadratic s w‖^(n+1) ∂ν :=
        integral_mono hBint ((hQ (n+1)).const_mul _) hp
      _ = J^(n+1)*(∫ s, ‖edgeQuadratic s w‖^(n+1) ∂ν) := integral_const_mul _ _
      _ ≤ J^(n+1)*Real.sqrt A :=
        mul_le_mul_of_nonneg_left hcs (pow_nonneg hJ _)
  have hw0 : w ≠ 0 := by intro hz; simp [hz] at hw
  have hR : 0<‖w‖^(n+1) := pow_pos (norm_pos_iff.mpr hw0) _
  have hW : ‖w‖^(n+1) ≤ J^(n+1)*r.im^(2*(n+1)) := by
    have hroot : ‖r‖^2 ≤ J*r.im^2 := by
      have hs := pow_le_pow_left₀ (norm_nonneg r) hsector 2
      rw [mul_pow] at hs
      apply hs.trans
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      dsimp [J,edgeStabilityConstant]
      nlinarith
    rw [edge_root_norm_sq hr2]
    simpa only [mul_pow,pow_mul] using
      pow_le_pow_left₀ (sq_nonneg ‖r‖) hroot (n+1)
  have hboot : A ≤ D*(‖w‖^(n+1)+Real.sqrt A) :=
    edgeQuadratic_moment_bootstrap ν β hh ha he hw n
  have hb : B≤2*D*J^(n+1) := by
    rcases edge_scalar_absorption hA hD hR hboot with hs | hl
    · have ht := hBA.trans (hs.trans
        (mul_le_mul_of_nonneg_left hW (mul_nonneg (by norm_num) hD)))
      apply (mul_le_mul_right (pow_pos hr (2*(n+1)))).mp
      nlinarith only [ht]
    · have ht := hBR.trans
        (mul_le_mul_of_nonneg_left hl (pow_nonneg hJ _))
      nlinarith only [ht]
  calc
    B ≤ 4*(8*localLawConstant β*((n:ℝ)+1)/w.im^2)^(n+1)*J^(n+1) := by
      convert hb using 1
      dsimp [D]
      ring
    _ ≤ 4^(n+1)*(8*localLawConstant β*((n:ℝ)+1)/w.im^2)^(n+1)*J^(n+1) := by
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg hJ _)
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      simpa using pow_le_pow_right₀ (by norm_num : (1:ℝ)≤4) (show 1≤n+1 by omega)
    _ = _ := by
      rw [← mul_pow,← mul_pow]
      have hc : 4*(8*localLawConstant β*((n:ℝ)+1)/w.im^2)*J =
          (32*localLawConstant β*edgeStabilityConstant K*((n:ℝ)+1))/w.im^2 := by
        dsimp [J]
        ring
      rw [hc,div_pow,pow_mul]

/-- The unrestricted edge estimate (3.8), written with an arbitrary square
root having positive imaginary part.  Its root-ratio loss is explicit. -/
theorem edge_localLaw_even_moment_global
    (ν : Measure AnchoredCountingState) [IsProbabilityMeasure ν] (β : ℝ)
    (hh : ExactHierarchy ν β) {a : ℝ} (ha : 0<a)
    (he : Integrable (fun s : AnchoredCountingState => Real.exp (a*‖s.val.2‖^2)) ν)
    {w r : ℂ} (hw : 0<w.im) (hr2 : r^2=w) (hr : 0<r.im) (n : ℕ) :
    Integrable (fun s => ‖anchoredNevanlinna s w-r‖^(2*(n+1))) ν ∧
    (∫ s, ‖anchoredNevanlinna s w-r‖^(2*(n+1)) ∂ν) ≤
      (128*localLawConstant β*((n:ℝ)+1))^(n+1)*‖w‖^(n+1)/
        (w.im^(2*(n+1))*r.im^(2*(n+1))) := by
  let K := ‖r‖/r.im
  have hK : 0≤K := div_nonneg (norm_nonneg _) hr.le
  have hK1 : 1≤K := by
    apply (le_div_iff₀ hr).2
    simpa only [one_mul] using
      (le_abs_self r.im).trans (Complex.abs_im_le_norm r)
  have hsector : ‖r‖≤K*r.im := by
    dsimp [K]
    rw [div_mul_cancel₀ _ hr.ne']
  obtain ⟨hi,hb⟩ := edge_localLaw_even_moment ν β hh ha he hw hr2 hr hK hsector n
  refine ⟨hi, hb.trans ?_⟩
  have hJ : edgeStabilityConstant K≤4*K^2 := by
    dsimp [edgeStabilityConstant]
    nlinarith [sq_nonneg (K-1)]
  have hL := (localLawConstant_pos β).le
  have hcompare : 32*localLawConstant β*edgeStabilityConstant K*((n:ℝ)+1) ≤
      (128*localLawConstant β*((n:ℝ)+1))*K^2 := by
    have ht := mul_le_mul_of_nonneg_left hJ
      (show 0≤32*localLawConstant β*((n:ℝ)+1) by positivity)
    nlinarith only [ht]
  calc
    _ ≤ ((128*localLawConstant β*((n:ℝ)+1))*K^2)^(n+1)/w.im^(2*(n+1)) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact pow_le_pow_left₀ (by have := (edgeStabilityConstant_pos hK).le; positivity)
        hcompare (n+1)
    _ = _ := by
      dsimp only [K]
      rw [mul_pow,div_pow,pow_mul,edge_root_norm_sq hr2,pow_mul]
      ring

end BourgadeHuang.RationalEdge
