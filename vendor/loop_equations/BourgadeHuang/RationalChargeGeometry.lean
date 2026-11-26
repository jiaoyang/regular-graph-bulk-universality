import BourgadeHuang.CMS.TwoScalePhase
import BourgadeHuang.CMS.GeneralBranchDegree

/-! The physical charge geometry for arbitrary positive rational coupling.
The numerator and denominator cardinalities are independent. Neutrality is
exactly `n = beta*m/2`, and the signed branch degree is an explicit square. -/
noncomputable section
open scoped BigOperators Topology
open Set Filter
namespace BourgadeHuang.RationalBulk

def realCharges (beta : ℝ) (n m : ℕ) : Fin (n+m) → ℝ :=
  Fin.append (fun _ => -1) (fun _ => beta/2)

def charges (beta : ℝ) (n m : ℕ) : Fin (n+m) → ℂ :=
  fun i => (realCharges beta n m i : ℂ)

theorem charges_physical (beta : ℝ) (n m : ℕ) (i : Fin (n+m)) :
    charges beta n m i = -1 ∨ charges beta n m i = (beta:ℂ)/2 := by
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
    simp [charges, realCharges]

theorem sum_realCharges (beta : ℝ) (n m : ℕ) :
    (∑ i, realCharges beta n m i) = -(n:ℝ)+(m:ℝ)*beta/2 := by
  simp only [realCharges, Fin.sum_univ_add, Fin.append_left, Fin.append_right,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

theorem neutral_rational {beta : ℝ} {p q k : ℕ}
    (h : beta * (q:ℝ) = 2*(p:ℝ)) :
    (∑ i, realCharges beta (k*p) (k*q) i) = 0 := by
  rw [sum_realCharges]
  push_cast
  nlinarith

theorem signedCharge_eq (beta : ℝ) {n m : ℕ}
    (epsilon : Fin n → CMS.Sign) (eta : Fin m → CMS.Sign) :
    (∑ i, realCharges beta n m i * CMS.realSign (Fin.append epsilon eta i)) =
      -(2*(CMS.signCount epsilon true:ℝ)-n) +
        (beta/2)*(2*(CMS.signCount eta true:ℝ)-m) := by
  simp only [realCharges, Fin.sum_univ_add, Fin.append_left, Fin.append_right,
    neg_one_mul, Finset.sum_neg_distrib, ← Finset.mul_sum]
  rw [OrthogonalCMS.sum_realSign, OrthogonalCMS.sum_realSign]

theorem signedCharge_neutral (beta : ℝ) {n m : ℕ}
    (hn : (n:ℝ) = (m:ℝ)*beta/2)
    (epsilon : Fin n → CMS.Sign) (eta : Fin m → CMS.Sign) :
    (∑ i, realCharges beta n m i * CMS.realSign (Fin.append epsilon eta i)) =
      beta*(CMS.signCount eta true:ℝ)-2*(CMS.signCount epsilon true:ℝ) := by
  rw [signedCharge_eq]
  linarith

theorem branch_degree {beta : ℝ} (hbeta : 0<beta) {n m : ℕ}
    (hn : (n:ℝ) = (m:ℝ)*beta/2)
    (epsilon : Fin n → CMS.Sign) (eta : Fin m → CMS.Sign) :
    CMS.generalRayDegree (beta:ℂ) (charges beta n m) (Fin.append epsilon eta) =
      (((beta*(CMS.signCount eta true:ℝ)-2*(CMS.signCount epsilon true:ℝ))^2 /
        (2*beta):ℝ):ℂ) := by
  unfold charges
  rw [CMS.generalRayDegree_real hbeta.ne', sum_realCharges,
    signedCharge_neutral beta hn, hn]
  simp

theorem branch_degree_pos_iff {beta : ℝ} (hbeta : 0<beta) {n m : ℕ}
    (hn : (n:ℝ) = (m:ℝ)*beta/2)
    (epsilon : Fin n → CMS.Sign) (eta : Fin m → CMS.Sign) :
    0 < (CMS.generalRayDegree (beta:ℂ) (charges beta n m) (Fin.append epsilon eta)).re ↔
      beta*(CMS.signCount eta true:ℝ) ≠ 2*(CMS.signCount epsilon true:ℝ) := by
  rw [branch_degree hbeta hn, Complex.ofReal_re]
  exact (div_pos_iff_of_pos_right (by positivity)).trans (sq_pos_iff.trans sub_ne_zero)

theorem branch_degree_zero {beta : ℝ} (hbeta : 0<beta) {n m : ℕ}
    (hn : (n:ℝ) = (m:ℝ)*beta/2)
    (epsilon : Fin n → CMS.Sign) (eta : Fin m → CMS.Sign)
    (hbal : beta*(CMS.signCount eta true:ℝ) = 2*(CMS.signCount epsilon true:ℝ)) :
    CMS.generalRayDegree (beta:ℂ) (charges beta n m) (Fin.append epsilon eta) = 0 := by
  rw [branch_degree hbeta hn, hbal]
  simp

theorem twoScalePhase_re (beta : ℝ) {n m : ℕ}
    (xi : Fin (n+m) → ℝ) (epsilon : Fin n → CMS.Sign) (eta : Fin m → CMS.Sign)
    (b d : ℝ) (k : ℕ) (tau : Fin (n+m) → CMS.Sign) (r : ℝ) :
    (CMS.generalRayPhase (charges beta n m) tau
      (CMS.twoScaleRay xi (Fin.append (fun _=>b) (fun _=>d)) (Fin.append epsilon eta) k r)).re =
      (∑i,CMS.realSign (tau (Fin.castAdd m i))*CMS.realSign (epsilon i))*(r^(k+2)+r*b)-
      (beta/2)*(∑j,CMS.realSign (tau (Fin.natAdd n j))*CMS.realSign (eta j))*(r^(k+2)+r*d) := by
  unfold charges
  rw [CMS.generalRayPhase_twoScale_real, Fin.sum_univ_add]
  simp only [realCharges, Fin.append_left, Fin.append_right, neg_one_mul, neg_mul,
    Finset.sum_neg_distrib, Finset.sum_mul, ← Finset.mul_sum, mul_assoc]
  ring

theorem twoScalePhase_target (beta : ℝ) {n m : ℕ}
    (xi : Fin (n+m) → ℝ) (epsilon : Fin n → CMS.Sign) (eta : Fin m → CMS.Sign)
    (b d : ℝ) (k : ℕ) (r : ℝ) :
    (CMS.generalRayPhase (charges beta n m) (Fin.append epsilon eta)
      (CMS.twoScaleRay xi (Fin.append (fun _=>b) (fun _=>d)) (Fin.append epsilon eta) k r)).re =
      (n:ℝ)*(r^(k+2)+r*b)-(m:ℝ)*beta/2*(r^(k+2)+r*d) := by
  rw [twoScalePhase_re]
  have hs (s : CMS.Sign) : CMS.realSign s * CMS.realSign s = 1 := by
    cases s <;> norm_num [CMS.realSign]
  simp only [Fin.append_left, Fin.append_right, hs, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one]
  ring

theorem twoScalePhase_gap (beta : ℝ) {n m : ℕ}
    (xi : Fin (n+m) → ℝ) (epsilon : Fin n → CMS.Sign) (eta : Fin m → CMS.Sign)
    (b d : ℝ) (k : ℕ) (tau : Fin (n+m) → CMS.Sign) (hb : 0≤b)
    (hden : ∀j,tau (Fin.natAdd n j)=eta j) (hne : tau≠Fin.append epsilon eta) :
    ∃e : ℝ,0<e ∧ ∀ᶠr : ℝ in atTop,
      (CMS.generalRayPhase (charges beta n m) tau
        (CMS.twoScaleRay xi (Fin.append (fun _=>b) (fun _=>d)) (Fin.append epsilon eta) k r)-
       CMS.generalRayPhase (charges beta n m) (Fin.append epsilon eta)
        (CMS.twoScaleRay xi (Fin.append (fun _=>b) (fun _=>d)) (Fin.append epsilon eta) k r)).re ≤ -e*r := by
  classical
  have hex : ∃i : Fin n,tau (Fin.castAdd m i)≠epsilon i := by
    by_contra hh
    push_neg at hh
    apply hne
    funext i
    refine Fin.addCases (fun j=>?_) (fun j=>?_) i
    · simpa only [Fin.append_left] using hh j
    · simpa only [Fin.append_right] using hden j
  obtain ⟨i₀,hi₀⟩ := hex
  let gain : Fin n → ℝ := fun i => 1-CMS.realSign (tau (Fin.castAdd m i))*CMS.realSign (epsilon i)
  have hg (i : Fin n) : 0≤gain i := by
    cases hs : tau (Fin.castAdd m i) <;> cases ht : epsilon i <;>
      norm_num [gain,CMS.realSign,hs,ht]
  have hg₀ : gain i₀=2 := by
    cases hs : tau (Fin.castAdd m i₀) <;> cases ht : epsilon i₀ <;>
      simp_all [gain,CMS.realSign] <;> norm_num
  have hsum : 2≤∑i,gain i := by
    rw [←hg₀]
    exact Finset.single_le_sum (fun i _=>hg i) (Finset.mem_univ _)
  have hs : (∑i,gain i)=(n:ℝ)-∑i,CMS.realSign (tau (Fin.castAdd m i))*CMS.realSign (epsilon i) := by
    simp [gain,Finset.sum_sub_distrib]
  refine ⟨2,by norm_num,?_⟩
  filter_upwards [eventually_ge_atTop (1:ℝ)] with r hr
  have hr0 : 0≤r := zero_le_one.trans hr
  have hp : r≤r^(k+2) := le_self_pow₀ hr (by omega)
  have hh : r≤r^(k+2)+r*b := by nlinarith
  rw [Complex.sub_re,twoScalePhase_re,twoScalePhase_target]
  have hsign (j : Fin m) : CMS.realSign (tau (Fin.natAdd n j))*CMS.realSign (eta j)=1 := by
    rw [hden]
    cases ht : eta j <;> norm_num [CMS.realSign,ht]
  simp only [hsign,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one]
  nlinarith

end BourgadeHuang.RationalBulk
