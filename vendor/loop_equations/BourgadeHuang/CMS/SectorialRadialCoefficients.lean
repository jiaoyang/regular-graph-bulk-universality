import BourgadeHuang.CMS.SectorialRows
import BourgadeHuang.CMS.ShiftedRays

/-! Actual homogeneous coefficients on separated rays. Their bounded part is
strictly degree-lowering, and their remaining part carries a factor 1/t. -/
noncomputable section
open scoped BigOperators Topology
open Set Filter
namespace BourgadeHuang.CMS

/-- The shifted ray parametrized by its total separation scale. -/
def sectorialRay {d : ℕ} (σ : Fin d → Sign) (z : Point d) (R t : ℝ) : Point d :=
  shiftedRay σ z (t-R)

theorem sectorialRay_mem {d : ℕ} (σ : Fin d → Sign) {z : Point d} {R t : ℝ}
    (hz : z∈OrderedDomain d) (ht : R≤t) : sectorialRay σ z R t∈OrderedDomain d := by
  apply orderedGapDomain_subset_orderedDomain (D := 0) le_rfl
  apply shiftedRay_mem_orderedGapDomain σ _ (sub_nonneg.mpr ht)
  intro i j hij
  simpa only [Complex.sub_re,sub_pos] using hz i j hij

theorem sectorialRay_separation {d : ℕ} (σ : Fin d → Sign) {z : Point d} {R t : ℝ}
    (hz : z∈OrderedDomain d) (hsep : ∀i j,i≠j→R≤‖z i-z j‖) (ht : R≤t) :
    ∀i j,i≠j→t/4≤‖sectorialRay σ z R t i-sectorialRay σ z R t j‖ := by
  simpa only [sectorialRay,add_sub_cancel] using shiftedRay_separation σ hz hsep (sub_nonneg.mpr ht)

namespace SquareFreeTerm

def scaledCoefficient {d : ℕ} (a : SquareFreeTerm d) (z : Point d) (t : ℂ) : ℂ :=
  t^a.weight*a.coefficient.eval z

/-- The coefficient bound is independent of the radial parameter. -/
theorem norm_scaledCoefficient_le {d : ℕ} (a : SquareFreeTerm d)
    {z : Point d} {t : ℝ} (ht : 0<t)
    (hsep : ∀i j,i≠j→t/4≤‖z i-z j‖) :
    ‖a.scaledCoefficient z t‖≤a.coefficient.size*4^a.weight := by
  have hp : 0<t/4 := by positivity
  have hb := GapExpression.norm_eval_le a.homogeneous z hp hsep
  calc
    ‖a.scaledCoefficient z t‖=t^a.weight*‖a.coefficient.eval z‖ := by
      simp only [scaledCoefficient,norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos ht]
    _≤t^a.weight*(a.coefficient.size/(t/4)^a.weight) :=
      mul_le_mul_of_nonneg_left hb (pow_nonneg ht.le _)
    _=a.coefficient.size*4^a.weight := by
      rw [div_pow]
      field_simp

/-- Analyticity is inherited from the actual rational expression. -/
theorem analyticAt_scaledCoefficient {d : ℕ} (a : SquareFreeTerm d) (t : ℂ)
    {z : Point d} (hz : CollisionFree z) :
    AnalyticAt ℂ (fun w => a.scaledCoefficient w t) z :=
  analyticAt_const.mul (GapExpression.analyticAt_eval a.coefficient hz)

theorem continuous_scaledCoefficient_ray {d : ℕ} (a : SquareFreeTerm d)
    (σ : Fin d → Sign) {z : Point d} {R : ℝ} (hz : z∈OrderedDomain d) :
    Continuous (fun t : Ici R => a.scaledCoefficient (sectorialRay σ z R t) (t:ℝ)) := by
  have hr : Continuous (fun t : Ici R => sectorialRay σ z R t) := by
    apply continuous_pi
    intro j
    change Continuous (fun t : Ici R => z j+((t:ℝ)-R : ℝ)*shiftedDirection σ j)
    fun_prop
  have he : Continuous (fun t : Ici R => a.coefficient.eval (sectorialRay σ z R t)) :=
    continuous_iff_continuousAt.mpr (fun t =>
      (GapExpression.analyticAt_eval a.coefficient
        (orderedDomain_collisionFree (sectorialRay_mem σ hz t.property))).continuousAt.comp (f := fun t : Ici R => sectorialRay σ z R t) hr.continuousAt)
  exact ((Complex.continuous_ofReal.comp continuous_subtype_val).pow a.weight).mul he

/-- The two rows are separated by their exact homogeneous degree. -/
def homogeneousEntry {d : ℕ} (ts : List (SquareFreeTerm d)) (n : ℕ)
    (T : Finset (Fin d)) (z : Point d) (t : ℂ) : ℂ :=
  (ts.map (fun a => if a.target=T ∧ a.weight+a.target.card=n then a.scaledCoefficient z t else 0)).sum

def rowBound {d : ℕ} (ts : List (SquareFreeTerm d)) : ℝ :=
  (ts.map (fun a => a.coefficient.size*4^a.weight)).sum

theorem rowBound_nonneg {d : ℕ} (ts : List (SquareFreeTerm d)) : 0≤rowBound ts := by
  apply List.sum_nonneg
  intro x hx
  obtain ⟨a,_,rfl⟩ := List.mem_map.mp hx
  exact mul_nonneg a.coefficient.size_nonneg (pow_nonneg (by norm_num) _)

theorem norm_homogeneousEntry_le {d : ℕ} (ts : List (SquareFreeTerm d)) (n : ℕ)
    (T : Finset (Fin d)) {z : Point d} {t : ℝ} (ht : 0<t)
    (hsep : ∀i j,i≠j→t/4≤‖z i-z j‖) :
    ‖homogeneousEntry ts n T z t‖≤rowBound ts := by
  induction ts with
  | nil => simp [homogeneousEntry,rowBound]
  | cons a ts ih =>
    change ‖(if a.target=T ∧ a.weight+a.target.card=n then a.scaledCoefficient z t else 0)+
      homogeneousEntry ts n T z t‖≤a.coefficient.size*4^a.weight+rowBound ts
    apply (norm_add_le _ _).trans
    apply add_le_add _ ih
    split
    · exact a.norm_scaledCoefficient_le ht hsep
    · simpa using mul_nonneg a.coefficient.size_nonneg (pow_nonneg (by norm_num : (0:ℝ)≤4) a.weight)

theorem homogeneousEntry_low_eq_zero {d n : ℕ} (ts : List (SquareFreeTerm d))
    (h : ∀a∈ts,a.IsCorrection n) (T : Finset (Fin d)) (z : Point d) (t : ℂ)
    (hT : ¬T.card<n) : homogeneousEntry ts n T z t=0 := by
  apply List.sum_eq_zero
  intro x hx
  obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hx
  split_ifs with he
  · exact False.elim (hT (he.1 ▸ (h a ha).target_card_lt_of_low he.2))
  · rfl

/-- The bounded triangular part has no column for the empty derivative. -/
theorem homogeneousEntry_low_empty {d n : ℕ} (ts : List (SquareFreeTerm d))
    (h : ∀a∈ts,a.IsCorrection n) (z : Point d) (t : ℂ) :
    homogeneousEntry ts n ∅ z t=0 := by
  apply List.sum_eq_zero
  intro x hx
  obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hx
  split_ifs with he
  · obtain ⟨_,hh⟩ := h a ha
    rcases hh with ⟨_,hn⟩|hn
    · exact False.elim (by simp [he.1] at hn)
    · omega
  · rfl

theorem continuous_homogeneousEntry_ray {d : ℕ} (ts : List (SquareFreeTerm d)) (n : ℕ)
    (T : Finset (Fin d)) (σ : Fin d → Sign) {z : Point d} {R : ℝ} (hz : z∈OrderedDomain d) :
    Continuous (fun t : Ici R => homogeneousEntry ts n T (sectorialRay σ z R t) (t:ℝ)) := by
  induction ts with
  | nil => exact continuous_const
  | cons a ts ih =>
    change Continuous (fun t : Ici R =>
      (if a.target=T ∧ a.weight+a.target.card=n then a.scaledCoefficient (sectorialRay σ z R t) (t:ℝ) else 0)+
        homogeneousEntry ts n T (sectorialRay σ z R t) (t:ℝ))
    split_ifs
    · exact (a.continuous_scaledCoefficient_ray σ hz).add ih
    · exact continuous_const.add ih


/-- Matrix action of one homogeneous slice of the correction terms. -/
theorem homogeneousEntry_action {d : ℕ} (ts : List (SquareFreeTerm d)) (n : ℕ)
    (X : Finset (Fin d) → ℂ) (z : Point d) (t : ℂ) :
    (∑T : Finset (Fin d),homogeneousEntry ts n T z t*X T)=
      (ts.map (fun a => if a.weight+a.target.card=n then a.scaledCoefficient z t*X a.target else 0)).sum := by
  classical
  induction ts with
  | nil => simp [homogeneousEntry]
  | cons a ts ih =>
    change (∑T : Finset (Fin d),
      ((if a.target=T ∧ a.weight+a.target.card=n then a.scaledCoefficient z t else 0)+
        homogeneousEntry ts n T z t)*X T)=_
    simp only [add_mul,Finset.sum_add_distrib,List.map_cons,List.sum_cons]
    rw [ih]
    congr 1
    by_cases ha : a.weight+a.target.card=n
    · simp [ha,ite_mul]
    · simp [ha]

/-- Exact splitting of a single scaled term into bounded and reciprocal parts. -/
theorem scaled_term_split {d n : ℕ} (a : SquareFreeTerm d) (ha : a.IsCorrection n)
    (z : Point d) {t : ℂ} (ht : t≠0) (b : ℂ) :
    t^n*a.coefficient.eval z*b=
      (if a.weight+a.target.card=n then a.scaledCoefficient z t*(t^a.target.card*b) else 0)+
      t⁻¹*(if a.weight+a.target.card=n+1 then a.scaledCoefficient z t*(t^a.target.card*b) else 0) := by
  obtain ⟨_,ha⟩ := ha
  rcases ha with ⟨ha,_⟩|ha
  · have hn : a.weight+a.target.card≠n+1 := by omega
    rw [if_pos ha,if_neg hn,mul_zero,add_zero]
    unfold scaledCoefficient
    rw [← ha,pow_add]
    ring
  · have hn : a.weight+a.target.card≠n := by omega
    rw [if_neg hn,if_pos ha,zero_add]
    unfold scaledCoefficient
    have hp : t^a.weight*t^a.target.card=t^(n+1) := by rw [← pow_add,ha]
    calc
      t^n*a.coefficient.eval z*b=t⁻¹*t^(n+1)*a.coefficient.eval z*b := by rw [pow_succ]; field_simp
      _=t⁻¹*(t^a.weight*a.coefficient.eval z*(t^a.target.card*b)) := by rw [← hp]; ring

/-- Exact finite splitting of the scaled correction row. -/
theorem scaled_evalSum_split {d n : ℕ} (ts : List (SquareFreeTerm d))
    (h : ∀a∈ts,a.IsCorrection n) (f : Point d → ℂ) (z : Point d)
    {t : ℂ} (ht : t≠0) :
    t^n*evalSum ts f z=
      (∑T : Finset (Fin d),homogeneousEntry ts n T z t*(t^T.card*squareFreeDerivative T f z))+
      t⁻¹*(∑T : Finset (Fin d),homogeneousEntry ts (n+1) T z t*(t^T.card*squareFreeDerivative T f z)) := by
  rw [homogeneousEntry_action,homogeneousEntry_action]
  induction ts with
  | nil => simp
  | cons a ts ih =>
    rw [evalSum_cons,mul_add]
    simp only [List.map_cons,List.sum_cons]
    rw [show t^n*(a.coefficient.eval z*squareFreeDerivative a.target f z)=
      t^n*a.coefficient.eval z*squareFreeDerivative a.target f z by ring,
      a.scaled_term_split (h a (List.mem_cons_self ..)) z ht,
      ih (fun b hb => h b (List.mem_cons_of_mem _ hb))]
    ring

end SquareFreeTerm
end BourgadeHuang.CMS
