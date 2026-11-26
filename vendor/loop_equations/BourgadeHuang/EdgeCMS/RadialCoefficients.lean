import BourgadeHuang.EdgeCMS.SectorialRows

/-! Exact separation of the homogeneous principal and reciprocal radial
coefficients.  Along pure dilation every scaled coefficient is constant. -/
noncomputable section
open scoped BigOperators Topology
open Set Filter
namespace BourgadeHuang.EdgeCMS
open CMS

namespace SquareFreeTerm

def scaledCoefficient {d : ℕ} {C : OpenCone d} (a : SquareFreeTerm C) (z : Point d) (t : ℂ) : ℂ :=
  t^a.weight*a.coefficient.eval z

/-- The two rows are separated by their exact homogeneous degree. -/
def homogeneousEntry {d : ℕ} {C : OpenCone d} (ts : List (SquareFreeTerm C)) (n : ℕ)
    (T : Finset (Fin d)) (z : Point d) (t : ℂ) : ℂ :=
  (ts.map (fun a => if a.target=T ∧ a.weight+a.target.card=n then a.scaledCoefficient z t else 0)).sum

theorem homogeneousEntry_low_eq_zero {d n : ℕ} {C : OpenCone d} (ts : List (SquareFreeTerm C))
    (h : ∀a∈ts,a.IsCorrection n) (T : Finset (Fin d)) (z : Point d) (t : ℂ)
    (hT : ¬T.card<n) : homogeneousEntry ts n T z t=0 := by
  apply List.sum_eq_zero
  intro x hx
  obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hx
  split_ifs with he
  · exact False.elim (hT (he.1 ▸ (h a ha).target_card_lt_of_low he.2))
  · rfl

/-- The bounded triangular part has no column for the empty derivative. -/
theorem homogeneousEntry_low_empty {d n : ℕ} {C : OpenCone d} (ts : List (SquareFreeTerm C))
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

/-- Matrix action of one homogeneous slice of the correction terms. -/
theorem homogeneousEntry_action {d : ℕ} {C : OpenCone d} (ts : List (SquareFreeTerm C)) (n : ℕ)
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
theorem scaled_term_split {d n : ℕ} {C : OpenCone d} (a : SquareFreeTerm C) (ha : a.IsCorrection n)
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
theorem scaled_evalSum_split {d n : ℕ} {C : OpenCone d} (ts : List (SquareFreeTerm C))
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

theorem scaledCoefficient_dilation {d : ℕ} {C : OpenCone d} (a : SquareFreeTerm C)
    {z : Point d} (hz : z ∈ C.carrier) {t : ℝ} (ht : 0 < t) :
    a.scaledCoefficient ((t : ℂ) • z) t = a.coefficient.eval z := by
  have ht0 : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
  unfold scaledCoefficient
  rw [a.homogeneous ht hz, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ ht0, one_pow, one_mul]

theorem homogeneousEntry_dilation {d : ℕ} {C : OpenCone d}
    (ts : List (SquareFreeTerm C)) (n : ℕ) (T : Finset (Fin d))
    {z : Point d} (hz : z ∈ C.carrier) {t : ℝ} (ht : 0 < t) :
    homogeneousEntry ts n T ((t : ℂ) • z) t = homogeneousEntry ts n T z 1 := by
  unfold homogeneousEntry
  congr 1
  apply List.map_congr_left
  intro a ha
  split_ifs
  · rw [scaledCoefficient_dilation a hz ht]
    simp [scaledCoefficient]
  · rfl

end SquareFreeTerm
end BourgadeHuang.EdgeCMS
