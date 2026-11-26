import BourgadeHuang.CMS.CanonicalSectorialFamily

/-! Convexity and nonemptiness of the actual large ordered chambers. -/
noncomputable section
open Set
namespace BourgadeHuang.CMS

/-- Every finite ordered chamber with a prescribed real gap is inhabited. -/
theorem orderedGapDomain_nonempty (d : ℕ) (R : ℝ) : (OrderedGapDomain d R).Nonempty := by
  refine ⟨fun i=>(((max R 0+1)*(i.val:ℝ):ℝ):ℂ),?_⟩
  intro i j hij
  have hgap : (1:ℝ)≤(j.val:ℝ)-(i.val:ℝ) := by
    have hh : i.val+1≤j.val := hij
    have hc : (i.val:ℝ)+1≤(j.val:ℝ) := by exact_mod_cast hh
    linarith
  have ha : 0<max R 0+1 := by positivity
  have hb : R<max R 0+1 := by linarith [le_max_left R 0]
  simp only [Complex.sub_re,Complex.ofReal_re]
  have hh := mul_le_mul_of_nonneg_left hgap ha.le
  nlinarith

/-- Real convex combinations preserve every strict real-gap inequality. -/
theorem orderedGapDomain_convex (d : ℕ) (R : ℝ) : Convex ℝ (OrderedGapDomain d R) := by
  intro x hx y hy a b ha hb hab i j hij
  have hxi := hx i j hij
  have hyi := hy i j hij
  have he : (((a•x+b•y) j-(a•x+b•y) i):ℂ).re=
      a*(x j-x i).re+b*(y j-y i).re := by
    simp only [Pi.add_apply,Pi.smul_apply,Complex.sub_re,Complex.add_re,
      Complex.smul_re,smul_eq_mul]
    ring
  rw [he]
  rcases eq_or_lt_of_le ha with ha|ha
  · subst a
    have hb1 : b=1 := by linarith
    simpa only [zero_mul,zero_add,hb1,one_mul] using hyi
  · have hp := mul_lt_mul_of_pos_left hxi ha
    have hq := mul_le_mul_of_nonneg_left hyi.le hb
    have hr : a*R+b*R=R := by rw [←add_mul,hab,one_mul]
    linarith

theorem orderedGapDomain_isConnected (d : ℕ) (R : ℝ) : IsConnected (OrderedGapDomain d R) :=
  (orderedGapDomain_convex d R).isConnected (orderedGapDomain_nonempty d R)

end BourgadeHuang.CMS
