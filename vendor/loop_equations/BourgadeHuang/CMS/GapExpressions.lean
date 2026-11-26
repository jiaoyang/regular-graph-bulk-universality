import BourgadeHuang.CMS.GeneralCouplingJets

/-! Finite rational expressions in inverse coordinate gaps. Symbolic
 differentiation is proved to be the actual complex coordinate derivative;
 homogeneous gap weight gives uniform decay of every resulting derivative. -/
noncomputable section
open scoped BigOperators Topology
open Set Filter
namespace BourgadeHuang.CMS

inductive GapExpression (d : ℕ) where
  | const (a : ℂ)
  | inverse (i j : Fin d) (hne : i≠j)
  | add (e f : GapExpression d)
  | mul (e f : GapExpression d)

namespace GapExpression

def eval {d : ℕ} : GapExpression d → Point d → ℂ
  | const a,_ => a
  | inverse i j _,z => (z i-z j)⁻¹
  | add e f,z => e.eval z+f.eval z
  | mul e f,z => e.eval z*f.eval z

def size {d : ℕ} : GapExpression d → ℝ
  | const a => ‖a‖
  | inverse _ _ _ => 1
  | add e f => e.size+f.size
  | mul e f => e.size*f.size

theorem size_nonneg {d : ℕ} (e : GapExpression d) : 0≤e.size := by
  induction e <;> simp only [size] <;> positivity

/-- Constants have weight zero, inverse gaps weight one, and weights add under
multiplication. The zero expression has every weight. -/
inductive Homogeneous {d : ℕ} : ℕ → GapExpression d → Prop where
  | const (a : ℂ) : Homogeneous 0 (const a)
  | zero (n : ℕ) : Homogeneous n (const 0)
  | inverse (i j : Fin d) (hne : i≠j) : Homogeneous 1 (inverse i j hne)
  | add {n : ℕ} {e f : GapExpression d} : Homogeneous n e → Homogeneous n f → Homogeneous n (add e f)
  | mul {n m : ℕ} {e f : GapExpression d} : Homogeneous n e → Homogeneous m f → Homogeneous (n+m) (mul e f)

def derivative {d : ℕ} (k : Fin d) : GapExpression d → GapExpression d
  | const _ => const 0
  | inverse i j hne => mul (const (-pairSlope k (i,j))) (mul (inverse i j hne) (inverse i j hne))
  | add e f => add (e.derivative k) (f.derivative k)
  | mul e f => add (mul (e.derivative k) f) (mul e (f.derivative k))

theorem homogeneous_derivative {d n : ℕ} {e : GapExpression d}
    (he : e.Homogeneous n) (i : Fin d) : (e.derivative i).Homogeneous (n+1) := by
  induction he with
  | const a => exact Homogeneous.zero _
  | zero n => exact Homogeneous.zero _
  | inverse j k hne =>
    exact (Homogeneous.const _).mul ((Homogeneous.inverse j k hne).mul (Homogeneous.inverse j k hne))
  | add he hf ihe ihf => exact ihe.add ihf
  | @mul n m e f he hf ihe ihf =>
    have h1 := ihe.mul hf
    have h2 := he.mul ihf
    apply Homogeneous.add
    · convert h1 using 1; omega
    · exact h2

theorem analyticAt_eval {d : ℕ} (e : GapExpression d) {z : Point d}
    (hz : CollisionFree z) : AnalyticAt ℂ e.eval z := by
  induction e with
  | const a => exact analyticAt_const
  | inverse i j hne =>
    exact (((ContinuousLinearMap.proj (R := ℂ) i).analyticAt z).sub
      ((ContinuousLinearMap.proj (R := ℂ) j).analyticAt z)).inv (hz.sub_ne_zero hne)
  | add e f he hf => exact he.add hf
  | mul e f he hf => exact he.mul hf

theorem hasDerivAt_eval {d : ℕ} (e : GapExpression d) {z : Point d}
    (hz : CollisionFree z) (i : Fin d) :
    HasDerivAt (fun w => e.eval (Function.update z i w)) ((e.derivative i).eval z) (z i) := by
  induction e with
  | const a => exact hasDerivAt_const _ _
  | inverse j k hne =>
    have h := hasDerivAt_pairInverse z i (j,k) (hz.sub_ne_zero hne)
    convert h using 1
    simp only [derivative,eval]
    ring
  | add e f he hf => exact he.add hf
  | mul e f he hf =>
    simpa only [derivative,eval,Function.update_eq_self] using he.mul hf

theorem coordDeriv_eval {d : ℕ} (e : GapExpression d) {z : Point d}
    (hz : CollisionFree z) (i : Fin d) : coordDeriv i e.eval z=(e.derivative i).eval z :=
  (hasDerivAt_eval e hz i).deriv

/-- The actual rational expression has the decay prescribed by its homogeneous
weight, uniformly at every configuration with the displayed gap lower bound. -/
theorem norm_eval_le {d n : ℕ} {e : GapExpression d} (he : e.Homogeneous n)
    (z : Point d) {R : ℝ} (hR : 0<R) (hsep : ∀i j,i≠j→R≤‖z i-z j‖) :
    ‖e.eval z‖≤e.size/R^n := by
  induction he with
  | const a => simp [eval,size]
  | zero n => simp [eval,size]
  | inverse i j hne =>
    simp only [eval,size,pow_one,norm_inv,one_div]
    exact inv_anti₀ hR (hsep i j hne)
  | add he hf ihe ihf =>
    exact (norm_add_le _ _).trans ((add_le_add ihe ihf).trans_eq (by simp [size,add_div]))
  | @mul n m e f he hf ihe ihf =>
    apply (norm_mul_le _ _).trans
    apply (mul_le_mul ihe ihf (norm_nonneg _) (div_nonneg (size_nonneg _) (by positivity))).trans_eq
    simp only [size,pow_add,mul_div_mul_comm]

def inverseGap {d : ℕ} (i j : Fin d) : GapExpression d :=
  if h : i=j then const 0 else inverse i j h

@[simp] theorem eval_inverseGap {d : ℕ} (i j : Fin d) (z : Point d) :
    (inverseGap i j).eval z=(z i-z j)⁻¹ := by
  by_cases h : i=j
  · subst j
    simp [inverseGap,eval]
  · simp [inverseGap,h,eval]

theorem homogeneous_inverseGap {d : ℕ} (i j : Fin d) :
    (inverseGap i j).Homogeneous 1 := by
  by_cases h : i=j
  · simp only [inverseGap,dif_pos h]
    exact Homogeneous.zero 1
  · simp only [inverseGap,dif_neg h]
    exact Homogeneous.inverse i j h

def finSum {d : ℕ} : (n : ℕ) → (Fin n → GapExpression d) → GapExpression d
  | 0,_ => const 0
  | n+1,f => add (f 0) (finSum n (fun j => f j.succ))

@[simp] theorem eval_finSum {d n : ℕ} (f : Fin n → GapExpression d) (z : Point d) :
    (finSum n f).eval z=∑i,(f i).eval z := by
  induction n with
  | zero => simp [finSum,eval]
  | succ n ih => simp only [finSum,eval,ih,Fin.sum_univ_succ]

theorem homogeneous_finSum {d n k : ℕ} (f : Fin n → GapExpression d)
    (hf : ∀i,(f i).Homogeneous k) : (finSum n f).Homogeneous k := by
  induction n with
  | zero => exact Homogeneous.zero k
  | succ n ih => exact (hf 0).add (ih _ (fun j => hf j.succ))

/-- Repeated actual differentiation preserves the exact inverse-gap order. -/
def iterated {d : ℕ} : (n : ℕ) → (Fin n → Fin d) → GapExpression d → GapExpression d
  | 0,_,e => e
  | n+1,v,e => iterated n (Fin.init v) (e.derivative (v (Fin.last n)))

theorem homogeneous_iterated {d n k : ℕ} {e : GapExpression d}
    (he : e.Homogeneous k) (v : Fin n → Fin d) : (iterated n v e).Homogeneous (k+n) := by
  induction n generalizing k e with
  | zero => exact he
  | succ n ih =>
    have h := ih (homogeneous_derivative he (v (Fin.last n))) (Fin.init v)
    convert h using 1; omega


/-- The symbolic repeated derivative is the actual coordinate Fréchet jet. -/
theorem coordinateJet_eval {d n : ℕ} (e : GapExpression d) (v : Fin n → Fin d)
    {z : Point d} (hz : z∈OrderedDomain d) :
    coordinateJet n e.eval z v=(iterated n v e).eval z := by
  induction n generalizing e with
  | zero => simp [iterated]
  | succ n ih =>
    let j := v (Fin.last n)
    have heq : EqOn (coordDeriv j e.eval) (e.derivative j).eval (OrderedDomain d) :=
      fun w hw => coordDeriv_eval e (orderedDomain_collisionFree hw) j
    have hjets := iteratedFDeriv_eq_of_eqOn_open (n := n) (orderedDomain_isOpen d) hz heq
    have hc := iteratedFDeriv_coordDeriv_apply (n := n) (orderedDomain_isOpen d)
      (fun w hw => analyticAt_eval e (orderedDomain_collisionFree hw)) hz j
      (fun k => Pi.single (Fin.init v k) 1)
    have hv : (Fin.snoc (fun k => (Pi.single (Fin.init v k) (1:ℂ) : Point d))
        (Pi.single j 1) : Fin (n+1) → Point d)=
        (fun k => (Pi.single (v k) (1:ℂ) : Point d)) := by
      funext k
      refine Fin.lastCases ?_ (fun l => ?_) k
      · simp [j]
      · simp only [Fin.snoc_castSucc]
        rfl
    rw [hv] at hc
    change iteratedFDeriv ℂ (n+1) e.eval z (fun k => Pi.single (v k) (1:ℂ))=_
    rw [← hc,hjets]
    exact ih (e.derivative j) (Fin.init v)

/-- Uniform all-order estimates for genuine derivatives of homogeneous gap
expressions, with a concrete finite coefficient constant. -/
theorem norm_coordinateJet_le {d n k : ℕ} {e : GapExpression d}
    (he : e.Homogeneous k) (v : Fin n → Fin d) {z : Point d} (hz : z∈OrderedDomain d)
    {R : ℝ} (hR : 0<R) (hsep : ∀i j,i≠j→R≤‖z i-z j‖) :
    ‖coordinateJet n e.eval z v‖≤(iterated n v e).size/R^(k+n) := by
  rw [coordinateJet_eval e v hz]
  exact norm_eval_le (homogeneous_iterated he v) z hR hsep

end GapExpression
end BourgadeHuang.CMS
