import BourgadeHuang.CMS.Basic
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Analytic.IteratedFDeriv
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.LinearAlgebra.Multilinear.Pi
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FinCases

/-!
Square-free jet uniqueness for genuine analytic CMS solutions in arbitrary dimension.

The actual CMS equations reduce repeated coordinate derivatives to lower-order jets.
Strong induction, symmetry of analytic Fréchet derivatives, and a product derivative
norm bound show that vanishing square-free jets forces every derivative to vanish.
Analytic continuation then gives equality on a connected open collision-free domain.
The endpoint uses one canonical jet for each coordinate subset, hence 2^d initial data.
The geometry of ordered and mixed upper/lower half-plane domains is also established.
-/

noncomputable section
open scoped BigOperators ContDiff
open Set Filter Topology

namespace BourgadeHuang.CMS

/-- One ordered collision-free domain, ordered by real parts. -/
def OrderedDomain (d : ℕ) : Set (Point d) :=
  {z | ∀ i j, i < j → (z i).re < (z j).re}

theorem orderedDomain_collisionFree {d : ℕ} {z : Point d}
    (hz : z ∈ OrderedDomain d) : CollisionFree z := by
  intro i j hij
  rcases lt_trichotomy i j with h | h | h
  · have := hz i j h
    rw [hij] at this
    exact (lt_irrefl _ this).elim
  · exact h
  · have := hz j i h
    rw [hij] at this
    exact (lt_irrefl _ this).elim

theorem orderedDomain_nonempty (d : ℕ) : (OrderedDomain d).Nonempty := by
  refine ⟨fun i => (i.val : ℂ), ?_⟩
  intro i j hij
  simp only [Complex.natCast_re]
  exact Nat.cast_lt.mpr hij

theorem orderedDomain_convex (d : ℕ) : Convex ℝ (OrderedDomain d) := by
  intro x hx y hy a b ha hb hab i j hij
  have hxi := hx i j hij
  have hyi := hy i j hij
  simp only [Pi.add_apply, Pi.smul_apply, Complex.add_re, Complex.smul_re, smul_eq_mul]
  rcases eq_or_lt_of_le ha with h | h
  · subst a
    have hb1 : b = 1 := by linarith
    simpa [hb1] using hyi
  · exact add_lt_add_of_lt_of_le (mul_lt_mul_of_pos_left hxi h)
      (mul_le_mul_of_nonneg_left hyi.le hb)

theorem orderedDomain_isOpen (d : ℕ) : IsOpen (OrderedDomain d) := by
  have hrepr : OrderedDomain d = ⋂ i : Fin d, ⋂ j : Fin d,
      {z : Point d | i < j → (z i).re < (z j).re} := by
    ext z
    simp [OrderedDomain]
  rw [hrepr]
  apply isOpen_iInter_of_finite
  intro i
  apply isOpen_iInter_of_finite
  intro j
  by_cases hij : i < j
  · simpa only [hij, true_implies] using
      isOpen_lt (Complex.continuous_re.comp (continuous_apply i))
        (Complex.continuous_re.comp (continuous_apply j))
  · simpa only [hij, false_implies, setOf_true] using
      (isOpen_univ : IsOpen (Set.univ : Set (Point d)))

theorem orderedDomain_isConnected (d : ℕ) : IsConnected (OrderedDomain d) :=
  (orderedDomain_convex d).isConnected (orderedDomain_nonempty d)

/-- The ordered chamber with half-plane restrictions only on the selected coordinates.
In the observable application the selected coordinates are denominator variables. -/
def OrderedMixedDomain (d : ℕ) (J : Finset (Fin d)) (σ : Fin d → Sign) :
    Set (Point d) :=
  OrderedDomain d ∩ {z | ∀ i ∈ J, if σ i then 0 < (z i).im else (z i).im < 0}

theorem orderedMixedDomain_convex (d : ℕ) (J : Finset (Fin d)) (σ : Fin d → Sign) :
    Convex ℝ (OrderedMixedDomain d J σ) := by
  apply (orderedDomain_convex d).inter
  intro x hx y hy a b ha hb hab i hi
  have hxi := hx i hi
  have hyi := hy i hi
  cases hσ : σ i <;> simp only [hσ, Bool.false_eq_true, ↓reduceIte] at hxi hyi ⊢
  all_goals
    simp only [Pi.add_apply, Pi.smul_apply, Complex.add_im, Complex.smul_im, smul_eq_mul]
    rcases eq_or_lt_of_le ha with h | h
    · subst a
      have hb1 : b = 1 := by linarith
      simpa [hb1] using hyi
    · nlinarith [mul_lt_mul_of_pos_left hxi h, mul_le_mul_of_nonneg_left hyi.le hb]

theorem orderedMixedDomain_nonempty (d : ℕ) (J : Finset (Fin d)) (σ : Fin d → Sign) :
    (OrderedMixedDomain d J σ).Nonempty := by
  refine ⟨fun i => (i.val : ℂ) + (if σ i then Complex.I else -Complex.I), ?_, ?_⟩
  · intro i j hij
    have hcast : (i.val : ℝ) < (j.val : ℝ) := by exact Nat.cast_lt.mpr hij
    simpa only [Complex.add_re, Complex.natCast_re, apply_ite Complex.re,
      Complex.I_re, Complex.neg_re, neg_zero, ite_self, add_zero] using hcast
  · intro i hi
    cases hσ : σ i <;> simp [hσ]

theorem orderedMixedDomain_isOpen (d : ℕ) (J : Finset (Fin d)) (σ : Fin d → Sign) :
    IsOpen (OrderedMixedDomain d J σ) := by
  apply (orderedDomain_isOpen d).inter
  have hrepr : {z : Point d | ∀ i ∈ J,
      if σ i then 0 < (z i).im else (z i).im < 0} =
      ⋂ i : Fin d, {z : Point d | i ∈ J →
        if σ i then 0 < (z i).im else (z i).im < 0} := by
    ext z
    simp
  rw [hrepr]
  apply isOpen_iInter_of_finite
  intro i
  by_cases hi : i ∈ J
  · cases hσ : σ i
    · simpa [hi, hσ] using isOpen_lt
        (Complex.continuous_im.comp (continuous_apply i)) continuous_const
    · simpa [hi, hσ] using isOpen_lt continuous_const
        (Complex.continuous_im.comp (continuous_apply i))
  · simpa only [hi, false_implies, setOf_true] using
      (isOpen_univ : IsOpen (Set.univ : Set (Point d)))

theorem orderedMixedDomain_isConnected (d : ℕ) (J : Finset (Fin d))
    (σ : Fin d → Sign) : IsConnected (OrderedMixedDomain d J σ) :=
  (orderedMixedDomain_convex d J σ).isConnected (orderedMixedDomain_nonempty d J σ)

theorem orderedMixedDomain_collisionFree {d : ℕ} {J : Finset (Fin d)}
    {σ : Fin d → Sign} {z : Point d} (hz : z ∈ OrderedMixedDomain d J σ) :
    CollisionFree z := orderedDomain_collisionFree hz.1

/-- The first repeated-derivative reduction, using the genuine CMS operator.
The general-order reduction is proved below. -/
theorem secondPartial_eq_zero_of_first_jet {d : ℕ} {f : Point d → ℂ}
    {z : Point d} (_hz : CollisionFree z) (hsolve : ∀ i, reducedOperator i f z = 0)
    (hzero : f z = 0) (hfirst : ∀ i, coordDeriv i f z = 0) :
    ∀ i, secondPartial i f z = 0 := by
  intro i
  simpa [reducedOperator, hzero, hfirst] using hsolve i

/-- Genuine order-`n` coordinate jet, evaluated on the listed coordinate directions.
The indices may repeat. -/
def coordinateJet {d : ℕ} (n : ℕ) (f : Point d → ℂ) (z : Point d)
    (v : Fin n → Fin d) : ℂ :=
  iteratedFDeriv ℂ n f z (fun k => Pi.single (v k) 1)

/-- Mixed coordinate jets commute for actual analytic functions. -/
theorem coordinateJet_comp_perm {d n : ℕ} {f : Point d → ℂ} {z : Point d}
    (hf : AnalyticAt ℂ f z) (v : Fin n → Fin d) (π : Equiv.Perm (Fin n)) :
    coordinateJet n f z (v ∘ π) = coordinateJet n f z v := by
  have hcont : ContDiffAt ℂ ω f z := hf.contDiffAt
  simpa only [coordinateJet, Function.comp_def] using
    hcont.iteratedFDeriv_comp_perm (fun k => (Pi.single (v k) (1 : ℂ) : Point d)) π

/-- Coordinate-slice derivatives agree with genuine Fréchet directional derivatives. -/
theorem coordDeriv_eq_fderiv {d : ℕ} {f : Point d → ℂ} {z : Point d}
    (hf : DifferentiableAt ℂ f z) (i : Fin d) :
    coordDeriv i f z = fderiv ℂ f z (Pi.single i 1) := by
  have hs := hf.hasFDerivAt.comp_hasDerivAt_of_eq (z i) (hasDerivAt_update z i (z i))
    (Function.update_eq_self i z).symm
  exact hs.deriv

/-- Genuine coordinate derivatives of analytic functions are analytic. -/
theorem analyticAt_coordDeriv {d : ℕ} {f : Point d → ℂ} {z : Point d}
    (hf : AnalyticAt ℂ f z) (i : Fin d) : AnalyticAt ℂ (coordDeriv i f) z := by
  have heval : AnalyticAt ℂ (fun w => fderiv ℂ f w (Pi.single i 1)) z :=
    ((ContinuousLinearMap.apply ℂ ℂ (Pi.single i (1 : ℂ) : Point d)).analyticAt _).comp hf.fderiv
  apply heval.congr
  filter_upwards [hf.eventually_analyticAt] with w hw
  exact (coordDeriv_eq_fderiv hw.differentiableAt i).symm

theorem analyticOnNhd_coordDeriv {d : ℕ} {f : Point d → ℂ} {U : Set (Point d)}
    (hf : AnalyticOnNhd ℂ f U) (i : Fin d) : AnalyticOnNhd ℂ (coordDeriv i f) U :=
  fun z hz => analyticAt_coordDeriv (hf z hz) i

/-- Coordinate derivatives depend only on the function germ at the point. -/
theorem coordDeriv_congr_nhds {d : ℕ} {f g : Point d → ℂ} {z : Point d}
    (hfg : f =ᶠ[𝓝 z] g) (i : Fin d) : coordDeriv i f z = coordDeriv i g z := by
  have ht : Tendsto (Function.update z i) (𝓝 (z i)) (𝓝 z) := by
    simpa only [Function.update_eq_self] using
      (hasDerivAt_update z i (z i)).continuousAt.tendsto
  exact (hfg.comp_tendsto ht).deriv_eq

/-- Iterated coordinate derivatives agree with the genuine Hessian for analytic functions. -/
theorem coordDeriv_coordDeriv_eq_fderiv {d : ℕ} {f : Point d → ℂ} {z : Point d}
    (hf : AnalyticAt ℂ f z) (i j : Fin d) :
    coordDeriv i (coordDeriv j f) z =
      fderiv ℂ (fderiv ℂ f) z (Pi.single i 1) (Pi.single j 1) := by
  have hloc : coordDeriv j f =ᶠ[𝓝 z]
      (fun w => fderiv ℂ f w (Pi.single j 1)) := by
    filter_upwards [hf.eventually_analyticAt] with w hw
    exact coordDeriv_eq_fderiv hw.differentiableAt j
  rw [coordDeriv_congr_nhds hloc i]
  have hs := hf.fderiv.differentiableAt.hasFDerivAt.comp_hasDerivAt_of_eq (z i)
    (hasDerivAt_update z i (z i)) (Function.update_eq_self i z).symm
  have ha := hs.clm_apply (hasDerivAt_const (z i) (Pi.single j (1 : ℂ)))
  simpa only [Function.comp_apply, Function.update_eq_self, map_zero, add_zero]
    using ha.deriv

@[simp] theorem coordinateJet_zero {d : ℕ} (f : Point d → ℂ) (z : Point d)
    (v : Fin 0 → Fin d) : coordinateJet 0 f z v = f z := by
  simp [coordinateJet]

/-- The first-order Fréchet-jet definition uses the same derivative as the CMS operator. -/
theorem coordinateJet_one {d : ℕ} {f : Point d → ℂ} {z : Point d}
    (hf : DifferentiableAt ℂ f z) (v : Fin 1 → Fin d) :
    coordinateJet 1 f z v = coordDeriv (v 0) f z := by
  simp only [coordinateJet, iteratedFDeriv_one_apply, coordDeriv_eq_fderiv hf]

/-- Repeated second coordinate jets are exactly the second partials in the PDE. -/
theorem coordinateJet_two_repeat {d : ℕ} {f : Point d → ℂ} {z : Point d}
    (hf : AnalyticAt ℂ f z) (i : Fin d) :
    coordinateJet 2 f z (fun _ => i) = secondPartial i f z := by
  rw [coordinateJet, iteratedFDeriv_two_apply, secondPartial,
    coordDeriv_coordDeriv_eq_fderiv hf]

/-- Differentiating a coordinate derivative contracts the full next derivative
with that coordinate direction. -/
theorem iteratedFDeriv_coordDeriv_apply {d n : ℕ} {f : Point d → ℂ}
    {U : Set (Point d)} (hU : IsOpen U) (hf : AnalyticOnNhd ℂ f U)
    {z : Point d} (hz : z ∈ U) (i : Fin d) (v : Fin n → Point d) :
    iteratedFDeriv ℂ n (coordDeriv i f) z v =
      iteratedFDeriv ℂ (n + 1) f z (Fin.snoc v (Pi.single i 1)) := by
  have hcd : ContDiffOn ℂ n (fderiv ℂ f) U :=
    fun w hw => (hf w hw).fderiv.contDiffAt.contDiffWithinAt
  have heq : EqOn (coordDeriv i f) (fun w => fderiv ℂ f w (Pi.single i 1)) U :=
    fun w hw => coordDeriv_eq_fderiv (hf w hw).differentiableAt i
  rw [← iteratedFDerivWithin_of_isOpen n hU hz,
    iteratedFDerivWithin_congr heq hz n,
    iteratedFDerivWithin_clm_apply_const_apply hU.uniqueDiffOn hcd le_rfl hz,
    iteratedFDerivWithin_of_isOpen n hU hz,
    iteratedFDeriv_succ_apply_right, Fin.init_snoc, Fin.snoc_last]

/-- Exact repeated-direction contraction for the second derivative appearing in CMS. -/
theorem iteratedFDeriv_secondPartial_apply {d n : ℕ} {f : Point d → ℂ}
    {U : Set (Point d)} (hU : IsOpen U) (hf : AnalyticOnNhd ℂ f U)
    {z : Point d} (hz : z ∈ U) (i : Fin d) (v : Fin n → Point d) :
    iteratedFDeriv ℂ n (secondPartial i f) z v =
      iteratedFDeriv ℂ (n + 2) f z
        (Fin.snoc (Fin.snoc v (Pi.single i 1)) (Pi.single i 1)) := by
  rw [secondPartial, iteratedFDeriv_coordDeriv_apply hU (analyticOnNhd_coordDeriv hf i) hz i,
    iteratedFDeriv_coordDeriv_apply hU hf hz i]

/-- Vanishing of one higher full derivative implies vanishing of the corresponding
full derivative of each actual coordinate derivative. -/
theorem iteratedFDeriv_coordDeriv_eq_zero {d n : ℕ} {f : Point d → ℂ}
    {U : Set (Point d)} (hU : IsOpen U) (hf : AnalyticOnNhd ℂ f U)
    {z : Point d} (hz : z ∈ U) (i : Fin d)
    (hzero : iteratedFDeriv ℂ (n + 1) f z = 0) :
    iteratedFDeriv ℂ n (coordDeriv i f) z = 0 := by
  ext v
  rw [iteratedFDeriv_coordDeriv_apply hU hf hz i, hzero]
  rfl


/-- A proved product-vanishing rule for the higher-order CMS induction.
It uses mathlib's derivative norm bound, so no explicit multiindex Leibniz formula is needed. -/
theorem iteratedFDeriv_mul_eq_zero_of_lower_jets {d n : ℕ}
    {U : Set (Point d)} (hU : IsOpen U) {z : Point d} (hz : z ∈ U)
    {a g : Point d → ℂ} (ha : ContDiffOn ℂ n a U) (hg : ContDiffOn ℂ n g U)
    (hgzero : ∀ m ≤ n, iteratedFDeriv ℂ m g z = 0) :
    iteratedFDeriv ℂ n (fun w => a w * g w) z = 0 := by
  have hbound := norm_iteratedFDerivWithin_mul_le ha hg hU.uniqueDiffOn hz
    (n := n) le_rfl
  have hwithin : ∀ m (k : Point d → ℂ),
      iteratedFDerivWithin ℂ m k U z = iteratedFDeriv ℂ m k z :=
    fun m k => iteratedFDerivWithin_of_isOpen m hU hz
  simp_rw [hwithin] at hbound
  have hzero : ∀ i, iteratedFDeriv ℂ (n - i) g z = 0 :=
    fun i => hgzero _ (Nat.sub_le _ _)
  simp only [hzero, norm_zero, mul_zero, Finset.sum_const_zero] at hbound
  exact norm_eq_zero.mp (le_antisymm hbound (norm_nonneg _))

/-- Square-free initial data: directions in a jet do not repeat. -/
def SquareFreeJetsVanish {d : ℕ} (f : Point d → ℂ) (z : Point d) : Prop :=
  ∀ n (v : Fin n → Fin d), Function.Injective v → coordinateJet n f z v = 0

/-- The order-two case of the repeated-derivative reduction in arbitrary dimension. -/
theorem second_jets_zero_of_squareFree {d : ℕ} {f : Point d → ℂ} {z : Point d}
    (hf : AnalyticAt ℂ f z) (hz : CollisionFree z)
    (hsolve : ∀ i, reducedOperator i f z = 0) (hsq : SquareFreeJetsVanish f z) : ∀ v, coordinateJet 2 f z v = 0 := by
  have hzero : f z = 0 := by
    simpa using hsq 0 (fun k => Fin.elim0 k)
      (Function.injective_of_subsingleton _)
  have hfirst : ∀ i, coordDeriv i f z = 0 := by
    intro i
    simpa only [coordinateJet_one hf.differentiableAt] using
      hsq 1 (fun _ => i) (Function.injective_of_subsingleton _)
  have hsecond := secondPartial_eq_zero_of_first_jet hz hsolve hzero hfirst
  intro v
  by_cases hv : Function.Injective v
  · exact hsq 2 v hv
  · have heq : v 0 = v 1 := by
      by_contra hne
      apply hv
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all
    have hconst : v = fun _ => v 0 := by
      funext k
      fin_cases k
      · rfl
      · exact heq.symm
    rw [hconst, coordinateJet_two_repeat hf, hsecond]

/-- All coordinate jets determine a continuous multilinear map. -/
theorem multilinear_eq_zero_of_coordinate_values {d n : ℕ}
    (A : ContinuousMultilinearMap ℂ (fun _ : Fin n => Point d) ℂ)
    (hA : ∀ v : Fin n → Fin d, A (fun k => Pi.single (v k) 1) = 0) : A = 0 := by
  have hml : A.toMultilinearMap = 0 := by
    apply MultilinearMap.pi_ext
    intro v
    apply MultilinearMap.ext
    intro c
    change A (fun k => Pi.single (v k) (c k)) = 0
    have hsingle : (fun k => (Pi.single (v k) (c k) : Point d)) =
        (fun k => c k • (Pi.single (v k) (1 : ℂ) : Point d)) := by
      funext k
      simpa only [smul_eq_mul, mul_one] using
        (Pi.single_smul' (v k) (c k) (1 : ℂ))
    rw [hsingle, A.map_smul_univ, hA, smul_zero]
  ext x
  exact congrArg (fun B : MultilinearMap ℂ (fun _ : Fin n => Point d) ℂ => B x) hml

/-- Full coordinate-jet vanishing gives vanishing of the actual Fréchet derivatives. -/
theorem iteratedFDeriv_eq_zero_of_coordinateJet {d : ℕ} {f : Point d → ℂ}
    {z : Point d} (hjets : ∀ n v, coordinateJet n f z v = 0) :
    ∀ n, iteratedFDeriv ℂ n f z = 0 := by
  intro n
  exact multilinear_eq_zero_of_coordinate_values _ (hjets n)

/-- The analytic step of the proposed jet argument, in every dimension.
The hypothesis is vanishing of ALL coordinate jets, not only square-free jets. -/
theorem analytic_eventually_zero_of_coordinateJet {d : ℕ} {f : Point d → ℂ}
    {z : Point d} (hf : AnalyticAt ℂ f z)
    (hjets : ∀ n v, coordinateJet n f z v = 0) : f =ᶠ[𝓝 z] 0 := by
  obtain ⟨p, r, hp⟩ := hf
  have hderiv := iteratedFDeriv_eq_zero_of_coordinateJet hjets
  filter_upwards [EMetric.ball_mem_nhds z hp.r_pos] with w hw
  have hmem : w - z ∈ EMetric.ball 0 r := by
    simpa only [EMetric.mem_ball, edist_eq_enorm_sub, sub_zero] using hw
  have hs := hp.hasSum_iteratedFDeriv hmem
  have hsum : HasSum (fun _ : ℕ => (0 : ℂ)) (f w) := by
    simpa [hderiv, add_sub_cancel] using hs
  exact hsum.unique hasSum_zero

/-- Analytic continuation transports the full-jet uniqueness to any preconnected domain. -/
theorem analytic_eqOn_zero_of_coordinateJet {d : ℕ} {f : Point d → ℂ}
    {U : Set (Point d)} (hf : AnalyticOnNhd ℂ f U) (hU : IsPreconnected U)
    {z : Point d} (hz : z ∈ U)
    (hjets : ∀ n v, coordinateJet n f z v = 0) : EqOn f 0 U :=
  hf.eqOn_zero_of_preconnected_of_eventuallyEq_zero hU hz
    (analytic_eventually_zero_of_coordinateJet (hf z hz) hjets)

/-- Specialization to the connected ordered collision-free domain required by CMS. -/
theorem analytic_eqOn_zero_on_orderedDomain {d : ℕ} {f : Point d → ℂ}
    (hf : AnalyticOnNhd ℂ f (OrderedDomain d)) {z : Point d}
    (hz : z ∈ OrderedDomain d) (hjets : ∀ n v, coordinateJet n f z v = 0) :
    EqOn f 0 (OrderedDomain d) :=
  analytic_eqOn_zero_of_coordinateJet hf (orderedDomain_isConnected d).isPreconnected hz hjets

/-- The same analytic continuation step on the domains with denominator half-plane signs. -/
theorem analytic_eqOn_zero_on_orderedMixedDomain {d : ℕ} {J : Finset (Fin d)}
    {σ : Fin d → Sign} {f : Point d → ℂ}
    (hf : AnalyticOnNhd ℂ f (OrderedMixedDomain d J σ)) {z : Point d}
    (hz : z ∈ OrderedMixedDomain d J σ) (hjets : ∀ n v, coordinateJet n f z v = 0) :
    EqOn f 0 (OrderedMixedDomain d J σ) :=
  analytic_eqOn_zero_of_coordinateJet hf
    (orderedMixedDomain_isConnected d J σ).isPreconnected hz hjets


/-- Full derivative locality on an open domain. -/
theorem iteratedFDeriv_eq_of_eqOn_open {d n : ℕ} {U : Set (Point d)}
    (hU : IsOpen U) {z : Point d} (hz : z ∈ U) {f g : Point d → ℂ}
    (hfg : EqOn f g U) : iteratedFDeriv ℂ n f z = iteratedFDeriv ℂ n g z := by
  rw [← iteratedFDerivWithin_of_isOpen n hU hz,
    ← iteratedFDerivWithin_of_isOpen n hU hz]
  exact iteratedFDerivWithin_congr hfg hz n

/-- The genuine rational coefficients are analytic wherever collisions are excluded. -/
theorem analyticOnNhd_inverse_difference {d : ℕ} {U : Set (Point d)}
    (hU : ∀ z ∈ U, CollisionFree z) {i j : Fin d} (hij : i ≠ j) :
    AnalyticOnNhd ℂ (fun z : Point d => (z i - z j)⁻¹) U := by
  intro z hz
  exact (((ContinuousLinearMap.proj i : Point d →L[ℂ] ℂ).analyticAt z).sub
    ((ContinuousLinearMap.proj j : Point d →L[ℂ] ℂ).analyticAt z)).inv
      ((hU z hz).sub_ne_zero hij)

/-- General-order differential reduction of the ACTUAL CMS equations.
No abstract recurrence or jet uniqueness is assumed. -/
theorem iteratedFDeriv_secondPartial_eq_zero_of_lower_jets {d n : ℕ}
    {U : Set (Point d)} (hU : IsOpen U) (hcf : ∀ z ∈ U, CollisionFree z)
    {f : Point d → ℂ} (hf : AnalyticOnNhd ℂ f U)
    (hsolve : ∀ z ∈ U, ∀ i, reducedOperator i f z = 0)
    {z : Point d} (hz : z ∈ U)
    (hzero : ∀ m < n + 2, iteratedFDeriv ℂ m f z = 0) (i : Fin d) :
    iteratedFDeriv ℂ n (secondPartial i f) z = 0 := by
  let T (j : Fin d) (w : Point d) :=
    (w i - w j)⁻¹ * (coordDeriv i f w - coordDeriv j f w)
  let J := Finset.univ.erase i
  have ha (j : Fin d) (hj : j ∈ J) :
      AnalyticOnNhd ℂ (fun w : Point d => (w i - w j)⁻¹) U :=
    analyticOnNhd_inverse_difference hcf (Finset.ne_of_mem_erase hj).symm
  have hg (j : Fin d) : AnalyticOnNhd ℂ
      (fun w => coordDeriv i f w - coordDeriv j f w) U :=
    (analyticOnNhd_coordDeriv hf i).sub (analyticOnNhd_coordDeriv hf j)
  have hT (j : Fin d) (hj : j ∈ J) : AnalyticOnNhd ℂ (T j) U :=
    (ha j hj).mul (hg j)
  have hTzero (j : Fin d) (hj : j ∈ J) : iteratedFDeriv ℂ n (T j) z = 0 := by
    apply iteratedFDeriv_mul_eq_zero_of_lower_jets hU hz
      (fun w hw => (ha j hj w hw).contDiffAt.contDiffWithinAt)
      (fun w hw => (hg j w hw).contDiffAt.contDiffWithinAt)
    intro m hm
    have hdi : iteratedFDeriv ℂ m (coordDeriv i f) z = 0 :=
      iteratedFDeriv_coordDeriv_eq_zero hU hf hz i (hzero (m + 1) (by omega))
    have hdj : iteratedFDeriv ℂ m (coordDeriv j f) z = 0 :=
      iteratedFDeriv_coordDeriv_eq_zero hU hf hz j (hzero (m + 1) (by omega))
    simp only [sub_eq_add_neg]
    change iteratedFDeriv ℂ m (coordDeriv i f + -(coordDeriv j f)) z = 0
    rw [iteratedFDeriv_add_apply (g := -(coordDeriv j f))
      (analyticAt_coordDeriv (hf z hz) i).contDiffAt
      (analyticAt_coordDeriv (hf z hz) j).contDiffAt.neg,
      iteratedFDeriv_neg_apply, hdi, hdj]
    simp
  have hsum : AnalyticOnNhd ℂ (fun w => ∑ j ∈ J, T j w) U :=
    J.analyticOnNhd_sum hT
  have hsumzero : iteratedFDeriv ℂ n (fun w => ∑ j ∈ J, T j w) z = 0 := by
    rw [← iteratedFDerivWithin_of_isOpen n hU hz,
      iteratedFDerivWithin_sum_apply hU.uniqueDiffOn hz
        (fun j hj => (hT j hj z hz).contDiffAt.contDiffWithinAt)]
    apply Finset.sum_eq_zero
    intro j hj
    rw [iteratedFDerivWithin_of_isOpen n hU hz, hTzero j hj]
  have hpde : EqOn (secondPartial i f) (fun w => -(f w + ∑ j ∈ J, T j w)) U := by
    intro w hw
    apply eq_neg_of_add_eq_zero_left
    have heq := hsolve w hw i
    simpa only [reducedOperator, J, T, div_eq_mul_inv, mul_comm, add_assoc] using heq
  rw [iteratedFDeriv_eq_of_eqOn_open hU hz hpde]
  change iteratedFDeriv ℂ n (-(fun w => f w + ∑ j ∈ J, T j w)) z = 0
  rw [iteratedFDeriv_neg_apply,
    iteratedFDeriv_add_apply' (hf z hz).contDiffAt (hsum z hz).contDiffAt,
    hzero n (by omega), hsumzero]
  simp

/-- A permutation can send any ordered pair of distinct indices to any other. -/
theorem exists_perm_map_pair {α : Type*} [DecidableEq α] {a b i j : α}
    (hab : a ≠ b) (hij : i ≠ j) :
    ∃ π : Equiv.Perm α, π a = i ∧ π b = j := by
  let s := Equiv.swap a i
  have hsja : s j ≠ a := by
    intro h
    have hh := congrArg s h
    have hji : j = i := by simpa [s] using hh
    exact hij hji.symm
  refine ⟨s * Equiv.swap b (s j), ?_, ?_⟩
  · change s (Equiv.swap b (s j) a) = i
    rw [Equiv.swap_apply_of_ne_of_ne hab hsja.symm]
    exact Equiv.swap_apply_left a i
  · change s (Equiv.swap b (s j) b) = j
    rw [Equiv.swap_apply_left]
    exact Equiv.swap_apply_self a i j

/-- Square-free jet vanishing forces all actual coordinate jets to vanish.
This is the strong induction for genuine analytic CMS solutions. -/
theorem all_jets_zero_of_squareFree {d : ℕ}
    {U : Set (Point d)} (hU : IsOpen U) (hcf : ∀ z ∈ U, CollisionFree z)
    {f : Point d → ℂ} (hf : AnalyticOnNhd ℂ f U)
    (hsolve : ∀ z ∈ U, ∀ i, reducedOperator i f z = 0)
    {z : Point d} (hz : z ∈ U) (hsq : SquareFreeJetsVanish f z) :
    ∀ n v, coordinateJet n f z v = 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro v
    by_cases hv : Function.Injective v
    · exact hsq n v hv
    · cases n with
      | zero => exact (hv (Function.injective_of_subsingleton v)).elim
      | succ n =>
        cases n with
        | zero =>
          have hvinj : Function.Injective v := by
            intro a b _
            apply Fin.ext
            omega
          exact (hv hvinj).elim
        | succ k =>
          obtain ⟨i, j, hvij, hij⟩ := Function.not_injective_iff.mp hv
          have hpair : (Fin.last k).castSucc ≠ Fin.last (k + 1) := by
            intro h
            have hh := congrArg Fin.val h
            simp at hh
          obtain ⟨π, hπa, hπb⟩ := exists_perm_map_pair hpair hij
          have hzero : ∀ m < k + 2, iteratedFDeriv ℂ m f z = 0 := by
            intro m hm
            exact multilinear_eq_zero_of_coordinate_values _ (ih m hm)
          have hsecond := iteratedFDeriv_secondPartial_eq_zero_of_lower_jets
            hU hcf hf hsolve hz hzero (v i)
          let w : Fin (k + 2) → Point d := fun q => Pi.single (v (π q)) 1
          have hwlast : w (Fin.last (k + 1)) = Pi.single (v i) 1 := by
            dsimp [w]
            rw [hπb, ← hvij]
          have hwsecond : Fin.init w (Fin.last k) = Pi.single (v i) 1 := by
            change Pi.single (v (π (Fin.last k).castSucc)) 1 = _
            rw [hπa]
          have hwinit : Fin.init w = Fin.snoc (Fin.init (Fin.init w)) (Pi.single (v i) 1) := by
            simpa only [hwsecond] using (Fin.snoc_init_self (Fin.init w)).symm
          have hw : w = Fin.snoc (Fin.snoc (Fin.init (Fin.init w))
              (Pi.single (v i) 1)) (Pi.single (v i) 1) := by
            calc
              w = Fin.snoc (Fin.init w) (w (Fin.last (k + 1))) :=
                (Fin.snoc_init_self w).symm
              _ = _ := by
                conv_lhs => rw [hwinit, hwlast]
          rw [← coordinateJet_comp_perm (hf z hz) v π]
          change iteratedFDeriv ℂ (k + 2) f z w = 0
          rw [hw, ← iteratedFDeriv_secondPartial_apply hU hf hz (v i)]
          simp only [hsecond, ContinuousMultilinearMap.zero_apply]

/-- The analytic square-free-jet uniqueness theorem on an arbitrary connected
open collision-free domain.  Its conclusion is equality ON the domain. -/
theorem analytic_eqOn_zero_of_squareFree {d : ℕ}
    {U : Set (Point d)} (hU : IsOpen U) (hconn : IsPreconnected U)
    (hcf : ∀ z ∈ U, CollisionFree z)
    {f : Point d → ℂ} (hf : AnalyticOnNhd ℂ f U)
    (hsolve : ∀ z ∈ U, ∀ i, reducedOperator i f z = 0)
    {z : Point d} (hz : z ∈ U) (hsq : SquareFreeJetsVanish f z) : EqOn f 0 U :=
  analytic_eqOn_zero_of_coordinateJet hf hconn hz
    (all_jets_zero_of_squareFree hU hcf hf hsolve hz hsq)

/-- One canonical square-free jet for each coordinate subset: increasing order. -/
def subsetJet {d : ℕ} (f : Point d → ℂ) (z : Point d) (s : Finset (Fin d)) : ℂ :=
  coordinateJet s.card f z (s.orderEmbOfFin rfl)

/-- Vanishing canonical subset jets is unchanged by an arity equality. -/
theorem subsetJet_zero_at_card {d : ℕ} {f : Point d → ℂ} {z : Point d}
    (hzero : ∀ s, subsetJet f z s = 0) (s : Finset (Fin d))
    (n : ℕ) (hcard : s.card = n) :
    coordinateJet n f z (s.orderEmbOfFin hcard) = 0 := by
  subst n
  exact hzero s

/-- Analytic symmetry reduces every square-free coordinate word to the single
canonical derivative for its coordinate subset. -/
theorem squareFreeJetsVanish_of_subsetJet {d : ℕ} {f : Point d → ℂ} {z : Point d}
    (hf : AnalyticAt ℂ f z) (hzero : ∀ s, subsetJet f z s = 0) :
    SquareFreeJetsVanish f z := by
  intro n v hv
  let s := Finset.univ.image v
  have hcard : s.card = n := by
    dsimp [s]
    rw [Finset.card_image_of_injective _ hv]
    simp
  let v' : Fin n → s := fun i => ⟨v i, Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩⟩
  have hv' : Function.Bijective v' := by
    constructor
    · intro i j hij
      exact hv (congrArg Subtype.val hij)
    · intro a
      obtain ⟨i, _, hi⟩ := Finset.mem_image.mp a.property
      refine ⟨i, ?_⟩
      exact Subtype.ext hi
  let e : Fin n ≃ s := Equiv.ofBijective v' hv'
  let e' : Fin n ≃ s := (s.orderIsoOfFin hcard).toEquiv
  let π : Equiv.Perm (Fin n) := e'.trans e.symm
  have hperm : v ∘ π = s.orderEmbOfFin hcard := by
    funext i
    change (e (e.symm (e' i))).val = (e' i).val
    rw [e.apply_symm_apply]
  rw [← coordinateJet_comp_perm hf v π, hperm]
  exact subsetJet_zero_at_card hzero s n hcard

/-- A genuine analytic CMS solution is determined on U by its 2^d canonical
subset jets at one point (zero form). No claim about values outside U is made. -/
theorem analytic_eqOn_zero_of_subsetJet {d : ℕ}
    {U : Set (Point d)} (hU : IsOpen U) (hconn : IsPreconnected U)
    (hcf : ∀ z ∈ U, CollisionFree z)
    {f : Point d → ℂ} (hf : AnalyticOnNhd ℂ f U)
    (hsolve : ∀ z ∈ U, ∀ i, reducedOperator i f z = 0)
    {z : Point d} (hz : z ∈ U) (hjets : ∀ s, subsetJet f z s = 0) : EqOn f 0 U :=
  analytic_eqOn_zero_of_squareFree hU hconn hcf hf hsolve hz
    (squareFreeJetsVanish_of_subsetJet (hf z hz) hjets)


end BourgadeHuang.CMS
