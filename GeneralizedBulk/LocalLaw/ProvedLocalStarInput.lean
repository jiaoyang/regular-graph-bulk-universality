import GeneralizedBulk.LocalLaw.ProvedMesoscopicInput
import GeneralizedBulk.LocalLaw.StarForestReference
import GeneralizedBulk.LocalLaw.StarPolynomialError
import LocalLaw.RadiusHierarchy

/-! The exact local-star HY record is constructed from the proved source
local law and actual structural graph event. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology BigOperators Classical

namespace GeneralizedBulk.External.RegularSpectralData
open Graph GeneralizedBulk.LocalLawBridge LocalLaw SpectralConsequences GeneralizedBulk.KestenMcKay

variable {d : ℕ} {N : ℕ → ℕ} {Ω : Type*} [MeasurableSpace Ω]
variable (D : RegularSpectralData d N Ω)

/-- Actual source comparison on the full uniform graph ensemble. The
energy set is arbitrary, and every power height in (0,1/2) is covered.
No local comparison, geometry or error estimate is assumed. -/
def provedHYLocalStarInput (P : Measure Ω) [IsProbabilityMeasure P]
    (hUniform : ∀ n,Measure.map (D.spectralRegularGraph n) P=regularGraphLaw (N n) d)
    (hd : 3≤d) (K : Set ℝ) (c : ℝ) (hc : 0<c) (hc1 : c<1/2) :
    HYLocalStarInput D P K c (treeGreenStar d (by exact_mod_cast hd)) := by
  classical
  let base := D.provedHYMesoscopicInput P hUniform hd Set.univ (1/4) (by norm_num)
  have herror := D.size_tendsto.eventually (eventually_source_star_error d hd c hc hc1)
  have hradii := D.size_tendsto.eventually
    (eventually_source_radius_hierarchy 12 d (1/4) (1/128) hd
      (by norm_num) (by norm_num) (by norm_num))
  let hex := eventually_atTop.mp (herror.and hradii)
  let T := Classical.choose hex
  have hT := Classical.choose_spec hex
  let events : PolynomialGoodEvents P N := {
    base.events with
    threshold := max base.events.threshold T
    failure_bound := by
      intro n hn
      exact base.events.failure_bound n ((le_max_left _ _).trans hn) }
  let bad : ∀ n,Ω → Finset (Fin (N n)) := fun n ω =>
    nonTreeCenters (D.localLawGraph n ω).graph
      (logarithmicRadius ((1/4 : ℝ)/4) d (N n))
  have hgood (n : ℕ) (ω : Ω) (hg : ω∈events.good n) :
      LocalLaw.RegularGraph.structural
        (logarithmicRadius ((1/4 : ℝ)/4) d (N n)) (finiteOmega d)
          ⌊(N n : ℝ)^(1/4 : ℝ)⌋₊ (D.localLawGraph n ω) ∧
      SourceLocalLawGood (D.localLawGraph n ω) (by omega) (1/128) := hg
  refine {
    height_range := ⟨hc,hc1⟩
    events := events
    local_exponent := 1/1024
    local_exponent_pos := by norm_num
    badRoots := bad
    bad_count := ?_
    approximation := ?_ }
  · intro n hn ω hg
    have hb := (hgood n ω hg).1.2
    have hn1 : (1 : ℝ) ≤ N n := by exact_mod_cast (D.size_pos n)
    have hb' : ((bad n ω).card : ℝ) ≤ (N n : ℝ)^(1/4 : ℝ) := by
      exact (Nat.cast_le.mpr hb).trans (Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg _) _))
    exact hb'.trans (Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num : (1/4 : ℝ)≤1/2))
  · intro n hn ω hg root hroot energy henergy i j
    have hnT : T≤n := (le_max_right _ _).trans hn
    have hnum := (hT n hnT).1
    have hradii := (hT n hnT).2
    let g := D.localLawGraph n ω
    let r := logarithmicRadius (1/128) d (N n)
    let R := logarithmicRadius ((1/4 : ℝ)/4) d (N n)
    have hr : 1≤r := by
      have hh := hradii.2.1
      dsimp only [r]
      omega
    have hmargin : r+1≤R := by
      have hh := hradii.1
      dsimp only [r,R]
      omega
    have htree : (graphBall g.graph root R).IsTree := by
      by_contra hnot
      apply hroot
      exact (nonTreeCenters_membership g.graph R root).mpr hnot
    let s : ℝ := Real.sqrt ((d : ℝ)-1)
    have hdr : (3 : ℝ)≤d := by exact_mod_cast hd
    have hs : 0<s := Real.sqrt_pos.mpr (by linarith)
    let z : ℂ := (energy : ℂ)+(↑((N n : ℝ)^(-c)) : ℂ)*Complex.I
    let w : ℂ := z/(s : ℂ)
    have hz : 0<z.im := by
      change 0<((energy : ℂ)+(↑((N n : ℝ)^(-c)) : ℂ)*Complex.I).im
      simpa using Real.rpow_pos_of_pos (Nat.cast_pos.mpr (D.size_pos n)) (-c)
    have hwim : w.im=(N n : ℝ)^(-c)/Real.sqrt ((d : ℝ)-1) := by
      simp [w,z,s,Complex.div_ofReal_im]
    have he := hnum w hwim
    have hlaw := (hgood n ω hg).2 w he.1 he.2.1
    have hadj (a : Fin d) : g.graph.Adj root (D.neighbor n ω root a) := by
      change D.adjacency n ω root (D.neighbor n ω root a)=1
      exact (D.neighbor_exact n ω root _).mpr ⟨a,rfl⟩
    have href := source_pairModel_star_reference g hd root (D.neighbor n ω root) hadj
      (fun a => (hadj a).ne.symm) (D.neighbor_injective n ω root) r R hr hmargin
      htree w he.1 i j
    let vertex : Fin (d+1) → Fin (N n) := Fin.cases root (D.neighbor n ω root)
    have hentry := hlaw.1 (vertex i) (vertex j)
    rw [href] at hentry
    have hscaled : ‖D.resolvent n ω z (vertex i) (vertex j)-treeGreenStar d (by exact_mod_cast hd) z i j‖ =
        s⁻¹*‖g.G w (vertex i) (vertex j)-normalizedStarReference d (semicircleRoot w) w i j‖ := by
      rw [D.resolvent_eq_localLaw_green hd n ω z hz,←normalizedStarReference_scaled d hd z hz i j]
      simp only [Matrix.smul_apply,smul_eq_mul,←mul_sub,norm_mul,norm_inv,
        Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _)]
      rfl
    change ‖D.resolvent n ω z (vertex i) (vertex j)-treeGreenStar d (by exact_mod_cast hd) z i j‖≤_
    rw [hscaled]
    calc
      _ ≤ s⁻¹*(sourceUniformLawConstant d*scalarScale (spectralScale w)
          (realSourcePaperError 12 d (N n) r w)) :=
        mul_le_mul_of_nonneg_left hentry (inv_nonneg.mpr hs.le)
      _ ≤ (N n : ℝ)^(-(1/1024 : ℝ)) := by
        simpa only [s,r,div_eq_mul_inv,mul_assoc,mul_comm,mul_left_comm] using he.2.2

end GeneralizedBulk.External.RegularSpectralData
