import GaussianWave.BS.Reused.Graph.Pairings
import GaussianWave.BS.Reused.Graph.UniformMarginals

/-!
# Simple configurations project to the uniform simple regular graph

A simple half-edge pairing has no root loop and has distinct neighboring
roots at every vertex. Its graph fiber is exactly the set of independent
port enumerations of each graph neighborhood, with cardinal `(d!)^N`.
-/
noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace GaussianWave.BS.Reused.Graph.Configuration

/-- The actual simplicity condition on a half-edge pairing. -/
def SimpleConfiguration {N d : ℕ} (p : Pairing (Fin N × Fin d)) : Prop :=
  (∀ h, (p.val h).1 ≠ h.1) ∧
    ∀ v, Function.Injective (fun j : Fin d => (p.val (v,j)).1)

abbrev SimplePairing (N d : ℕ) := {p : Pairing (Fin N × Fin d) // SimpleConfiguration p}

def pairingGraph {N d : ℕ} (p : Pairing (Fin N × Fin d)) (hp : SimpleConfiguration p) :
    SimpleGraph (Fin N) where
  Adj v w := ∃ j : Fin d, (p.val (v,j)).1 = w
  symm v w h := by
    obtain ⟨j,hj⟩ := h
    refine ⟨(p.val (v,j)).2, ?_⟩
    have heq : (w, (p.val (v,j)).2) = p.val (v,j) := Prod.ext hj.symm rfl
    rw [heq, p.property.1]
  loopless v h := by
    obtain ⟨j,hj⟩ := h
    exact hp.1 (v,j) hj

def pairingNeighborEquiv {N d : ℕ} (p : Pairing (Fin N × Fin d)) (hp : SimpleConfiguration p)
    (v : Fin N) : Fin d ≃ {w // (pairingGraph p hp).Adj v w} :=
  Equiv.ofBijective (fun j => ⟨(p.val (v,j)).1, ⟨j,rfl⟩⟩) ⟨
    fun j k h => hp.2 v (congrArg Subtype.val h),
    fun w => by obtain ⟨j,hj⟩ := w.property; exact ⟨j,Subtype.ext hj⟩⟩

theorem pairingGraph_regular {N d : ℕ} (p : Pairing (Fin N × Fin d)) (hp : SimpleConfiguration p) :
    (pairingGraph p hp).IsRegularOfDegree d := by
  intro v
  have heq : (pairingGraph p hp).neighborFinset v =
      Finset.univ.image (fun j : Fin d => (p.val (v,j)).1) := by
    ext w
    simp only [SimpleGraph.mem_neighborFinset, pairingGraph, Finset.mem_image,
      Finset.mem_univ, true_and]
  rw [SimpleGraph.degree, heq, Finset.card_image_of_injective _ (hp.2 v),
    Finset.card_univ, Fintype.card_fin]

def configurationGraph {N d : ℕ} (p : Pairing (Fin N × Fin d)) (hp : SimpleConfiguration p) :
    RegularGraph N d := ⟨pairingGraph p hp, pairingGraph_regular p hp⟩

def simpleConfigurationGraph {N d : ℕ} (p : SimplePairing N d) : RegularGraph N d :=
  configurationGraph p.val p.property

/-- The roots of every stub's mate determine a simple pairing uniquely;
the return port is forced by involutivity and distinct neighbors. -/
theorem pairing_eq_of_roots {N d : ℕ} (p q : Pairing (Fin N × Fin d))
    (hp : SimpleConfiguration p) (hroots : ∀ h, (p.val h).1 = (q.val h).1) : p = q := by
  apply Subtype.ext
  apply Equiv.ext
  intro h
  apply Prod.ext (hroots h)
  apply hp.2 (p.val h).1
  have heq : ((p.val h).1, (q.val h).2) = q.val h := Prod.ext (hroots h) rfl
  change (p.val ((p.val h).1, (p.val h).2)).1 = (p.val ((p.val h).1, (q.val h).2)).1
  rw [Prod.mk.eta, p.property.1, heq, hroots (q.val h), q.property.1]

/-- An independent enumeration of every graph neighborhood by its ports. -/
abbrev PortLabeling {N d : ℕ} (G : RegularGraph N d) :=
  ∀ v : Fin N, Fin d ≃ {w // G.val.Adj v w}

def labelingDartEquiv {N d : ℕ} (G : RegularGraph N d) (L : PortLabeling G) :
    (Fin N × Fin d) ≃ G.val.Dart where
  toFun h := ⟨(h.1, (L h.1 h.2).val), (L h.1 h.2).property⟩
  invFun a := (a.fst, (L a.fst).symm ⟨a.snd, a.adj⟩)
  left_inv h := by
    rcases h with ⟨v,j⟩
    change (v, (L v).symm (L v j)) = (v,j)
    exact Prod.ext rfl ((L v).symm_apply_apply j)
  right_inv a := by
    apply SimpleGraph.Dart.ext
    change (a.fst, ((L a.fst) ((L a.fst).symm ⟨a.snd,a.adj⟩)).val) = (a.fst,a.snd)
    exact Prod.ext rfl (congrArg Subtype.val ((L a.fst).apply_symm_apply ⟨a.snd,a.adj⟩))

def dartPairing {N : ℕ} (G : SimpleGraph (Fin N)) : Pairing G.Dart :=
  ⟨⟨SimpleGraph.Dart.symm, SimpleGraph.Dart.symm, SimpleGraph.Dart.symm_symm, SimpleGraph.Dart.symm_symm⟩,
    SimpleGraph.Dart.symm_symm, by
      intro a ha
      exact a.fst_ne_snd (congrArg (fun b : G.Dart => b.snd) ha)⟩

def labelingPairing {N d : ℕ} (G : RegularGraph N d) (L : PortLabeling G) : Pairing (Fin N × Fin d) :=
  conjugate (labelingDartEquiv G L).symm (dartPairing G.val)

@[simp] theorem labelingPairing_root {N d : ℕ} (G : RegularGraph N d) (L : PortLabeling G)
    (h : Fin N × Fin d) : ((labelingPairing G L).val h).1 = (L h.1 h.2).val := rfl

theorem labelingPairing_simple {N d : ℕ} (G : RegularGraph N d) (L : PortLabeling G) :
    SimpleConfiguration (labelingPairing G L) := by
  constructor
  · intro h hh
    have hl := (L h.1 h.2).property
    rw [← labelingPairing_root G L h, hh] at hl
    exact G.val.loopless _ hl
  · intro v j k hjk
    apply (L v).injective
    exact Subtype.ext hjk

theorem labelingPairing_graph {N d : ℕ} (G : RegularGraph N d) (L : PortLabeling G) :
    configurationGraph (labelingPairing G L) (labelingPairing_simple G L) = G := by
  apply Subtype.ext
  ext v w
  change (∃ j : Fin d, (L v j).val = w) ↔ G.val.Adj v w
  constructor
  · rintro ⟨j,hj⟩
    simpa only [hj] using (L v j).property
  · intro h
    exact ⟨(L v).symm ⟨w,h⟩, by simp⟩

abbrev ConfigurationFiber {N d : ℕ} (G : RegularGraph N d) :=
  {p : SimplePairing N d // simpleConfigurationGraph p = G}

def fiberPortLabeling {N d : ℕ} (G : RegularGraph N d) (p : ConfigurationFiber G) : PortLabeling G := by
  intro v
  let f : Fin d → {w // G.val.Adj v w} := fun j =>
    ⟨(p.val.val.val (v,j)).1, by
      have hg := congrArg Subtype.val p.property
      exact Eq.mp (congrArg (fun H : SimpleGraph (Fin N) => H.Adj v (p.val.val.val (v,j)).1) hg)
        (show (pairingGraph p.val.val p.val.property).Adj v (p.val.val.val (v,j)).1 from ⟨j,rfl⟩)⟩
  refine Equiv.ofBijective f ⟨?_, ?_⟩
  · intro j k h
    exact p.val.property.2 v (congrArg Subtype.val h)
  · intro w
    have hadj : (pairingGraph p.val.val p.val.property).Adj v w.val := by
      exact Eq.mpr (congrArg (fun H : SimpleGraph (Fin N) => H.Adj v w.val)
        (congrArg Subtype.val p.property)) w.property
    obtain ⟨j,hj⟩ := hadj
    exact ⟨j,Subtype.ext hj⟩

@[simp] theorem fiberPortLabeling_root {N d : ℕ} (G : RegularGraph N d) (p : ConfigurationFiber G)
    (v : Fin N) (j : Fin d) : (fiberPortLabeling G p v j).val = (p.val.val.val (v,j)).1 := rfl

/-- A graph fiber consists exactly of its independent vertex port labelings.
The inverse pairing is constructed by finding the unique reverse port. -/
def configurationFiberEquiv {N d : ℕ} (G : RegularGraph N d) : ConfigurationFiber G ≃ PortLabeling G where
  toFun := fiberPortLabeling G
  invFun L := ⟨⟨labelingPairing G L, labelingPairing_simple G L⟩, labelingPairing_graph G L⟩
  left_inv p := by
    apply Subtype.ext
    apply Subtype.ext
    apply pairing_eq_of_roots _ _ (labelingPairing_simple G (fiberPortLabeling G p))
    intro h
    rw [labelingPairing_root]
    rfl
  right_inv L := by
    funext v
    apply Equiv.ext
    intro j
    apply Subtype.ext
    rfl

theorem regular_neighbor_card {N d : ℕ} (G : RegularGraph N d) (v : Fin N) :
    Fintype.card {w // G.val.Adj v w} = d := by
  change Fintype.card (G.val.neighborSet v) = d
  rw [SimpleGraph.card_neighborSet_eq_degree, G.property.degree_eq]

def canonicalPortLabeling {N d : ℕ} (G : RegularGraph N d) : PortLabeling G :=
  fun v => Fintype.equivOfCardEq (by rw [Fintype.card_fin, regular_neighbor_card G v])

theorem portLabeling_card {N d : ℕ} (G : RegularGraph N d) :
    Fintype.card (PortLabeling G) = (Nat.factorial d) ^ N := by
  rw [Fintype.card_pi]
  have hc (v : Fin N) : Fintype.card (Fin d ≃ {w // G.val.Adj v w}) = Nat.factorial d := by
    simpa only [Fintype.card_fin] using Fintype.card_equiv (canonicalPortLabeling G v)
  simp only [hc, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem configurationGraph_fiber_card {N d : ℕ} (G : RegularGraph N d) :
    (Finset.univ.filter (fun p : SimplePairing N d => simpleConfigurationGraph p = G)).card =
      (Nat.factorial d) ^ N := by
  rw [← Fintype.card_subtype, Fintype.card_congr (configurationFiberEquiv G)]
  exact portLabeling_card G

theorem simplePairing_card (N d : ℕ) :
    Fintype.card (SimplePairing N d) = Fintype.card (RegularGraph N d) * (Nat.factorial d) ^ N := by
  rw [← Fintype.card_congr (Equiv.sigmaFiberEquiv (simpleConfigurationGraph (N := N) (d := d))),
    Fintype.card_sigma]
  have hc (G : RegularGraph N d) : Fintype.card (ConfigurationFiber G) = (Nat.factorial d) ^ N := by
    rw [Fintype.card_congr (configurationFiberEquiv G)]
    exact portLabeling_card G
  simp only [hc, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.cast_id]

theorem simplePairing_nonempty (N d : ℕ) [Nonempty (RegularGraph N d)] : Nonempty (SimplePairing N d) := by
  obtain ⟨G⟩ := (inferInstance : Nonempty (RegularGraph N d))
  exact ⟨⟨labelingPairing G (canonicalPortLabeling G), labelingPairing_simple G _⟩⟩

def simpleConfigurationLaw (N d : ℕ) : Measure (SimplePairing N d) := finiteUniform _

/-- The actual finite uniform simple-configuration law has exactly the
uniform labeled simple regular graph marginal. -/
theorem simpleConfigurationLaw_graph_marginal (N d : ℕ) [Nonempty (RegularGraph N d)] :
    Measure.map simpleConfigurationGraph (simpleConfigurationLaw N d) = regularGraphLaw N d := by
  letI := simplePairing_nonempty N d
  exact finiteUniform_map_of_fiber_card simpleConfigurationGraph ((Nat.factorial d) ^ N)
    (pow_pos (Nat.factorial_pos d) N) configurationGraph_fiber_card

end GaussianWave.BS.Reused.Graph.Configuration
