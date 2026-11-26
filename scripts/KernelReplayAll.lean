import GeneralizedBulk
import GaussianWave
import BourgadeHuang
import LocalLaw.Audit
import SpectralConsequences.Audit
import Lean.Replay

/-! Replay all five merged mathematical libraries in a fresh kernel environment.
The imported `.olean` declarations are evidence to be checked, rather than
trusted proof objects. Types and bodies are checked at trust level zero.
Generated implementation auxiliaries are treated exactly as in Lean.Replay;
the complete logical dependency closure of each endpoint must avoid them.
-/
set_option maxHeartbeats 0
open Lean Elab Command

run_cmd do
  let source ← getEnv
  let roots : Array Name := #[`GeneralizedBulk, `GaussianWave, `BourgadeHuang,
    `LocalLaw, `SpectralConsequences]
  let projectModule := fun n : Name => roots.any (·.isPrefixOf n)
  let modules := source.header.moduleNames.filter projectModule
  let mut declarations : Std.HashMap Name ConstantInfo := {}
  let mut byModule : Std.HashMap Name (Std.HashMap Name ConstantInfo) := {}
  let mut counts := Array.replicate roots.size 0
  for (name, info) in source.constants.toList do
    if let some idx := source.getModuleIdxFor? name then
      let moduleName := source.header.moduleNames[idx.toNat]!
      if projectModule moduleName then
        declarations := declarations.insert name info
        let members := (byModule[moduleName]?).getD {}
        byModule := byModule.insert moduleName (members.insert name info)
        for i in [:roots.size] do
          if roots[i]!.isPrefixOf moduleName then
            counts := counts.modify i (· + 1)
  let safe := declarations.toList.countP (fun (_, info) => !info.isUnsafe && !info.isPartial)
  for i in [:roots.size] do
    if counts[i]! == 0 then
      throwError "No declarations selected from required library {roots[i]!}"
    logInfo m!"{roots[i]!}: {counts[i]!} declarations selected for merged kernel replay."
  let required : Array Name := #[
    `GeneralizedBulk.Graph.uniform_regular_graph_bulk_universality,
    `GeneralizedBulk.External.RegularSpectralData.bulk_universality,
    `GeneralizedBulk.Graph.uniform_graph_star_wasserstein,
    `GeneralizedBulk.Graph.uniform_root_fourth_probability,
    `GeneralizedBulk.Graph.uniform_graph_mixed_fourth,
    `GeneralizedBulk.Graph.uniform_regular_graph_bulk_universality_along_admissible_sizes,
    `GeneralizedBulk.Graph.uniform_graph_mixed_fourth_along_admissible_sizes,
    `GeneralizedBulk.Graph.article_polynomial_mixed_fourth,
    `GeneralizedBulk.Graph.regularGraph_nonempty_clique_blocks,
    `GeneralizedBulk.Graph.frequently_admissibleSize,
    `GeneralizedBulk.Graph.regularGraph_nonempty_of_arithmetic,
    `GeneralizedBulk.Graph.regularGraph_nonempty_iff_arithmetic,
    `GeneralizedBulk.Graph.admissibleSize_iff_arithmetic,
    `GeneralizedBulk.Graph.admissibleSizeFilter_eq_arithmetic,
    `GeneralizedBulk.Graph.arithmeticSizeFilter_neBot,
    `GeneralizedBulk.Graph.uniform_graph_star_wasserstein_sup,
    `GeneralizedBulk.Graph.fixedEnergyStarWassersteinSup,
    `GeneralizedBulk.Graph.measurable_fixedEnergyStarWassersteinSup,
    `GeneralizedBulk.Graph.fixedEnergyStarWassersteinSup_eq_zero_of_empty,
    `GeneralizedBulk.Graph.graphEigenCandidate_wassersteinTwoSquared_common_energy_le,
    `GeneralizedBulk.Graph.fixedEnergyStarWassersteinSup_le,
    `GeneralizedBulk.Graph.fixedEnergyStarWassersteinSup_lt_top,
    `GeneralizedBulk.Graph.fixedEnergyStarWassersteinSupReal,
    `GeneralizedBulk.Graph.ofReal_fixedEnergyStarWassersteinSupReal,
    `GeneralizedBulk.Graph.measurable_fixedEnergyStarWassersteinSupReal,
    `GeneralizedBulk.Graph.fixedEnergyStarWassersteinSupReal_eq_zero_of_empty,
    `GeneralizedBulk.Graph.uniform_graph_star_wasserstein_fixed_energy,
    `GeneralizedBulk.Graph.uniform_graph_star_wasserstein_fixed_energy_sup,
    `GeneralizedBulk.Graph.corollary_1_3,
    `GeneralizedBulk.Graph.corollary_1_3_real,
    `GeneralizedBulk.Graph.corollary_1_3_along_sizes,
    `GeneralizedBulk.Graph.corollary_1_3_real_along_sizes,
    `GeneralizedBulk.Graph.selected_graph_star_wasserstein,
    `GeneralizedBulk.Graph.selected_graph_star_wasserstein_common_energy,
    `GeneralizedBulk.External.RegularSpectralData.provedBSQualitativeInput,
    `GeneralizedBulk.External.RegularSpectralData.provedHYCoarseInput,
    `GeneralizedBulk.External.RegularSpectralData.provedHYMesoscopicInput,
    `GeneralizedBulk.External.RegularSpectralData.provedHYLocalStarInput,
    `GeneralizedBulk.External.RegularSpectralData.provedHYGeometryInput,
    `GaussianWave.BS.RRGClassificationEvents.eigenvectors_BSJointClassification,
    `GaussianWave.BS.RRGClassificationEvents.signals_BSJointClassification,
    `BourgadeHuang.RationalBulk.gaussianBeta_vague_full_convergence,
    `SpectralConsequences.full_paper_theorem_1_2,
    `SpectralConsequences.full_paper_theorem_1_4,
    `LocalLaw.source_theorem_4_2]
  for name in required do
    unless declarations.contains name do
      throwError "Missing required merged declaration {name}"
  -- Traverse types, theorem/definition bodies, opaque bodies, and constructors.
  -- This also inspects base-library dependencies for excluded implementations.
  let mut seen : NameSet := {}
  let mut todo := required
  let mut cursor := 0
  while cursor < todo.size do
    let name := todo[cursor]!
    cursor := cursor + 1
    unless seen.contains name do
      seen := seen.insert name
      let some info := source.toKernelEnv.find? name
        | throwError "Missing logical dependency {name}"
      if info.isUnsafe || info.isPartial then
        throwError "Logical endpoint dependency would be skipped by Lean.Replay: {name}"
      for dependency in info.getUsedConstantsAsSet do
        todo := todo.push dependency
  logInfo m!"Merged replay: {modules.size} modules; {safe} safe declarations; {declarations.size-safe} generated implementation auxiliaries skipped. Complete endpoint closure: {seen.size} safe constants."
  let base ← liftM <| importModules #[{module := `Mathlib}, {module := `Lean.Replay}] {} 0
  if base.header.trustLevel != 0 then
    throwError "Fresh base environment has nonzero trust level"
  for (name, _) in declarations.toList do
    if base.contains name then
      throwError "Base environment already contains a project declaration: {name}"
  let mut checked := base
  let mut replayedModules := 0
  for moduleName in modules do
    let members := (byModule[moduleName]?).getD {}
    -- Preserve the checked kernel; discard elaborator-only private-name tries
    -- between modules, as required by Lean 4.19's private-name normalization.
    let clean := Environment.ofKernelEnv checked.toKernelEnv
    checked ← liftM <| Environment.replay members clean
    replayedModules := replayedModules + 1
    if replayedModules % 100 == 0 then
      liftM <| IO.println s!"Merged kernel replay progress: {replayedModules}/{modules.size} modules; completed {moduleName}"
    for (name, original) in members.toList do
      if !original.isUnsafe && !original.isPartial then
        let some replayed := checked.toKernelEnv.find? name
          | throwError "Kernel environment missing {name} after replay of {moduleName}"
        unless original.type == replayed.type &&
            original.value? true == replayed.value? true &&
            original.levelParams == replayed.levelParams do
          throwError "Replayed declaration changed type/body/universes: {name}"
  if checked.header.trustLevel != 0 then
    throwError "Merged replay environment has nonzero trust level"
  for name in required do
    let some original := declarations[name]? | throwError "Missing original endpoint {name}"
    let some replayed := checked.toKernelEnv.find? name
      | throwError "Required endpoint was not replayed: {name}"
    unless original.type == replayed.type && original.value? true == replayed.value? true do
      throwError "Final endpoint differs after kernel replay: {name}"
  logInfo m!"PASSED: all {safe} safe declarations from all five merged libraries replayed at trust level zero, with identical types and bodies. Every project declaration in the endpoint closure was replayed; base-library dependencies were checked for excluded implementations."
