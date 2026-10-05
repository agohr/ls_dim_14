import QuaternionicSymmetry.Stage2IntrinsicClassification
import Lean.Util.CollectAxioms

/-! Guard the final endpoints against reintroducing the retired universal
preservation boundary or routing through a conditional full-group comparison.
Unlike an axiom audit, this checks named ordinary hypotheses and definitions
in both theorem types and proof bodies. -/

/- Eliminated contracts must remain proved adapters, not source fields.
Counting constructor fields distinguishes assumptions from dot-notation methods. -/
open Lean in
run_cmd do
  let env ← getEnv
  let some info := getStructureInfo? env ``QuaternionicSymmetry.Stage2IntrinsicSources.Sources
    | throwError "Missing final source record"
  unless info.fieldNames.size == 15 do
    throwError "Expected 15 literature fields, found {info.fieldNames.size}"
  for name in [
      ``QuaternionicSymmetry.Stage2IntrinsicSources.Sources.maximalTorus,
      ``QuaternionicSymmetry.Stage2IntrinsicSources.Sources.torusLie,
      ``QuaternionicSymmetry.Stage2IntrinsicSources.Sources.quaternionicSubmanifold,
      ``QuaternionicSymmetry.Stage2IntrinsicSources.Sources.ntHamiltonian,
      ``QuaternionicSymmetry.Stage2IntrinsicSources.Sources.circleCharacters,
      ``QuaternionicSymmetry.Stage2IntrinsicSources.Sources.eigenbasis,
      ``QuaternionicSymmetry.Stage2IntrinsicSources.Sources.embeddedRestriction,
      ``QuaternionicSymmetry.Stage2IntrinsicSources.Sources.finiteMapDimension,
      ``QuaternionicSymmetry.Stage2IntrinsicSources.Sources.equivariantImmersion,
      ``QuaternionicSymmetry.Stage2IntrinsicSources.Sources.adjointDifferential,
      ``QuaternionicSymmetry.Stage2IntrinsicSources.Sources.orbitSubmersion,
      ``QuaternionicSymmetry.Stage2IntrinsicSources.Sources.complexSubmanifold,
      ``QuaternionicSymmetry.Stage2IntrinsicSources.Sources.finiteSections,
      ``QuaternionicSymmetry.Stage2IntrinsicSources.Sources.fixedTotalGeodesy,
      ``QuaternionicSymmetry.Stage2IntrinsicSources.Sources.kswDecomposition,
      ``QuaternionicSymmetry.Stage2IntrinsicSources.Sources.kswSp1,
      ``QuaternionicSymmetry.Stage2IntrinsicSources.Sources.fixedComponents,
      ``QuaternionicSymmetry.Stage2IntrinsicSources.Sources.oneJet] do
    if (← getProjectionFnInfo? name).isSome then
      throwError "Eliminated contract {name} has returned as a source field"
    match ← getConstInfo name with
    | .thmInfo _ => pure ()
    | _ => throwError "Expected a proved adapter for {name}"
  logInfo "Contract elimination regression: 15 source fields and eighteen proved adapters; final proofs bypass Myers–Steenrod, Chow, Remmert, Kobayashi, Killing-radical, the ORSW rank seed, the compact rank-one dimension input, compact analytic-subset finiteness, the general Riemannian fixed-component input, and the general contact canonical theorem; KSW Eq. (3.8), the maximal-torus Lie correspondence, the positive quaternionic-submanifold theorem, and the canonical contact Hamiltonian bijection are now proved internally."

open Lean in
run_cmd do
  let env ← getEnv
  let roots := [
    ``QuaternionicSymmetry.Stage2IntrinsicClassification.intrinsicSymmetric_c12,
    ``QuaternionicSymmetry.Stage2IntrinsicClassification.intrinsicSymmetric_e14,
    ``QuaternionicSymmetry.Stage2IntrinsicClassification.exists_generated_ample_contact_c12,
    ``QuaternionicSymmetry.Stage2IntrinsicClassification.exists_generated_ample_contact_e14]
  let forbidden := [
    ``QuaternionicSymmetry.GeneralComplexContactData.GeneralContactCanonicalTheorem,
    ``QuaternionicSymmetry.ManifoldRiemannianFixedComponentGenericInput.RiemannianFixedComponentOnModel,
    ``QuaternionicSymmetry.HolomorphicAnalyticSubsetFiniteSource.SeparatedCompactAnalyticSubsetFiniteTheorem,
    ``QuaternionicSymmetry.HolomorphicSeparatedFiniteFibersSource.SeparatedCompactProjectiveFiberFiniteTheorem,
    ``QuaternionicSymmetry.CompactLieTorusInputs.CompactRankOneDimensionSource,
    ``QuaternionicSymmetry.CompactLieTorusInputs.CompactRankOneDimensionOnModel,
    ``QuaternionicSymmetry.GeneralContactFanoORSWSource.AnalyticCompactRealFormRankHomogeneity,
    ``QuaternionicSymmetry.GeneralKillingRadicalSource.KnappKillingRadicalSource,
    ``QuaternionicSymmetry.GeneralHolomorphicFullAutomorphismLieSource.KobayashiCompactAutomorphismTransformation,
    ``QuaternionicSymmetry.ProjectiveAnalyticAlgebraicSources.RemmertProjectiveImageTheorem,
    ``QuaternionicSymmetry.ProjectiveAnalyticAlgebraicSources.ChowProjectiveAnalyticTheorem,
    ``QuaternionicSymmetry.ManifoldRiemannianMyersSteenrodInput.MyersSteenrodSource,
    ``QuaternionicSymmetry.ManifoldRiemannianMyersSteenrodInput.MyersSteenrodConclusion,
    ``QuaternionicSymmetry.ManifoldQuaternionicIsometryPreservationInput.FullMetricSpanPreservation,
    ``QuaternionicSymmetry.ManifoldQuaternionicIsometryPreservationInput.fullMetricIsometryEquiv,
    ``QuaternionicSymmetry.ManifoldRiemannianIsometryLieInput.KillingLieSource]
  let mut state : CollectAxioms.State := {}
  for name in roots do
    let (_, next) := ((CollectAxioms.collect name).run env).run state
    for legacy in forbidden do
      if next.visited.contains legacy then
        throwError "{name} still depends on retired boundary {legacy}"
    state := next
  logInfo "Contract repair regression: all four final endpoints avoid every listed retired boundary, in both types and proof bodies."
