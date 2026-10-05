import QuaternionicSymmetry.TorusDiagonalProjectiveFaithfulWeightSpan
import QuaternionicSymmetry.ManifoldQuaternionicContactPowerFromSources

/-! Actual complete contact-power sections of a faithful compact torus
have real-spanning integral weights for one selected very ample power.
The power, basis and weights are the SAME witnesses from the genuine
equivariant embedding. No claim is made for the unpowered contact line. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicContactPowerWeightSpan

open TorusDiagonalProjectiveFaithfulWeightSpan TorusFaithfulWeightSpan
open ManifoldQuaternionicContactPowerFromSources
open ManifoldQuaternionicContactPowerContinuousFaithful
open ManifoldQuaternionicContactPowerContinuity
open ManifoldQuaternionicContactPowerWeights
open ManifoldQuaternionicActualTwistorTangentContinuity
open ManifoldQuaternionicTorusAction
open ManifoldTwistorLeBrunComplexAtlas ManifoldTwistorLineCoreClasses
open ManifoldTwistorSphereCore HolomorphicLineCorePullback
open HolomorphicLineTensorPowerClasses HolomorphicLineCoreAmpleFiniteMap
open CompactTorusEigenbasisSource TorusCharacterInput
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [T3Space M] [CompactSpace M]
  [SecondCountableTopology M] [PreconnectedSpace M] [Nonempty M]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

theorem exists_veryAmple_contactPower_realSpanning_weights
    (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
      (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
    (hR3 : ManifoldRiemannianIsometryLieInput.IsometryLieSource.{0,0})
    (hFinite : HolomorphicLineFiniteSectionsSource.CompactHolomorphicLineSectionFiniteness)
    (hEigen : KnappTorusEigenbasis) (hCircle : CircleCharacterSource)
    {r : ℕ} (T : ContinuousTorusAction Q r) (hFaithful : T.Faithful)
    (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)
    {n : ℕ} (B : CompatibleComplexAtlas Q D n)
    (C : HolomorphicContactData Q D n B)
    (hAmple : letI := B.charts; letI := B.complexManifold
      AmpleCore 𝓘(ℂ,ComplexTwistorModel n) (contactLineCore Q D C.line)) :
    letI := B.charts
    letI := B.complexManifold
    ∃ k : ℕ, 0 < k ∧
      VeryAmpleCore 𝓘(ℂ,ComplexTwistorModel n)
        (powerCoreRep 𝓘(ℂ,ComplexTwistorModel n)
          (contactLineCore Q D C.line) k) ∧
      ∃ b : Module.Basis (Fin (Module.finrank ℂ (PowerSections Q D B C k)))
        ℂ (PowerSections Q D B C k),
      ∃ μ : Fin (Module.finrank ℂ (PowerSections Q D B C k)) → Fin r → ℤ,
        (∀ (t : Torus r) i,
          contactPowerTorusRepresentation Q T D B C k t (b i) =
            (weightCharacter (μ i) t : ℂ) • b i) ∧
        Submodule.span ℝ (Set.range
          (fun i => integralWeightLinear (μ i))) = ⊤ := by
  letI := B.charts
  letI := B.complexManifold
  obtain ⟨k,hk,hVery,hFD,hCont,hScalarFaith⟩ :=
    exists_veryAmple_power_continuous_projectively_faithful
      Q hFinite T hFaithful D B C hAmple
      (continuous_jointSphereTangentAction Q hR3)
  obtain ⟨b,μ,hμ⟩ :=
    exists_integral_eigenbasis_from_sources Q hR3 hFinite hEigen hCircle
      T D B C k
  refine ⟨k,hk,hVery,b,μ,hμ,?_⟩
  exact integral_weights_span_of_projective_faithfulness
    (contactPowerTorusRepresentation Q T D B C k) b μ hμ hScalarFaith

end
end QuaternionicSymmetry.ManifoldQuaternionicContactPowerWeightSpan
