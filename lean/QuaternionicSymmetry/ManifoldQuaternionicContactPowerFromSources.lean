import QuaternionicSymmetry.ManifoldQuaternionicActualTwistorTangentContinuity
import QuaternionicSymmetry.ManifoldQuaternionicContactPowerGeometricWeights

/-! The actual joint tangent action is now proved from BG-R3. Thus the
complete contact-power representation has an integral eigenbasis using only
the registered general finiteness and compact-character inputs. No internal
continuity hypothesis remains. Ampleness below is still geometric data,
not a new literature premise. -/
namespace QuaternionicSymmetry.ManifoldQuaternionicContactPowerFromSources

open ManifoldQuaternionicSpanSymmetry ManifoldQuaternionicTorusAction
open ManifoldQuaternionicContactPowerFiniteSections
open ManifoldQuaternionicContactPowerContinuity
open ManifoldQuaternionicContactPowerContinuousFaithful
open ManifoldQuaternionicContactPowerWeights ManifoldQuaternionicContactPowerGeometricWeights
open ManifoldQuaternionicActualTwistorTangentContinuity
open ManifoldQuaternionicActualWeightHull
open ManifoldTwistorLeBrunComplexAtlas ManifoldTwistorLineCoreClasses
open ManifoldTwistorSphereCore HolomorphicLineCorePullback
open HolomorphicLineTensorPowerClasses HolomorphicLineCoreAmpleFiniteMap
open CompactTorusEigenbasisSource TorusCharacterInput TorusLaurentRepresentation
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [T3Space M] [CompactSpace M] [SecondCountableTopology M]
  [PreconnectedSpace M] [Nonempty M]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
  (hR3 : ManifoldRiemannianIsometryLieInput.IsometryLieSource.{0,0})
  (hFinite : HolomorphicLineFiniteSectionsSource.CompactHolomorphicLineSectionFiniteness)
  (hEigen : KnappTorusEigenbasis) (hCircle : CircleCharacterSource)
  {r : ℕ} (T : ContinuousTorusAction Q r)
  (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)
  {n : ℕ} (B : CompatibleComplexAtlas Q D n)
  (C : HolomorphicContactData Q D n B)

include hR3 in
theorem continuous_contactPowerTorusAction_from_sources (k : ℕ) :
    letI := B.charts
    letI := contactPowerSectionsNormedAddCommGroup Q hFinite D B C k
    Continuous (fun p : Torus r × PowerSections Q D B C k =>
      contactPowerTorusRepresentation Q T D B C k p.1 p.2) :=
  continuous_contactPowerTorusAction_of_existing_tangent Q hFinite T D B C k
    (continuous_jointSphereTangentAction Q hR3)

include hR3 hFinite hEigen hCircle in
theorem exists_integral_eigenbasis_from_sources (k : ℕ) :
    letI := B.charts
    ∃ b : Module.Basis (Fin (Module.finrank ℂ (PowerSections Q D B C k)))
      ℂ (PowerSections Q D B C k),
      ∃ μ : Fin (Module.finrank ℂ (PowerSections Q D B C k)) → Fin r → ℤ,
        ∀ (t : Torus r) (i : Fin (Module.finrank ℂ (PowerSections Q D B C k))),
          contactPowerTorusRepresentation Q T D B C k t (b i) =
            (weightCharacter (μ i) t : ℂ) • b i :=
  exists_integral_contactPower_eigenbasis Q hFinite hEigen hCircle T D B C k
    (continuous_jointSphereTangentAction Q hR3)

include hR3 hFinite hEigen hCircle in
theorem exists_laurent_extension_from_sources (k : ℕ) :
    letI := B.charts
    ∃ b : Module.Basis (Fin (Module.finrank ℂ (PowerSections Q D B C k)))
      ℂ (PowerSections Q D B C k),
      ∃ μ : Fin (Module.finrank ℂ (PowerSections Q D B C k)) → Fin r → ℤ,
        ∀ t : Torus r, complexRepresentation b μ (compactInclusion r t) =
          contactPowerTorusRepresentation Q T D B C k t :=
  exists_contactPower_laurent_extension Q hFinite hEigen hCircle T D B C k
    (continuous_jointSphereTangentAction Q hR3)

include hFinite hEigen hCircle in
theorem actual_weights_finite_of_ample
    (hAmple : letI := B.charts; letI := B.complexManifold
      AmpleCore 𝓘(ℂ,ComplexTwistorModel n) (contactLineCore Q D C.line)) :
    (actualIntegralWeights Q hR3 T).Finite ∧ (actualRealWeights Q hR3 T).Finite := by
  letI := B.charts
  letI := B.complexManifold
  obtain ⟨k,hk,hVery⟩ := hAmple
  obtain ⟨b,μ,hμ⟩ :=
    exists_integral_eigenbasis_from_sources Q hR3 hFinite hEigen hCircle T D B C k
  obtain ⟨d,b',hGen,hEmbedding⟩ := hVery
  exact ⟨actualIntegralWeights_finite Q hR3 T D B C k b μ hμ hGen (Nat.ne_of_gt hk),
    actualRealWeights_finite Q hR3 T D B C k b μ hμ hGen (Nat.ne_of_gt hk)⟩

end
end QuaternionicSymmetry.ManifoldQuaternionicContactPowerFromSources
