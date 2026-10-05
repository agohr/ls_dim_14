import QuaternionicSymmetry.ManifoldTwistorBWW66ReductiveTransformationSource
import QuaternionicSymmetry.ManifoldQuaternionicIsometryCompactness
import QuaternionicSymmetry.ManifoldTwistorORSWFixedWeightComparison
import QuaternionicSymmetry.ManifoldTwistorORSWSeedApplication
import QuaternionicSymmetry.ManifoldTwistorORSWCompactRealFormApplication
import QuaternionicSymmetry.ManifoldQuaternionicIsometryLieFromSources
import QuaternionicSymmetry.ManifoldTwistorPicardContactLieAction
import QuaternionicSymmetry.HolomorphicLineCoreSheafPicardGenerator

/-! Actual ORSW5.1 application with all real and complex group atlases and
the compact real form selected internally. The same compact maximal torus,
actual unpowered vertical weights and literal extremal components are used.
Extremal isolation remains explicit for the separate induction proof. -/
namespace QuaternionicSymmetry.ManifoldTwistorORSWRecognitionApplication

open GeneralContactFanoORSWRecognitionSource ManifoldTwistorORSWFixedWeightComparison
open ManifoldQuaternionicMaximalTorusAction
open ManifoldQuaternionicTorusFixedComplexComponent
open ManifoldQuaternionicActualWeightHull ManifoldQuaternionicVerticalCircleCharacter
open GeneralContactFanoORSWSource GeneralContactFanoPicardUniquenessSource
open GeneralHolomorphicFullAutomorphismLieSource
open ManifoldTwistorORSWSeedApplication ManifoldTwistorORSWCompactRealFormApplication
open ManifoldTwistorNTContactInfinitesimalSource
open ManifoldTwistorBKKPicardUniquenessApplication
open ManifoldTwistorUniqueContactFullEquiv ManifoldTwistorUniqueContactFullLieTransfer
open ManifoldTwistorLeBrunComplexAtlas ManifoldTwistorSphereCore
open ManifoldTwistorContactAutomorphisms ManifoldTwistorFullAutomorphisms
open ManifoldTwistorLineCoreClasses ManifoldPositiveQuaternionicKahlerGeometry
open ManifoldQuaternionicSpanSymmetry ManifoldQuaternionicTorusAction
open HolomorphicLineCoreAmpleFiniteMap HolomorphicLineCoreSheafPicardGenerator
open HolomorphicLineSheafClasses HolomorphicLineSheafClassGroup
open GeneralClosedSubgroupLieSource GeneralSmoothMapSource
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [Nonempty M]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [CompactSpace M] [PreconnectedSpace M] [T3Space M]

/-- Actual recognition with no group atlas or compact-real-form witness
supplied by the caller. Geometric isolation uses the selected literal torus. -/
theorem contactAut_transitive_of_picard_extreme_isolation_from_sources
    (hORSW : AnalyticCompactRealFormExtremalRecognition)
    (hUnique : AnalyticContactPicardGeneratorPreservesDistribution)
    (hAutSource : ManifoldTwistorBWW66ReductiveTransformationSource.FullAutReductiveTransformationSource)
    (hNT : NTContactInfinitesimalComplexificationSource)
    (hCompact : ManifoldQuaternionicIsometryCompactness.QuaternionicIsometryCompactness)
    (hR3 : ManifoldRiemannianIsometryLieInput.IsometryLieSource.{0,0})
    (hClosed : LeeClosedEmbeddingTheorem)
    (hImm : LeeEquivariantImmersionTheorem)
    (hLee : LeeEmbeddedCodomainRestrictionTheorem)
    (P : CompactConnectedPositiveQuaternionicKahlerGeometry (E := E) (M := M))
    (n : ℕ) (hn : 2 ≤ n) (hDim : Module.finrank ℝ E = 4*n)
    (A : CompatibleComplexAtlas P.tangent P.connection n)
    (C : NondegenerateHolomorphicContactData P.tangent P.connection n A)
    (hAmple : letI := A.charts
      letI := A.complexManifold
      AmpleCore 𝓘(ℂ,ComplexTwistorModel n)
        (contactLineCore P.tangent P.connection C.contact.line))
    (hPic : letI := A.charts
      letI := A.complexManifold
      Function.Bijective (fun q : ℤ =>
        (classMulEquiv 𝓘(ℂ,ComplexTwistorModel n)
          (contactClass P.tangent P.connection C.contact.line) :
          SheafClass (B := SphereBundleTotal P.tangent)
            𝓘(ℂ,ComplexTwistorModel n)) ^ q))
    {r : ℕ} (T : CompactLieTorusInputs.TorusEmbedding (QuaternionicIsometries P.tangent) r)
    (hr : 2 ≤ r) (hMax : T.IsMaximal (QuaternionicIsometries P.tangent))
    (hIso : ∀ (z : SphereBundleTotal P.tangent)
      (hz : ∀ t, (actionOfEmbedding P.tangent T).representation t • z = z)
      (μ : Fin r → ℤ),
      (∀ t, torusVerticalCircleCharacter P.tangent hR3
        (actionOfEmbedding P.tangent T) z hz t = weightCharacter μ t) →
      (fun i => (μ i : ℝ)) ∈
        (convexHull ℝ (actualRealWeights P.tangent hR3
          (actionOfEmbedding P.tangent T))).extremePoints ℝ →
      (component P.tangent (actionOfEmbedding P.tangent T) z).Subsingleton) :
    ∀ z w : SphereBundleTotal P.tangent,
      ∃ f : ContactAutomorphisms P.tangent P.connection A C.contact.line,
        f.1 z = w := by
  letI : CompactSpace M := ⟨P.compact⟩
  letI : PreconnectedSpace M := ⟨P.connected⟩
  letI : T3Space M := inferInstance
  letI : ConnectedSpace M := {
    toPreconnectedSpace := inferInstance
    toNonempty := inferInstance }
  letI := A.charts
  letI := A.complexManifold
  letI : CompactSpace (QuaternionicIsometries P.tangent) :=
    hCompact
      P.toPositiveQuaternionicKahlerGeometry n hn hDim
  obtain ⟨VR,hNormR,hSpaceR,hFiniteR,hChartR,hManifoldR,hLieR⟩ :=
    ManifoldQuaternionicIsometryLieFromSources.exists_real_lie_atlas
      P.toPositiveQuaternionicKahlerGeometry n hn hDim hClosed hR3
  letI := hNormR
  letI := hSpaceR
  letI := hFiniteR
  letI := hChartR
  letI := hManifoldR
  letI := hLieR
  have hPreserve := fullPreservesContact_of_analyticPicard_generator
    hUnique P n (by omega) A C hAmple hPic
  obtain ⟨VC,hNormC,hSpaceC,hFiniteC,hChartC,hManifoldC,hLieC,hJoint,_hRad⟩ :=
    hAutSource P n hn hDim A
  letI := hNormC
  letI := hSpaceC
  letI := hFiniteC
  letI : ChartedSpace VC (TwistorHolomorphicAutomorphisms P.tangent P.connection A) := hChartC
  letI : IsManifold 𝓘(ℂ,VC) ∞ (TwistorHolomorphicAutomorphisms P.tangent P.connection A) := hManifoldC
  letI : LieGroup 𝓘(ℂ,VC) ∞ (TwistorHolomorphicAutomorphisms P.tangent P.connection A) := hLieC
  have hReal := actual_contact_lift_isCompactRealForm
    hNT hR3 hCompact hClosed hImm hLee P n hn hDim A C hPreserve
    hChartR hManifoldR hLieR hJoint
  letI := contactCharts (V := VC) P.tangent P.connection A C.contact.line hPreserve
  letI := contactManifold (V := VC) P.tangent P.connection A C.contact.line hPreserve
  letI := contactLieGroup (V := VC) P.tangent P.connection A C.contact.line hPreserve
  have hContactJoint := contact_joint_holomorphic_of_full
    P.tangent P.connection A C.contact.line hPreserve hJoint
  have hCorePic := (core_zpow_bijective_iff_analyticPicard
    (B := SphereBundleTotal P.tangent) 𝓘(ℂ,ComplexTwistorModel n)
    (contactLineCore P.tangent P.connection C.contact.line)).mpr hPic
  letI : ChartedSpace VC
      (GeneralHolomorphicDistributionAutomorphisms.Automorphisms
        (contactDistribution P.tangent P.connection A C.contact.line)) :=
    inferInstanceAs (ChartedSpace VC
      (ContactAutomorphisms P.tangent P.connection A C.contact.line))
  letI : IsManifold 𝓘(ℂ,VC) ∞
      (GeneralHolomorphicDistributionAutomorphisms.Automorphisms
        (contactDistribution P.tangent P.connection A C.contact.line)) :=
    inferInstanceAs (IsManifold 𝓘(ℂ,VC) ∞
      (ContactAutomorphisms P.tangent P.connection A C.contact.line))
  letI : LieGroup 𝓘(ℂ,VC) ∞
      (GeneralHolomorphicDistributionAutomorphisms.Automorphisms
        (contactDistribution P.tangent P.connection A C.contact.line)) :=
    inferInstanceAs (LieGroup 𝓘(ℂ,VC) ∞
      (ContactAutomorphisms P.tangent P.connection A C.contact.line))
  exact hORSW (𝓘(ℝ,E).prod (𝓡 2)) n (by omega) C.toGeneralContactGeometry
    (contactDistribution P.tangent P.connection A C.contact.line)
    (ManifoldTwistorBKKPicardHomogeneityApplication.actual_contact_kernel
      P.tangent P.connection A C)
    hAmple hCorePic hContactJoint
    (isometryContactLift P.tangent P.connection A C.contact.line)
    hReal r T hr hMax (compactTwistorAction P.tangent T) (by intro t z; rfl)
    (compactContactFiberEquiv P.tangent P.connection A C T)
    (compactContactFiberEquiv_isCanonical P.tangent P.connection A C T)
    (isolatedExtremalComponents_of_actual P.tangent P.connection A C T hR3 hIso)

end
end QuaternionicSymmetry.ManifoldTwistorORSWRecognitionApplication
