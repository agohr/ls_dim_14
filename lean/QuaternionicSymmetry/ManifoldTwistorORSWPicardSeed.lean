import QuaternionicSymmetry.ManifoldTwistorBWW66ReductiveTransformationSource
import QuaternionicSymmetry.ManifoldTwistorORSWSeedApplication
import QuaternionicSymmetry.ManifoldTwistorORSWCompactRealFormApplication
import QuaternionicSymmetry.ManifoldQuaternionicIsometryLieFromSources
import QuaternionicSymmetry.ManifoldTwistorPicardContactLieAction
import QuaternionicSymmetry.HolomorphicLineCoreSheafPicardGenerator

/-! On the actual Picard branch, real and complex group atlases and the
compact real form are selected internally from the named general sources.
The torus rank is the actual rank predicate supplied by the numerical chain,
not an algebraic-group rank marker. The external ORSW derivation is reviewed in
Textbooks/STAGE2_SOURCE_REVIEW_20261001.md; final release audit is separate. -/
namespace QuaternionicSymmetry.ManifoldTwistorORSWPicardSeed

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

/-- Actual seed homogeneity with no group atlas or compact-real-form witness
supplied by the caller. All three are chosen in one compatible action atlas. -/
theorem contactAut_transitive_of_picard_rank_two_from_sources
    (hORSW : AnalyticCompactRealFormRankHomogeneity)
    (hUnique : AnalyticContactPicardGeneratorPreservesDistribution)
    (hAutSource : ManifoldTwistorBWW66ReductiveTransformationSource.FullAutReductiveTransformationSource)
    (hNT : NTContactInfinitesimalComplexificationSource)
    (hR3 : ManifoldRiemannianIsometryLieInput.IsometryLieSource.{0,0})
    (hClosed : LeeClosedEmbeddingTheorem)
    (hImm : LeeEquivariantImmersionTheorem)
    (hLee : LeeEmbeddedCodomainRestrictionTheorem)
    (P : CompactConnectedPositiveQuaternionicKahlerGeometry (E := E) (M := M))
    (n : ℕ) (hn : 2 ≤ n) (hn7 : n ≤ 7) (hDim : Module.finrank ℝ E = 4*n)
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
    (hRank : HasTorusRankAtLeast P.tangent 2) :
    ∀ z w : SphereBundleTotal P.tangent,
      ∃ f : ContactAutomorphisms P.tangent P.connection A C.contact.line,
        f.1 z = w := by
  letI : CompactSpace M := ⟨P.compact⟩
  letI : PreconnectedSpace M := ⟨P.connected⟩
  letI : T3Space M := inferInstance
  letI := A.charts
  letI := A.complexManifold
  letI : CompactSpace (QuaternionicIsometries P.tangent) :=
    ManifoldQuaternionicIsometryClosedSubgroup.quaternionicIsometries_compactSpace_of_isometryLie
      P.tangent (hR3 P.tangent)
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
    hNT hR3 (ManifoldQuaternionicIsometryCompactness.compactness_of_isometryLie hR3) hClosed hImm hLee P n hn hDim A C hPreserve
    hChartR hManifoldR hLieR hJoint
  letI := contactCharts (V := VC) P.tangent P.connection A C.contact.line hPreserve
  letI := contactManifold (V := VC) P.tangent P.connection A C.contact.line hPreserve
  letI := contactLieGroup (V := VC) P.tangent P.connection A C.contact.line hPreserve
  have hContactJoint := contact_joint_holomorphic_of_full
    P.tangent P.connection A C.contact.line hPreserve hJoint
  obtain ⟨T,hFaithful⟩ := hRank
  let TK : CompactLieTorusInputs.TorusEmbedding (QuaternionicIsometries P.tangent) 2 :=
    ⟨T.representation,
      ManifoldQuaternionicIsometryTopology.continuous_representation_of_action
        P.tangent T.representation T.continuous_action,
      hFaithful⟩
  have hCorePic := (core_zpow_bijective_iff_analyticPicard
    (B := SphereBundleTotal P.tangent) 𝓘(ℂ,ComplexTwistorModel n)
    (contactLineCore P.tangent P.connection C.contact.line)).mpr hPic
  exact contactAut_transitive_of_compactRealForm_rank_two hORSW P n hn hn7 A C
    hAmple hCorePic hContactJoint
    (isometryContactLift P.tangent P.connection A C.contact.line) hReal TK

end
end QuaternionicSymmetry.ManifoldTwistorORSWPicardSeed
