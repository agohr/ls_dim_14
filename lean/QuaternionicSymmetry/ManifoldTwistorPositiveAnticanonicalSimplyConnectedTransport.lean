import QuaternionicSymmetry.ManifoldTwistorPositiveAnticanonicalSimplyConnected
import QuaternionicSymmetry.ManifoldQuaternionicHomothetyTwistorHomeomorph

/-! The actual homothety sphere-bundle homeomorphism transports simple
connectedness from the normalized twistor to the original one. No new
topological source or assumed comparison map is used. -/

namespace QuaternionicSymmetry.ManifoldTwistorPositiveAnticanonicalSimplyConnectedTransport

open GeneralPositiveAnticanonicalSimplyConnectedSource
open ManifoldTwistorPositiveAnticanonicalSimplyConnected
open ManifoldQuaternionicHomothetyReduction
open ManifoldQuaternionicHomothetyTwistorHomeomorph
open ManifoldPositiveQuaternionicKahlerHomothety
open ManifoldPositiveQuaternionicKahlerGeometry ManifoldQuaternionicKSWEq38Input
open ManifoldTwistorSphereCore
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [T3Space M] [SecondCountableTopology M] [Nonempty M]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [CompactSpace M] [PreconnectedSpace M]

/-- Transfer through the *constructed* metric-homothety twistor
homeomorphism, whose inverse is also continuous. -/
theorem simplyConnected_original_of_rescaled
    (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
      (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
    (s : ℝ) (hs : 0 < s)
    (hSC : SimplyConnectedSpace
      (SphereBundleTotal (rescaleMetric Q s (ne_of_gt hs)))) :
    SimplyConnectedSpace (SphereBundleTotal Q) := by
  letI := hSC
  exact ((sphereTotalHomeomorph Q s (ne_of_gt hs)).symm.toHomotopyEquiv).simplyConnectedSpace

/-- Every actual higher-dimensional compact connected positive input has
simply connected **original** twistor, relative to the published general
Fano theorem, existing T1, and existing KSW scalar normalization. -/
theorem original_twistor_simplyConnected
    (hBallmann : BallmannPositiveAnticanonicalSimplyConnected)
    (hT1 : ManifoldTwistorPositiveRicciInput.NormalizedPositiveRicciContactExistence)
    (S : QuaternionicStructure E)
    (P : CompactConnectedPositiveQuaternionicKahlerGeometry (E := E) (M := M))
    (heq38 : KSWEq38OnModel (E := E) (M := M))
    (hn : 2 ≤ S.quaternionicDimension) :
    SimplyConnectedSpace (SphereBundleTotal P.tangent) := by
  obtain ⟨s,hs,hSC⟩ := exists_rescaled_twistor_simplyConnected
    hBallmann hT1 S P heq38 hn
  exact simplyConnected_original_of_rescaled P.tangent s hs hSC

end
end QuaternionicSymmetry.ManifoldTwistorPositiveAnticanonicalSimplyConnectedTransport
