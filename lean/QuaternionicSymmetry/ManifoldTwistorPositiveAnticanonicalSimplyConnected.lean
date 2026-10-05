import QuaternionicSymmetry.GeneralPositiveAnticanonicalSimplyConnectedSource
import QuaternionicSymmetry.ManifoldTwistorPositiveRicciInput
import QuaternionicSymmetry.ManifoldTwistorCompactHausdorff

/-! Apply the general positive-anticanonical Fano theorem to the actual
LeBrun complex twistor and the already constructed determinant metric.
No Kählerness of the original retained Hermitian metric is asserted. -/

namespace QuaternionicSymmetry.ManifoldTwistorPositiveAnticanonicalSimplyConnected

open GeneralPositiveAnticanonicalSimplyConnectedSource
open ManifoldTwistorPositiveRicciInput ManifoldTwistorLeBrunComplexAtlas
open ManifoldTwistorLineCoreClasses ManifoldTwistorSphereCore
open ManifoldPositiveQuaternionicKahlerGeometry ManifoldQuaternionicScalarCurvature
open ManifoldPositiveQuaternionicKahlerHomothety ManifoldQuaternionicKSWEq38Input
open HolomorphicLineHermitianMetric
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [T3Space M] [SecondCountableTopology M] [Nonempty M]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [CompactSpace M] [PreconnectedSpace M]

/-- The represented anticanonical core on the selected twistor atlas is
definitionally the generic determinant of the actual complex tangent core. -/
theorem anticanonical_core_eq_generic
    (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
      (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
    (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)
    {n : ℕ} (A : CompatibleComplexAtlas Q D n) :
    letI := A.charts
    letI := A.complexManifold
    anticanonicalLineCore Q D A =
      GeneralPositiveAnticanonicalSimplyConnectedSource.anticanonicalLineCore
        (B := SphereBundleTotal Q) (F := ComplexTwistorModel n) := by
  letI := A.charts
  letI := A.complexManifold
  rfl

/-- A positive Hermitian metric on the actual anticanonical determinant
line yields simple connectedness through Ballmann's general Fano theorem. -/
theorem simplyConnected_of_positive_anticanonical
    (hBallmann : BallmannPositiveAnticanonicalSimplyConnected)
    (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
      (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
    (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)
    {n : ℕ} (A : CompatibleComplexAtlas Q D n) :
    letI := A.charts
    ∀ (m : HermitianLineMetric (anticanonicalLineCore Q D A)),
      m.PositiveChernCurvature → SimplyConnectedSpace (SphereBundleTotal Q) := by
  letI := A.charts
  letI := A.complexManifold
  intro m hm
  exact hBallmann m hm

/-- The normalized positive quaternionic-Kähler twistor is simply
connected, with the actual complex atlas and determinant metric selected
by the existing T1 source. -/
theorem normalized_twistor_simplyConnected
    (hBallmann : BallmannPositiveAnticanonicalSimplyConnected)
    (hT1 : NormalizedPositiveRicciContactExistence)
    (P : CompactConnectedPositiveQuaternionicKahlerGeometry (E := E) (M := M))
    (n : ℕ) (hn : 2 ≤ n) (hDim : Module.finrank ℝ E = 4*n)
    (hScalar : ∀ p y (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target),
      localScalarCurvature P.tangent P.connection p y hy =
        16 * (n : ℝ) * ((n : ℝ) + 2)) :
    SimplyConnectedSpace (SphereBundleTotal P.tangent) := by
  obtain ⟨A,_C,m,hm⟩ := exists_positive_anticanonical
    hT1 P n hn hDim hScalar
  exact simplyConnected_of_positive_anticanonical hBallmann
    P.tangent P.connection A m hm

/-- The same route applies after the already checked positive scalar
normalization of an arbitrary higher-dimensional positive input. -/
theorem exists_rescaled_twistor_simplyConnected
    (hBallmann : BallmannPositiveAnticanonicalSimplyConnected)
    (hT1 : NormalizedPositiveRicciContactExistence)
    (S : QuaternionicStructure E)
    (P : CompactConnectedPositiveQuaternionicKahlerGeometry (E := E) (M := M))
    (heq38 : KSWEq38OnModel (E := E) (M := M))
    (hn : 2 ≤ S.quaternionicDimension) :
    ∃ s : ℝ, ∃ hs : 0 < s,
      SimplyConnectedSpace (SphereBundleTotal (rescaleCompact P s hs).tangent) := by
  obtain ⟨s,hs,A,_C,m,hm⟩ := exists_rescaled_positive_anticanonical
    hT1 S P heq38 hn
  exact ⟨s,hs,simplyConnected_of_positive_anticanonical hBallmann
    (rescaleCompact P s hs).tangent (rescaleCompact P s hs).connection A m hm⟩

end
end QuaternionicSymmetry.ManifoldTwistorPositiveAnticanonicalSimplyConnected
