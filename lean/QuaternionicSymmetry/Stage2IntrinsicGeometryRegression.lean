import QuaternionicSymmetry.Stage2IntrinsicClassification

/-! Regression checks for the dimension-one boundary. These test exact preservation
of the actual metric, connection, and Einstein/Weyl package. They do not claim
that arbitrary four-dimensional quaternionic-Kähler span preservation implies
these additional tensor equations, or supply a concrete model witness. -/
namespace QuaternionicSymmetry.Stage2IntrinsicGeometryRegression

open Stage2IntrinsicGeometry ManifoldPositiveTwistorCompatibleFourGeometry
open ManifoldPositiveQuaternionicKahlerGeometry ManifoldRiemannianIntrinsicSymmetry
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

theorem four_roundtrip
    (P : CompactConnectedPositiveTwistorCompatibleFourGeometry (E := E) (M := M)) :
    toFour (ofFour P) = P := rfl

theorem uniform_four_roundtrip
    (P : CompactConnectedPositiveTwistorGeometry (E := E) (M := M) 1) :
    ofFour (toFour P) = P := by
  cases P
  rfl

theorem four_connection_preserved
    (P : CompactConnectedPositiveTwistorCompatibleFourGeometry (E := E) (M := M)) :
    (ofFour P).connection = P.connection := rfl

theorem four_einstein_preserved
    (P : CompactConnectedPositiveTwistorCompatibleFourGeometry (E := E) (M := M)) :
    (toFour (ofFour P)).einstein = P.einstein := rfl

theorem four_weyl_preserved
    (P : CompactConnectedPositiveTwistorCompatibleFourGeometry (E := E) (M := M)) :
    (toFour (ofFour P)).oppositeWeyl = P.oppositeWeyl := rfl

/-- The final uniform endpoint accepts the original actual four-dimensional
package without changing its metric or imposing higher-dimensional conditions. -/
theorem four_intrinsic_endpoint [T2Space M] [SecondCountableTopology M] [Nonempty M]
    (sources : Stage2IntrinsicSources.Sources)
    (hFour : ManifoldFourDerdzinskiIntrinsicSymmetry.DerdzinskiFourSymmetrySource)
    (P : CompactConnectedPositiveTwistorCompatibleFourGeometry (E := E) (M := M)) :
    IsRiemannianSymmetric P.tangent :=
  Stage2IntrinsicClassification.intrinsicSymmetric_c12 sources hFour (ofFour P)
    (by norm_num)

end
end QuaternionicSymmetry.Stage2IntrinsicGeometryRegression
