import QuaternionicSymmetry.QuaternionicActualTangentExteriorMatrix
import QuaternionicSymmetry.ManifoldQuaternionicCurvatureProjection

/-! Axial two-form coefficients reconstruct the actual scalar tangent
curvature in a fixed quaternionic frame. -/
namespace QuaternionicSymmetry.QuaternionicActualScalarCurvatureCoordinates
open QuaternionicActualSpCurvatureCoordinates
  QuaternionicCurvatureExteriorCoordinates
  QuaternionicLieAlgebraProjection ManifoldQuaternionicCurvatureProjection
  ManifoldQuaternionicConnectionSplitting
  ManifoldQuaternionicAdjointConnection
  VectorBundleFrameTransitions VectorBundleFrameTransitions.QuaternionicFrameReduction
  ManifoldQuaternionicRankThreeOrthogonal
  QuaternionicTangentFormalMatrix
open scoped Manifold ContDiff Topology
noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]
variable (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
  (I := 𝓘(ℝ, E)) (M := M) (n := ∞))
  (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)

theorem scalarCurvature_expansion (p : M) (y u v : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ, E) p).target) :
    ∑ i : Fin 3,
      (axialCurvatureTwoForm Q D p y i) ![u,v] •
        scalarOperator (chartStructure Q p) i =
      LocalConnection.curvature (scalarConnection Q D p) y u v := by
  let S := chartStructure Q p
  rw [scalarCurvature_eq_projection Q D p y u v hy]
  have hcoord (i : Fin 3) :
      (axialCurvatureTwoForm Q D p y i) ![u,v] =
        (axialProjection (adjointRepresentation S
          (D.curvature Q p y u v))) i := by
    change (axialCoordinate S i)
      (LocalConnectionForms.curvatureForm (D.form p) y ![u,v]) = _
    rw [LocalConnectionForms.curvatureForm_apply]
    rfl
  have hop (i : Fin 3) : scalarOperator S i = quaternionicGenerator S i := by
    have hs : Pi.single i (1 : ℝ) = Pi.basisFun ℝ (Fin 3) i := by
      ext j
      simp [Pi.basisFun_apply]
    change synth S (Pi.single i 1) = _
    rw [hs]
    exact synth_basis S i
  change (∑ i : Fin 3, (axialCurvatureTwoForm Q D p y i) ![u,v] •
    scalarOperator S i) = scalarProjection S (D.curvature Q p y u v)
  simp only [hcoord, hop]
  change (∑ i : Fin 3,
    (axialProjection (adjointRepresentation S
      (D.curvature Q p y u v))) i • quaternionicGenerator S i) =
      synth S (axialProjection (adjointRepresentation S
        (D.curvature Q p y u v)))
  exact (synth_apply S _).symm

end
end QuaternionicSymmetry.QuaternionicActualScalarCurvatureCoordinates
