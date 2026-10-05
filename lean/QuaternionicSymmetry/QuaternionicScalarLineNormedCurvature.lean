import QuaternionicSymmetry.QuaternionicNormedLineBasis
import QuaternionicSymmetry.QuaternionicScalarLineExteriorCurvature
import QuaternionicSymmetry.ContinuousEndomorphismMatrix
import QuaternionicSymmetry.ExteriorMatrixTraceBridge

/-! Actual scalar-line curvature in the normed-space quaternion basis. -/
namespace QuaternionicSymmetry.QuaternionicScalarLineNormedCurvature
open QuaternionicNormedLineBasis QuaternionicScalarLineExteriorCurvature
  QuaternionicCurvatureExteriorCoordinates QuaternionicUniversalEvenTrace
  QuaternionicExteriorEvenTrace ExteriorMatrixWedgeBridge
  ContinuousEndomorphismMatrix ManifoldQuaternionicAdjointConnection
open scoped Quaternion ContDiff Manifold
noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]
local instance : NormedRing (Matrix (Fin 4) (Fin 4) ℝ) := Matrix.linftyOpNormedRing
local instance : NormedAlgebra ℝ (Matrix (Fin 4) (Fin 4) ℝ) :=
  Matrix.linftyOpNormedAlgebra
variable (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
  (I := 𝓘(ℝ, E)) (M := M) (n := ∞))
  (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)

/-- The actual scalar-line curvature two-form is the universal line matrix
in the real basis coherent with the continuous endomorphism module. -/
theorem scalarLineCurvature_matrixTwoForm (p : M) (y : E) :
    ((matrixCLM lineBasis).comp
      (QuaternionicProjectiveStandardLie.scalarLineLie
        (Q.reduction.Q (achart E p)))).compContinuousAlternatingMap
        (LocalConnectionForms.curvatureForm (D.form p) y) =
    matrixTwoForm
      (lineMatrix (liftTwo (fun i => axialCurvaturePower Q D p y i)))
      (line_entries_two (fun i => axialCurvaturePower Q D p y i)) := by
  apply ContinuousAlternatingMap.ext
  intro w
  have hw : w = ![w 0, w 1] := by
    funext t
    fin_cases t <;> rfl
  rw [hw]
  ext i j
  change (matrixCLM lineBasis
    ((QuaternionicProjectiveStandardLie.scalarLineLie
      (Q.reduction.Q (achart E p)))
      (LocalConnectionForms.curvatureForm (D.form p) y ![w 0,w 1]))) i j = _
  rw [LocalConnectionForms.curvatureForm_apply, matrixCLM_apply]
  change (LinearMap.toMatrix lineBasis lineBasis
    ((QuaternionicProjectiveStandardLie.scalarLineLie
      (Q.reduction.Q (achart E p)))
      (D.curvature Q p y (w 0) (w 1))).toLinearMap) i j = _
  rw [QuaternionicNormedLineBasis.scalarLineLie_matrix,
    line_matrixTwoForm_apply]
  congr 1
  funext t
  exact (axialCurvaturePower_apply Q D p y (w 0) (w 1) t).symm

end
end QuaternionicSymmetry.QuaternionicScalarLineNormedCurvature
