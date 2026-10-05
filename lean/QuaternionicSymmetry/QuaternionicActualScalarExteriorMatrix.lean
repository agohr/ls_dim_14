import QuaternionicSymmetry.QuaternionicActualScalarCurvatureCoordinates

/-! The formal scalar quaternionic matrix in actual exterior coordinates
is exactly the scalar part of tangent curvature. -/
namespace QuaternionicSymmetry.QuaternionicActualScalarExteriorMatrix
open QuaternionicActualSpCurvatureCoordinates
  QuaternionicActualScalarCurvatureCoordinates
  QuaternionicActualTangentExteriorMatrix
  QuaternionicCurvatureExteriorCoordinates
  QuaternionicTangentFormalMatrix QuaternionicTangentUniversalSpecialization
  QuaternionicExteriorEvenTrace EvenForms ExteriorContinuousPairing
  HomogeneousMatrixCombinations ContinuousMatrixCombinationPairing
  ContinuousMatrixExteriorEquivalence
  ExteriorMatrixWedgeBridge ContinuousEndomorphismMatrix
  LocalConnectionForms ManifoldQuaternionicConnectionSplitting
  RealifiedTracePolynomial
open scoped Manifold ContDiff Topology
noncomputable section
set_option maxHeartbeats 1000000

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]
variable (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
  (I := 𝓘(ℝ, E)) (M := M) (n := ∞))
  (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)

theorem actual_scalar_matrixTwoForm (p : M) (y : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ, E) p).target) :
    matrixTwoForm (scalarMatrix (chartStructure Q p) (actualEta Q D p y))
      (formal_scalar_entries_two (chartStructure Q p) (actualEta Q D p y)
        (actualEta_entries_two Q D p y)) =
    (matrixCLM (Module.finBasis ℝ E)).compContinuousAlternatingMap
      (curvatureForm (scalarConnection Q D p) y) := by
  let S := chartStructure Q p
  have hmatrix : scalarMatrix S (actualEta Q D p y) =
      combination (QuaternionicTangentFormalMatrix.scalarMatrix S)
        (fun i => ofTwoForm (axialCurvaturePower Q D p y i)) := by
    rw [formal_scalar_matrix_eq_combination]
    rfl
  have hform := matrixTwoForm_combination
    (QuaternionicTangentFormalMatrix.scalarMatrix S)
    (fun i => axialCurvaturePower Q D p y i)
  calc
    matrixTwoForm (scalarMatrix (chartStructure Q p) (actualEta Q D p y))
        (formal_scalar_entries_two (chartStructure Q p) (actualEta Q D p y)
          (actualEta_entries_two Q D p y)) =
      matrixTwoForm (combination (QuaternionicTangentFormalMatrix.scalarMatrix S)
        (fun i => ofTwoForm (axialCurvaturePower Q D p y i)))
        (combination_entries_two _ _
          (fun i => (axialCurvaturePower Q D p y i).property)) := by
            apply matrixTwoForm_congr
            exact hmatrix
    _ = formCombination (QuaternionicTangentFormalMatrix.scalarMatrix S)
        (fun i => toContinuous 2 (axialCurvaturePower Q D p y i)) := hform
    _ = _ := by
      apply ContinuousAlternatingMap.ext
      intro w
      have hw : w = ![w 0, w 1] := by funext i; fin_cases i <;> rfl
      rw [hw]
      have hsum := congrArg (matrixCLM (Module.finBasis ℝ E))
        (scalarCurvature_expansion Q D p y (w 0) (w 1) hy)
      change matrixCLM (Module.finBasis ℝ E)
        (∑ i : Fin 3,
          (axialCurvatureTwoForm Q D p y i) ![w 0,w 1] •
            scalarOperator S i) = _ at hsum
      simp only [map_sum, map_smul] at hsum
      change (∑ i : Fin 3,
        (axialCurvatureTwoForm Q D p y i) ![w 0,w 1] •
          QuaternionicTangentFormalMatrix.scalarMatrix S i) = _ at hsum
      apply Matrix.ext
      intro i j
      have hh := congrArg (fun A : Matrix (MatrixIndex (E := E))
        (MatrixIndex (E := E)) ℝ => A i j) hsum
      simp only [formCombination_apply, axialCurvaturePower_toContinuous,
        ContinuousAlternatingMap.sum_apply,
        ContinuousAlternatingMap.smul_apply]
      change (∑ x, QuaternionicTangentFormalMatrix.scalarMatrix S x i j •
        (axialCurvatureTwoForm Q D p y x) ![w 0,w 1]) =
        (matrixCLM (Module.finBasis ℝ E)
          (curvatureForm (scalarConnection Q D p) y ![w 0,w 1])) i j
      rw [curvatureForm_apply]
      simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul] at hh
      simpa only [mul_comm] using hh

end
end QuaternionicSymmetry.QuaternionicActualScalarExteriorMatrix
