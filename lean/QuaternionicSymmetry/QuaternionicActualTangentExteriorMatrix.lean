import QuaternionicSymmetry.QuaternionicActualSpCurvatureCoordinates
import QuaternionicSymmetry.ContinuousMatrixCombinationPairing

/-! The finite formal Sp and scalar matrices evaluated in the actual
curvature two-form algebra represent the corresponding real tangent
curvature blocks entrywise. -/
namespace QuaternionicSymmetry.QuaternionicActualTangentExteriorMatrix
open QuaternionicActualSpCurvatureCoordinates
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

def actualEta (p : M) (y : E) :
    Index (chartStructure Q p) → EvenAlgebra E
  | Sum.inl a => ofTwoForm (spCoefficientPower Q D p y a)
  | Sum.inr i => ofTwoForm (axialCurvaturePower Q D p y i)

theorem actualEta_entries_two (p : M) (y : E) (a : Index (chartStructure Q p)) :
    ((actualEta Q D p y a : EvenAlgebra E) :
      ExteriorAlgebra ℝ (Module.Dual ℝ E)) ∈
        ExteriorAlgebra.exteriorPower ℝ 2 (Module.Dual ℝ E) := by
  cases a with
  | inl a => exact (spCoefficientPower Q D p y a).property
  | inr i => exact (axialCurvaturePower Q D p y i).property

theorem actual_sp_matrixTwoForm (p : M) (y : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ, E) p).target) :
    matrixTwoForm (spMatrix (chartStructure Q p) (actualEta Q D p y))
      (formal_sp_entries_two (chartStructure Q p) (actualEta Q D p y)
        (actualEta_entries_two Q D p y)) =
    (matrixCLM (Module.finBasis ℝ E)).compContinuousAlternatingMap
      (curvatureForm (symplecticConnection Q D p) y) := by
  let S := chartStructure Q p
  have hmatrix : spMatrix S (actualEta Q D p y) =
      combination (QuaternionicTangentFormalMatrix.spMatrix S)
        (fun a => ofTwoForm (spCoefficientPower Q D p y a)) := by
    rw [formal_sp_matrix_eq_combination]
    rfl
  have hform := matrixTwoForm_combination
    (QuaternionicTangentFormalMatrix.spMatrix S)
    (fun a => spCoefficientPower Q D p y a)
  calc
    matrixTwoForm (spMatrix (chartStructure Q p) (actualEta Q D p y))
        (formal_sp_entries_two (chartStructure Q p) (actualEta Q D p y)
          (actualEta_entries_two Q D p y)) =
      matrixTwoForm (combination (QuaternionicTangentFormalMatrix.spMatrix S)
        (fun a => ofTwoForm (spCoefficientPower Q D p y a)))
        (combination_entries_two _ _
          (fun a => (spCoefficientPower Q D p y a).property)) := by
            apply matrixTwoForm_congr
            exact hmatrix
    _ = formCombination (QuaternionicTangentFormalMatrix.spMatrix S)
        (fun a => toContinuous 2 (spCoefficientPower Q D p y a)) := hform
    _ = _ := by
      apply ContinuousAlternatingMap.ext
      intro w
      have hw : w = ![w 0, w 1] := by funext i; fin_cases i <;> rfl
      rw [hw]
      have hsum := congrArg (matrixCLM (Module.finBasis ℝ E))
        (symplecticCurvature_expansion Q D p y (w 0) (w 1) hy)
      change matrixCLM (Module.finBasis ℝ E)
        (∑ a : QuaternionicCurvatureFiniteExpansion.Index S,
          (spCoefficientTwoForm Q D p y a) ![w 0,w 1] •
            (QuaternionicCurvatureFiniteExpansion.operatorBasis S a).val) = _ at hsum
      simp only [map_sum, map_smul] at hsum
      change (∑ a : QuaternionicCurvatureFiniteExpansion.Index S,
        (spCoefficientTwoForm Q D p y a) ![w 0,w 1] •
          QuaternionicTangentFormalMatrix.spMatrix S a) = _ at hsum
      apply Matrix.ext
      intro i j
      have hh := congrArg (fun A : Matrix (MatrixIndex (E := E))
        (MatrixIndex (E := E)) ℝ => A i j) hsum
      simp only [formCombination_apply, spCoefficientPower_toContinuous,
        ContinuousAlternatingMap.sum_apply,
        ContinuousAlternatingMap.smul_apply]
      change (∑ x, QuaternionicTangentFormalMatrix.spMatrix S x i j •
        (spCoefficientTwoForm Q D p y x) ![w 0,w 1]) =
        (matrixCLM (Module.finBasis ℝ E)
          (curvatureForm (symplecticConnection Q D p) y ![w 0,w 1])) i j
      rw [curvatureForm_apply]
      simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul] at hh
      simpa only [mul_comm] using hh

end
end QuaternionicSymmetry.QuaternionicActualTangentExteriorMatrix
