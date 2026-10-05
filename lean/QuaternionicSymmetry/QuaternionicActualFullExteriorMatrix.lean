import QuaternionicSymmetry.QuaternionicActualScalarExteriorMatrix
import QuaternionicSymmetry.ManifoldQuaternionicCurvatureSplitting

/-! Exact all-rank formal full tangent matrix realization for actual
compatible quaternionic curvature on each valid chart. -/
namespace QuaternionicSymmetry.QuaternionicActualFullExteriorMatrix
open QuaternionicActualSpCurvatureCoordinates
  QuaternionicActualTangentExteriorMatrix
  QuaternionicActualScalarExteriorMatrix
  QuaternionicTangentUniversalSpecialization
  HomogeneousMatrixCombinations ContinuousMatrixExteriorEquivalence
  QuaternionicExteriorEvenTrace ExteriorMatrixWedgeBridge
  ContinuousEndomorphismMatrix LocalConnectionForms
  ManifoldQuaternionicConnectionSplitting
  ManifoldQuaternionicCurvatureSplitting
open scoped Manifold ContDiff Topology
noncomputable section
set_option maxHeartbeats 1000000

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]
variable (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
  (I := 𝓘(ℝ, E)) (M := M) (n := ∞))
  (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)

theorem actual_tangent_matrixTwoForm (p : M) (y : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ, E) p).target) :
    matrixTwoForm
      (spMatrix (chartStructure Q p) (actualEta Q D p y) +
        scalarMatrix (chartStructure Q p) (actualEta Q D p y))
      (entries_two_add _ _
        (formal_sp_entries_two (chartStructure Q p) (actualEta Q D p y)
          (actualEta_entries_two Q D p y))
        (formal_scalar_entries_two (chartStructure Q p) (actualEta Q D p y)
          (actualEta_entries_two Q D p y))) =
    (matrixCLM (Module.finBasis ℝ E)).compContinuousAlternatingMap
      (curvatureForm (D.form p) y) := by
  let S := chartStructure Q p
  let η := actualEta Q D p y
  let hsp := formal_sp_entries_two S η (actualEta_entries_two Q D p y)
  let hsc := formal_scalar_entries_two S η (actualEta_entries_two Q D p y)
  calc
    matrixTwoForm (spMatrix S η + scalarMatrix S η)
        (entries_two_add _ _ hsp hsc) =
      matrixTwoForm (spMatrix S η) hsp +
        matrixTwoForm (scalarMatrix S η) hsc :=
      matrixTwoForm_add _ _ hsp hsc
    _ = (matrixCLM (Module.finBasis ℝ E)).compContinuousAlternatingMap
          (curvatureForm (symplecticConnection Q D p) y) +
        (matrixCLM (Module.finBasis ℝ E)).compContinuousAlternatingMap
          (curvatureForm (scalarConnection Q D p) y) := by
            rw [actual_sp_matrixTwoForm Q D p y hy,
              actual_scalar_matrixTwoForm Q D p y hy]
    _ = (matrixCLM (Module.finBasis ℝ E)).compContinuousAlternatingMap
          (curvatureForm (D.form p) y) := by
            apply ContinuousAlternatingMap.ext
            intro w
            have hw : w = ![w 0, w 1] := by funext i; fin_cases i <;> rfl
            rw [hw]
            have hsplit := congrArg (matrixCLM (Module.finBasis ℝ E))
              (congrArg (fun T : LocalConnection.Bilinear (E := E)
                (A := E →L[ℝ] E) => T (w 0) (w 1))
                (curvature_split Q D p y hy))
            change matrixCLM (Module.finBasis ℝ E)
              (D.curvature Q p y (w 0) (w 1)) = _ at hsplit
            simp only [ContinuousLinearMap.add_apply, map_add] at hsplit
            change matrixCLM (Module.finBasis ℝ E)
                (curvatureForm (symplecticConnection Q D p) y ![w 0,w 1]) +
              matrixCLM (Module.finBasis ℝ E)
                (curvatureForm (scalarConnection Q D p) y ![w 0,w 1]) =
              matrixCLM (Module.finBasis ℝ E)
                (curvatureForm (D.form p) y ![w 0,w 1])
            rw [curvatureForm_apply, curvatureForm_apply, curvatureForm_apply]
            simpa only [Matrix.cons_val_zero, Matrix.cons_val_one] using hsplit.symm

end
end QuaternionicSymmetry.QuaternionicActualFullExteriorMatrix
