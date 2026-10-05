import QuaternionicSymmetry.QuaternionicLineMatrixCoordinates
import QuaternionicSymmetry.QuaternionicCurvatureExteriorCoordinates
import QuaternionicSymmetry.ContinuousEndomorphismMatrix
import QuaternionicSymmetry.ExteriorMatrixTraceBridge

/-! Universal scalar-line curvature matrix as an actual alternating two-form. -/
namespace QuaternionicSymmetry.QuaternionicScalarLineExteriorCurvature
open QuaternionicUniversalEvenTrace QuaternionicExteriorEvenTrace
  ExteriorContinuousPairing ExteriorMatrixWedgeBridge
  QuaternionicCurvatureExteriorCoordinates ContinuousEndomorphismMatrix
  QuaternionicLineMatrixCoordinates EvenForms ContinuousMatrixWedgeEntries
open scoped Quaternion ContDiff Manifold
noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

private abbrev X := ExteriorAlgebra ℝ (Module.Dual ℝ E)

local instance : NormedRing (Matrix (Fin 4) (Fin 4) ℝ) := Matrix.linftyOpNormedRing
local instance : NormedAlgebra ℝ (Matrix (Fin 4) (Fin 4) ℝ) :=
  Matrix.linftyOpNormedAlgebra

omit [FiniteDimensional ℝ E] [Nontrivial E] in
theorem line_entries_two (omegaForms : Fin 3 → Power E 2) (i j : Fin 4) :
    ((lineMatrix (liftTwo omegaForms) i j : EvenAlgebra E) : X (E := E)) ∈
      ExteriorAlgebra.exteriorPower ℝ 2 (Module.Dual ℝ E) := by
  fin_cases i <;> fin_cases j <;>
    simp [lineMatrix, liftTwo, ofTwoForm_coe]

omit [Nontrivial E] in
private theorem eval_of_val_eq (z a : Power E 2)
    (h : (z : X (E := E)) = (a : X (E := E))) (u v : E) :
    toContinuous 2 z ![u,v] = toContinuous 2 a ![u,v] := by
  have hz : z = a := Subtype.ext h
  rw [hz]

omit [Nontrivial E] in
private theorem eval_of_val_eq_neg (z a : Power E 2)
    (h : (z : X (E := E)) = -(a : X (E := E))) (u v : E) :
    toContinuous 2 z ![u,v] = -(toContinuous 2 a ![u,v]) := by
  have hz : z = -a := Subtype.ext h
  rw [hz]
  exact congrArg (fun f : E [⋀^Fin 2]→L[ℝ] ℝ => f ![u,v])
    ((ExteriorContinuousPairing.toContinuousLinear (V := E) 2).map_neg a) |>.trans (by rfl)

omit [Nontrivial E] in
private theorem eval_of_val_eq_zero (z : Power E 2)
    (h : (z : X (E := E)) = 0) (u v : E) :
    toContinuous 2 z ![u,v] = 0 := by
  have hz : z = 0 := Subtype.ext h
  rw [hz, toContinuous_zero]
  rfl

omit [Nontrivial E] in
theorem line_matrixTwoForm_apply (omegaForms : Fin 3 → Power E 2) (u v : E) :
    matrixTwoForm (lineMatrix (liftTwo omegaForms))
      (line_entries_two omegaForms) ![u,v] =
      lineMatrix (fun i => toContinuous 2 (omegaForms i) ![u,v]) := by
  ext i j
  change entry i j (matrixTwoForm (lineMatrix (liftTwo omegaForms))
    (line_entries_two omegaForms)) ![u,v] = _
  rw [matrixTwoForm_entry]
  let z := powerEntry (lineMatrix (liftTwo omegaForms))
    (line_entries_two omegaForms) 1 i j
  change toContinuous 2 z ![u,v] = _
  fin_cases i <;> fin_cases j <;>
    simp only [lineMatrix, Matrix.of_apply]
  all_goals
    first
    | exact eval_of_val_eq_zero z (by simp [z, powerEntry, lineMatrix,
        liftTwo, ofTwoForm_coe]) u v
    | simpa using (eval_of_val_eq z (omegaForms 0)
        (by simp [z, powerEntry, lineMatrix, liftTwo, ofTwoForm_coe]) u v)
    | simpa using (eval_of_val_eq z (omegaForms 1)
        (by simp [z, powerEntry, lineMatrix, liftTwo, ofTwoForm_coe]) u v)
    | simpa using (eval_of_val_eq z (omegaForms 2)
        (by simp [z, powerEntry, lineMatrix, liftTwo, ofTwoForm_coe]) u v)
    | simpa using (eval_of_val_eq_neg z (omegaForms 0)
        (by simp [z, powerEntry, lineMatrix, liftTwo, ofTwoForm_coe]) u v)
    | simpa using (eval_of_val_eq_neg z (omegaForms 1)
        (by simp [z, powerEntry, lineMatrix, liftTwo, ofTwoForm_coe]) u v)
    | simpa using (eval_of_val_eq_neg z (omegaForms 2)
        (by simp [z, powerEntry, lineMatrix, liftTwo, ofTwoForm_coe]) u v)

variable (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
  (I := 𝓘(ℝ, E)) (M := M) (n := ∞))
  (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)

/-- The actual scalar-line representation applied to tangent curvature is
the universal exterior line matrix in the named quaternion basis. -/
theorem scalarLineCurvature_matrixTwoForm (p : M) (y : E) :
    ((matrixCLM (QuaternionAlgebra.basisOneIJK (-1 : ℝ) 0 (-1))).comp
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
  change (matrixCLM (QuaternionAlgebra.basisOneIJK (-1 : ℝ) 0 (-1))
    ((QuaternionicProjectiveStandardLie.scalarLineLie
      (Q.reduction.Q (achart E p)))
      (LocalConnectionForms.curvatureForm (D.form p) y ![w 0,w 1]))) i j = _
  rw [LocalConnectionForms.curvatureForm_apply, matrixCLM_apply]
  change (LinearMap.toMatrix (QuaternionAlgebra.basisOneIJK (-1 : ℝ) 0 (-1))
    (QuaternionAlgebra.basisOneIJK (-1 : ℝ) 0 (-1))
    ((QuaternionicProjectiveStandardLie.scalarLineLie
      (Q.reduction.Q (achart E p)))
      (D.curvature Q p y (w 0) (w 1))).toLinearMap) i j = _
  rw [scalarLineLie_matrix, line_matrixTwoForm_apply]
  congr 1
  funext t
  exact (axialCurvaturePower_apply Q D p y (w 0) (w 1) t).symm

end
end QuaternionicSymmetry.QuaternionicScalarLineExteriorCurvature
