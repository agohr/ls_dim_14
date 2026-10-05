import QuaternionicSymmetry.QuaternionicAdjointCurvatureMatrix
import QuaternionicSymmetry.QuaternionicCurvatureExteriorCoordinates
import QuaternionicSymmetry.ContinuousEndomorphismMatrix
import QuaternionicSymmetry.ExteriorMatrixTraceBridge

/-! The actual induced rank-three curvature two-form in universal exterior
matrix coordinates. -/
namespace QuaternionicSymmetry.QuaternionicAdjointExteriorCurvature
open QuaternionicUniversalEvenTrace QuaternionicExteriorEvenTrace
  ExteriorContinuousPairing ExteriorMatrixWedgeBridge
  QuaternionicCurvatureExteriorCoordinates ContinuousEndomorphismMatrix
  QuaternionicAdjointCurvatureMatrix EvenForms
  ContinuousMatrixWedgeEntries
  ManifoldQuaternionicAdjointConnection LocalConnectionForms
open scoped ContDiff Manifold
noncomputable section
set_option maxHeartbeats 1000000

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

private abbrev X := ExteriorAlgebra ℝ (Module.Dual ℝ E)

local instance : NormedRing (Matrix (Fin 3) (Fin 3) ℝ) := Matrix.linftyOpNormedRing
local instance : NormedAlgebra ℝ (Matrix (Fin 3) (Fin 3) ℝ) :=
  Matrix.linftyOpNormedAlgebra

omit [FiniteDimensional ℝ E] [Nontrivial E] in
private theorem even_two_coe : ((2 : EvenAlgebra E) : X (E := E)) = 2 := by
  exact map_ofNat (Subalgebra.val (evenSubalgebra ℝ (Module.Dual ℝ E))) 2

omit [FiniteDimensional ℝ E] [Nontrivial E] in
theorem adjoint_entries_two (omegaForms : Fin 3 → Power E 2) (i j : Fin 3) :
    ((adjointMatrix (liftTwo omegaForms) i j : EvenAlgebra E) : X (E := E)) ∈
      ExteriorAlgebra.exteriorPower ℝ 2 (Module.Dual ℝ E) := by
  have htwo (k : Fin 3) :
      (2 : X (E := E)) * (omegaForms k).val ∈
        ExteriorAlgebra.exteriorPower ℝ 2 (Module.Dual ℝ E) := by
    have h := (ExteriorAlgebra.exteriorPower ℝ 2 (Module.Dual ℝ E)).smul_mem
      (2 : ℝ) (omegaForms k).property
    simpa only [Algebra.smul_def, map_ofNat] using h
  fin_cases i <;> fin_cases j <;>
    simp [adjointMatrix, liftTwo, ofTwoForm_coe]
  all_goals first | exact htwo 0 | exact htwo 1 | exact htwo 2

omit [Nontrivial E] in
private theorem eval_of_val_eq_smul (z a : Power E 2) (r : ℝ)
    (h : (z : X (E := E)) = r • (a : X (E := E))) (u v : E) :
    toContinuous 2 z ![u,v] = r * toContinuous 2 a ![u,v] := by
  have hz : z = r • a := Subtype.ext h
  rw [hz, toContinuous_smul]
  simp

omit [Nontrivial E] in
private theorem eval_of_val_eq_zero (z : Power E 2)
    (h : (z : X (E := E)) = 0) (u v : E) :
    toContinuous 2 z ![u,v] = 0 := by
  have hz : z = 0 := Subtype.ext h
  rw [hz, toContinuous_zero]
  rfl

omit [Nontrivial E] in
theorem adjoint_matrixTwoForm_apply (omegaForms : Fin 3 → Power E 2)
    (u v : E) :
    matrixTwoForm (adjointMatrix (liftTwo omegaForms)) (adjoint_entries_two omegaForms) ![u,v] =
      adjointMatrix (fun i => toContinuous 2 (omegaForms i) ![u,v]) := by
  ext i j
  change entry i j (matrixTwoForm (adjointMatrix (liftTwo omegaForms))
    (adjoint_entries_two omegaForms)) ![u,v] = _
  rw [matrixTwoForm_entry]
  let z := powerEntry (adjointMatrix (liftTwo omegaForms))
    (adjoint_entries_two omegaForms) 1 i j
  change toContinuous 2 z ![u,v] = _
  fin_cases i <;> fin_cases j <;>
    simp only [adjointMatrix, Matrix.of_apply]
  all_goals
    first
    | exact eval_of_val_eq_zero z (by simp [z, powerEntry, adjointMatrix,
        liftTwo, ofTwoForm_coe]) u v
    | simpa [mul_assoc] using (eval_of_val_eq_smul z (omegaForms 0) 2
        (by simp [z, powerEntry, adjointMatrix, liftTwo, ofTwoForm_coe,
          Algebra.smul_def, map_ofNat, even_two_coe]) u v)
    | simpa [mul_assoc] using (eval_of_val_eq_smul z (omegaForms 1) 2
        (by simp [z, powerEntry, adjointMatrix, liftTwo, ofTwoForm_coe,
          Algebra.smul_def, map_ofNat, even_two_coe]) u v)
    | simpa [mul_assoc] using (eval_of_val_eq_smul z (omegaForms 2) 2
        (by simp [z, powerEntry, adjointMatrix, liftTwo, ofTwoForm_coe,
          Algebra.smul_def, map_ofNat, even_two_coe]) u v)
    | simpa [neg_mul, mul_assoc] using (eval_of_val_eq_smul z (omegaForms 0) (-2)
        (by simp [z, powerEntry, adjointMatrix, liftTwo, ofTwoForm_coe,
          Algebra.smul_def, map_ofNat, even_two_coe]) u v)
    | simpa [neg_mul, mul_assoc] using (eval_of_val_eq_smul z (omegaForms 1) (-2)
        (by simp [z, powerEntry, adjointMatrix, liftTwo, ofTwoForm_coe,
          Algebra.smul_def, map_ofNat, even_two_coe]) u v)
    | simpa [neg_mul, mul_assoc] using (eval_of_val_eq_smul z (omegaForms 2) (-2)
        (by simp [z, powerEntry, adjointMatrix, liftTwo, ofTwoForm_coe,
          Algebra.smul_def, map_ofNat, even_two_coe]) u v)

variable (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
  (I := 𝓘(ℝ, E)) (M := M) (n := ∞))
  (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)

/-- Actual induced rank-three curvature, transported through its fixed real
basis, is exactly the universal exterior adjoint matrix of the axial
curvature two-form. -/
theorem inducedCurvature_matrixTwoForm (p : M) (y : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ, E) p).target) :
    (matrixCLM (Pi.basisFun ℝ (Fin 3))).compContinuousAlternatingMap
      (curvatureForm (inducedForm Q D p) y) =
    matrixTwoForm
      (adjointMatrix (liftTwo (fun i => axialCurvaturePower Q D p y i)))
      (adjoint_entries_two (fun i => axialCurvaturePower Q D p y i)) := by
  apply ContinuousAlternatingMap.ext
  intro w
  have hw : w = ![w 0, w 1] := by
    funext t
    fin_cases t <;> rfl
  rw [hw]
  ext i j
  change (matrixCLM (Pi.basisFun ℝ (Fin 3))
      (curvatureForm (inducedForm Q D p) y ![w 0,w 1])) i j = _
  rw [curvatureForm_apply, matrixCLM_apply, adjoint_matrixTwoForm_apply]
  change (LinearMap.toMatrix (Pi.basisFun ℝ (Fin 3)) (Pi.basisFun ℝ (Fin 3))
      (inducedCurvature Q D p y (w 0) (w 1)).toLinearMap) i j = _
  rw [inducedCurvature_matrix Q D p y (w 0) (w 1) hy]
  congr 1
  funext t
  exact (axialCurvaturePower_apply Q D p y (w 0) (w 1) t).symm

end
end QuaternionicSymmetry.QuaternionicAdjointExteriorCurvature
