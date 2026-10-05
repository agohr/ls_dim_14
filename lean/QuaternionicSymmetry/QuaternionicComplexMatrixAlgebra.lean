import QuaternionicSymmetry.QuaternionicOperatorMatrixTrace
import Mathlib.Algebra.Algebra.Subalgebra.Centralizer

/-! Multiplicative complex matrix coordinates for the full algebra of
endomorphisms commuting with I. Products of skew quaternionic operators
need not be skew, so the full algebra is used for curvature trace powers. -/
namespace QuaternionicSymmetry.QuaternionicComplexMatrixAlgebra
open QuaternionicOperatorMatrix QuaternionicOperatorMatrixLinear
open QuaternionicOperatorMatrixTrace QuaternionicMatrixCoordinates QuaternionicMatrixModel
open scoped Matrix
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] (S : QuaternionicStructure E)
local instance : NormedSpace ℝ E := inferInstance

theorem realMatrixAction_mul {n : ℕ}
    (A B : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ) (v : V n) :
    realMatrixAction (A * B) v = realMatrixAction A (realMatrixAction B v) := by
  apply (WithLp.equiv 2 _).injective
  change (realMatrixAction (A * B) v).ofLp =
    (realMatrixAction A (realMatrixAction B v)).ofLp
  simp only [realMatrixAction_apply, Matrix.mulVec_mulVec]

theorem operatorMatrix_mul (A B : E →ₗ[ℝ] E)
    (hA : ∀ v, A (S.I v) = S.I (A v))
    (hB : ∀ v, B (S.I v) = S.I (B v))
    (hAB : ∀ v, (A * B) (S.I v) = S.I ((A * B) v)) :
    operatorMatrix S (A * B) hAB = operatorMatrix S A hA * operatorMatrix S B hB := by
  apply Matrix.toEuclideanLin.injective
  apply LinearMap.ext
  intro v
  change realMatrixAction (operatorMatrix S (A * B) hAB) v =
    realMatrixAction (operatorMatrix S A hA * operatorMatrix S B hB) v
  rw [realMatrixAction_mul]
  simp only [operatorMatrix, matrixEnd_action]
  simp [modelEnd]

def complexLinearAlgebra : Subalgebra ℝ (E →L[ℝ] E) :=
  Subalgebra.centralizer ℝ {S.I.toContinuousLinearMap}

theorem mem_complexLinearAlgebra (A : E →L[ℝ] E) :
    A ∈ complexLinearAlgebra S ↔ ∀ v, A (S.I v) = S.I (A v) := by
  simp only [complexLinearAlgebra, Subalgebra.mem_centralizer_iff,
    Set.mem_singleton_iff, forall_eq]
  constructor
  · intro h v
    exact (congrArg (fun T : E →L[ℝ] E => T v) h).symm
  · intro h
    exact ContinuousLinearMap.ext (fun v => (h v).symm)

def matrixLinear : complexLinearAlgebra S →ₗ[ℝ]
    Matrix (Fin S.quaternionicDimension ⊕ Fin S.quaternionicDimension)
      (Fin S.quaternionicDimension ⊕ Fin S.quaternionicDimension) ℂ where
  toFun A := operatorMatrix S A.val.toLinearMap
    ((mem_complexLinearAlgebra S A.val).mp A.property)
  map_add' A B := operatorMatrix_add S A.val.toLinearMap B.val.toLinearMap _ _ _
  map_smul' r A := operatorMatrix_smul S r A.val.toLinearMap _ _

theorem matrixLinear_mul (A B : complexLinearAlgebra S) :
    matrixLinear S (A * B) = matrixLinear S A * matrixLinear S B :=
  operatorMatrix_mul S A.val.toLinearMap B.val.toLinearMap
    ((mem_complexLinearAlgebra S A.val).mp A.property)
    ((mem_complexLinearAlgebra S B.val).mp B.property)
    ((mem_complexLinearAlgebra S (A * B).val).mp (A * B).property)


theorem matrixLinear_pow_succ (A : complexLinearAlgebra S) (k : ℕ) :
    matrixLinear S (A ^ (k + 1)) = matrixLinear S A ^ (k + 1) := by
  induction k with
  | zero => simp only [Nat.zero_add, pow_one]
  | succ k ih =>
      rw [pow_succ, matrixLinear_mul, ih]
      simp only [pow_succ]

theorem matrixLinear_trace (A : complexLinearAlgebra S) :
    LocalEndomorphismTrace.traceCLM A.val = 2 * (matrixLinear S A).trace.re :=
  operatorMatrix_trace S A.val.toLinearMap
    ((mem_complexLinearAlgebra S A.val).mp A.property)


local instance : NormedRing (Matrix
    (Fin S.quaternionicDimension ⊕ Fin S.quaternionicDimension)
    (Fin S.quaternionicDimension ⊕ Fin S.quaternionicDimension) ℂ) :=
  Matrix.linftyOpNormedRing
local instance : NormedAlgebra ℝ (Matrix
    (Fin S.quaternionicDimension ⊕ Fin S.quaternionicDimension)
    (Fin S.quaternionicDimension ⊕ Fin S.quaternionicDimension) ℂ) :=
  Matrix.linftyOpNormedAlgebra

def matrixCLM : complexLinearAlgebra S →L[ℝ]
    Matrix (Fin S.quaternionicDimension ⊕ Fin S.quaternionicDimension)
      (Fin S.quaternionicDimension ⊕ Fin S.quaternionicDimension) ℂ :=
  (matrixLinear S).toContinuousLinearMap

theorem matrixCLM_mul (A B : complexLinearAlgebra S) :
    matrixCLM S (A * B) = matrixCLM S A * matrixCLM S B := matrixLinear_mul S A B

theorem matrixCLM_trace (A : complexLinearAlgebra S) :
    LocalEndomorphismTrace.traceCLM A.val = 2 * (matrixCLM S A).trace.re :=
  matrixLinear_trace S A

end
end QuaternionicSymmetry.QuaternionicComplexMatrixAlgebra
