import QuaternionicSymmetry.QuaternionicInfinitesimalSplitting
import QuaternionicSymmetry.ManifoldQuaternionicAdjointConnection

/-! Bounded linear projections implementing the infinitesimal Sp(n)·Sp(1)
splitting, suitable for smooth connection one-forms. -/
namespace QuaternionicSymmetry.QuaternionicLieAlgebraProjection

open QuaternionicInfinitesimalSplitting ManifoldQuaternionicAdjointConnection
  VectorBundleFrameTransitions.QuaternionicFrameReduction
noncomputable section

def axialLinear : ((Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ)) →ₗ[ℝ] (Fin 3 → ℝ) where
  toFun B := ![B (Pi.basisFun ℝ (Fin 3) 1) 2 / 2,
    B (Pi.basisFun ℝ (Fin 3) 2) 0 / 2, B (Pi.basisFun ℝ (Fin 3) 0) 1 / 2]
  map_add' B C := by ext i; fin_cases i <;> simp [add_div]
  map_smul' c B := by ext i; fin_cases i <;> simp [mul_div_assoc]

def axialProjection : ((Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ)) →L[ℝ] (Fin 3 → ℝ) :=
  axialLinear.toContinuousLinearMap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]

def scalarProjection (S : QuaternionicStructure E) : (E →L[ℝ] E) →L[ℝ] (E →L[ℝ] E) :=
  (synth S).comp (axialProjection.comp (adjointRepresentation S))

def symplecticProjection (S : QuaternionicStructure E) : (E →L[ℝ] E) →L[ℝ] (E →L[ℝ] E) :=
  ContinuousLinearMap.id ℝ (E →L[ℝ] E) - scalarProjection S

theorem scalarProjection_apply (S : QuaternionicStructure E) (A : E →L[ℝ] E) :
    scalarProjection S A = scalarPart S
      (fun i j => adjointRepresentation S A (Pi.basisFun ℝ (Fin 3) j) i) := rfl

theorem symplecticProjection_apply (S : QuaternionicStructure E) (A : E →L[ℝ] E) :
    symplecticProjection S A = symplecticPart S A
      (fun i j => adjointRepresentation S A (Pi.basisFun ℝ (Fin 3) j) i) := rfl

theorem projection_sum (S : QuaternionicStructure E) (A : E →L[ℝ] E) :
    symplecticProjection S A + scalarProjection S A = A := by
  change A - scalarProjection S A + scalarProjection S A = A
  exact sub_add_cancel _ _

end
end QuaternionicSymmetry.QuaternionicLieAlgebraProjection
