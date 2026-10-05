import QuaternionicSymmetry.QuaternionicExteriorTraceForms
import QuaternionicSymmetry.ManifoldQuaternionicConnection
import QuaternionicSymmetry.ManifoldQuaternionicAdjointConnection
import QuaternionicSymmetry.QuaternionicLieAlgebraProjection
import QuaternionicSymmetry.LocalConnectionForms

/-! Actual scalar curvature coordinates represented as homogeneous exterior
two-forms through the canonical pairing. -/
namespace QuaternionicSymmetry.QuaternionicCurvatureExteriorCoordinates
open ExteriorContinuousPairing
  ManifoldQuaternionicConnection
  ManifoldQuaternionicAdjointConnection
  QuaternionicLieAlgebraProjection
  LocalConnectionForms DifferentialFormCoefficient
open scoped ContDiff Manifold
noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]
variable (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
  (I := 𝓘(ℝ, E)) (M := M) (n := ∞))
  (D : CompatibleTangentConnection Q)

/-- The linear functional taking the `i`-th scalar quaternionic component
of a real tangent endomorphism. -/
def axialCoordinate (T : QuaternionicStructure E) (i : Fin 3) :
    (E →L[ℝ] E) →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) i).comp
    ((axialProjection).comp (adjointRepresentation T))

/-- A genuine alternating scalar two-form from actual tangent curvature. -/
def axialCurvatureTwoForm (p : M) (y : E) (i : Fin 3) :
    E [⋀^Fin 2]→L[ℝ] ℝ :=
  (axialCoordinate (Q.reduction.Q (achart E p)) i).compContinuousAlternatingMap
    (curvatureForm (D.form p) y)

/-- Its canonical homogeneous exterior representative. -/
def axialCurvaturePower (p : M) (y : E) (i : Fin 3) :
    Power E 2 :=
  (equiv (V := E) 2).symm (axialCurvatureTwoForm Q D p y i)

@[simp] theorem axialCurvaturePower_toContinuous (p : M) (y : E) (i : Fin 3) :
    toContinuous 2 (axialCurvaturePower Q D p y i) =
      axialCurvatureTwoForm Q D p y i :=
  (equiv (V := E) 2).apply_symm_apply _

theorem axialCurvaturePower_apply (p : M) (y u v : E) (i : Fin 3) :
    toContinuous 2 (axialCurvaturePower Q D p y i) ![u,v] =
      (axialProjection (adjointRepresentation
        (Q.reduction.Q (achart E p)) (D.curvature Q p y u v))) i := by
  rw [axialCurvaturePower_toContinuous]
  change (axialCoordinate (Q.reduction.Q (achart E p)) i)
    (curvatureForm (D.form p) y ![u,v]) = _
  rw [curvatureForm_apply]
  rfl

end
end QuaternionicSymmetry.QuaternionicCurvatureExteriorCoordinates
