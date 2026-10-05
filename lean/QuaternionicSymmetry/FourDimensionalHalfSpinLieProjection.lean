import QuaternionicSymmetry.FourDimensionalHalfSpinSmoothLocalFactors
import QuaternionicSymmetry.QuaternionicLieAlgebraProjection
import QuaternionicSymmetry.QuaternionicManifoldProjectiveStandardConnection

/-! The left half-spin Lie-algebra component of an actual four-dimensional
adapted metric connection is extracted by the previously checked adjoint
rank-three connection and axial projection.  This is an independent
bounded-linear projection, not a connection transported across Hopf. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinLieProjection

open scoped Quaternion ContDiff Manifold
open QuaternionicLieAlgebraProjection
  QuaternionicUnitScalarIsometries
  QuaternionicProjectiveStandardHilbertStructure
  ManifoldQuaternionicConnection
  ManifoldQuaternionicAdjointConnection
  QuaternionicManifoldProjectiveStandardConnection
  VectorBundleFrameTransitions.QuaternionicFrameReduction

noncomputable section

private def pureScalarLinear : (Fin 3 → ℝ) →ₗ[ℝ] ℍ where
  toFun := pureScalar
  map_add' a b := by ext <;> simp [pureScalar]
  map_smul' c a := by ext <;> simp [pureScalar]

/-- The skew left-spinor coefficient of a real tangent endomorphism. -/
def leftLieProjection : (ℍ →L[ℝ] ℍ) →L[ℝ] ℍ :=
  pureScalarLinear.toContinuousLinearMap.comp
    (axialProjection.comp (adjointRepresentation leftLineStructure))

theorem leftLieProjection_re (A : ℍ →L[ℝ] ℍ) :
    (leftLieProjection A).re = 0 := by
  rfl

/-- The scalar component of the actual infinitesimal splitting acts on the
left spinor line by the extracted imaginary quaternion. -/
theorem scalarProjection_apply_leftLie (A : ℍ →L[ℝ] ℍ) (v : ℍ) :
    scalarProjection leftLineStructure A v = leftLieProjection A * v := by
  change (synth leftLineStructure
      (axialProjection (adjointRepresentation leftLineStructure A))) v =
    pureScalar (axialProjection (adjointRepresentation leftLineStructure A)) * v
  rw [← action_pureScalar]
  exact QuaternionicLeftLineAction.action_eq_mul _ _

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℍ M]
  [IsManifold 𝓘(ℝ, ℍ) ∞ M]
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ, ℍ)) (M := M) (n := ∞))
  (D : CompatibleTangentConnection Q)

/-- Independent local left-spinor connection one-form from the actual
adapted tangent metric connection. -/
def leftSpinorForm (p : M) (y : ℍ) : ℍ →L[ℝ] ℍ :=
  leftLieProjection.comp
    ((fixedTangentConjugation leftLineStructure Q p).comp (D.form p y))

theorem leftSpinorForm_apply (p : M) (y u : ℍ) :
    leftSpinorForm Q D p y u =
      leftLieProjection (fixedTangentConjugation leftLineStructure Q p
        (D.form p y u)) := rfl

theorem leftSpinorForm_re (p : M) (y u : ℍ) :
    (leftSpinorForm Q D p y u).re = 0 :=
  leftLieProjection_re _

theorem leftSpinorForm_smooth (p : M) :
    ContDiffOn ℝ ∞ (leftSpinorForm Q D p)
      (extChartAt 𝓘(ℝ, ℍ) p).target := by
  let C := fixedTangentConjugation leftLineStructure Q p
  let LC : (ℍ →L[ℝ] ℍ) →L[ℝ] ℍ := leftLieProjection
  have hC : ContDiffOn ℝ ∞
      (fun y : ℍ => C.comp (D.form p y))
      (extChartAt 𝓘(ℝ, ℍ) p).target :=
    contDiffOn_const.clm_comp (D.smooth_form p)
  exact contDiffOn_const.clm_comp hC

end
end QuaternionicSymmetry.FourDimensionalHalfSpinLieProjection
