import QuaternionicSymmetry.QuaternionicManifoldFixedConnectionOverlap
import QuaternionicSymmetry.QuaternionicProjectiveProductMaurer

/-! The fixed tangent overlap is literally the scalar-times-symplectic
product on each refined quaternionic lift neighborhood. -/

namespace QuaternionicSymmetry.QuaternionicManifoldProductGaugeIdentity

open scoped Manifold ContDiff Quaternion
open QuaternionicManifoldLocalScalarLifts
open QuaternionicManifoldSmoothProductLifts
open QuaternionicProjectiveProductMaurer
open QuaternionicManifoldFixedConnectionOverlap
open VectorBundleFrameTransitions

noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

variable (S : QuaternionicStructure E)
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ, E)) (M := M) (n := ∞))

theorem fixedTransition_eq_product (i j : atlas E M) (q : unitary ℍ)
    (x : M) (hx : x ∈ liftNeighborhood Q i j q) :
    fixedTransitionCLM S Q i j x =
      scalarActionLinear S (scalarLiftRaw Q i j q x) *
        symplecticFactorOperator S Q i j q x := by
  let r := scalarLiftRaw Q i j q x
  have hr : Quaternion.normSq r = 1 :=
    (scalarLiftRaw_valid Q S i j q x hx).1
  have hmul : r * star r = 1 := by
    rw [Quaternion.self_mul_star, hr]
    rfl
  change fixedTransitionCLM S Q i j x =
    scalarActionLinear S r *
      (scalarActionLinear S (star r) * fixedTransitionCLM S Q i j x)
  rw [← mul_assoc, ← scalarAction_mul, hmul, scalarAction_one, one_mul]

theorem fixedGauge_eq_product (p q : M) (lift : unitary ℍ)
    (y : E)
    (hy : (extChartAt 𝓘(ℝ, E) p).symm y ∈
      liftNeighborhood Q (achart E p) (achart E q) lift) :
    fixedGauge S Q p q y =
      scalarActionLinear S
        (scalarLiftRaw Q (achart E p) (achart E q) lift
          ((extChartAt 𝓘(ℝ, E) p).symm y)) *
      symplecticFactorOperator S Q (achart E p) (achart E q) lift
        ((extChartAt 𝓘(ℝ, E) p).symm y) := by
  rw [fixedGauge_eq_transition]
  exact fixedTransition_eq_product S Q _ _ lift _ hy

end
end QuaternionicSymmetry.QuaternionicManifoldProductGaugeIdentity
