import QuaternionicSymmetry.ManifoldTwistorHorizontalConnection
import QuaternionicSymmetry.ManifoldQuaternionicAdjointOverlap
/-! The connection splitting has the correct affine covariance across
actual adapted quaternionic tangent charts. The transition is the tangent
formula for the rotating S² coordinate in ambient coordinates. -/

namespace QuaternionicSymmetry.ManifoldTwistorHorizontalOverlap
open QuaternionicSymmetry.ManifoldTwistorHorizontalConnection
open QuaternionicSymmetry.ManifoldQuaternionicAdjointConnection
open QuaternionicSymmetry.ManifoldQuaternionicAdjointOverlap
open QuaternionicSymmetry.ManifoldQuaternionicConnection
open QuaternionicSymmetry.ManifoldQuaternionicMetric
open scoped Manifold ContDiff
noncomputable section
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Nontrivial E] [FiniteDimensional ℝ E]
 [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (Q : SmoothQuaternionicHermitianTangent (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
variable (D : CompatibleTangentConnection Q)

private abbrev V := Fin 3 → ℝ

def ambientTransition (p q : M) (y : E) (a : V)
    (uv : E × V) : E × V :=
  (fderiv ℝ (chartTransition (I := 𝓘(ℝ,E)) p q) y uv.1,
   fderiv ℝ (rankThreeGauge Q p q) y uv.1 a +
     rankThreeGauge Q p q y uv.2)

def covariantVertical (p : M) (y : E) (a : V)
    (uv : E × V) : V :=
  uv.2 + inducedForm Q D p y uv.1 a

theorem covariantVertical_overlap (p q : M) (y : E) (a : V)
    (uv : E × V)
    (hy : y ∈ chartOverlap (I := 𝓘(ℝ,E)) p q) :
    covariantVertical Q D q (chartTransition (I := 𝓘(ℝ,E)) p q y)
      (rankThreeGauge Q p q y a)
      (ambientTransition Q p q y a uv) =
        rankThreeGauge Q p q y (covariantVertical Q D p y a uv) := by
  have h := inducedForm_overlap Q D p q y uv.1 a hy (by exact ENat.LEInfty.out)
  dsimp [covariantVertical, ambientTransition]
  rw [map_add]
  rw [h]
  abel
theorem horizontalTransition (p q : M) (y : E) (a : V)
    (u : E) (hy : y ∈ chartOverlap (I := 𝓘(ℝ,E)) p q) :
    (ambientTransition Q p q y a
      (u, -inducedForm Q D p y u a)).2 =
      -inducedForm Q D q (chartTransition (I := 𝓘(ℝ,E)) p q y)
        (fderiv ℝ (chartTransition (I := 𝓘(ℝ,E)) p q) y u)
        (rankThreeGauge Q p q y a) := by
  have h := covariantVertical_overlap Q D p q y a
    (u, -inducedForm Q D p y u a) hy
  simp only [covariantVertical, ambientTransition,
    neg_add_cancel, map_zero] at h
  exact eq_neg_of_add_eq_zero_left h

end
end QuaternionicSymmetry.ManifoldTwistorHorizontalOverlap
