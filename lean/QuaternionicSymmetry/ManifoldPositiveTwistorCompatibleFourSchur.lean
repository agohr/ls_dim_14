import QuaternionicSymmetry.ManifoldQuaternionicEinsteinSchurFromEquation
import QuaternionicSymmetry.ManifoldPositiveTwistorCompatibleFourNormalize

/-! The four-dimensional Einstein equation itself supplies Schur's
hypothesis. No quaternionic-dimension-two Eq38 identity is used. -/
namespace QuaternionicSymmetry.ManifoldPositiveTwistorCompatibleFourSchur

open ManifoldPositiveTwistorCompatibleFourGeometry
open ManifoldPositiveTwistorCompatibleFourHomothety
open ManifoldPositiveTwistorCompatibleFourNormalize
open ManifoldQuaternionicEinsteinSchurFromEquation
open ManifoldQuaternionicScalarCurvature
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

theorem localEinsteinEquation
    (P : PositiveTwistorCompatibleFourGeometry (E := E) (M := M)) :
    LocalEinsteinEquation P.tangent P.connection := by
  intro p y hy v w
  rw [P.realDimension]
  exact P.einstein p y hy v w

theorem preferredScalarCurvature_eq_of_connected
    (P : CompactConnectedPositiveTwistorCompatibleFourGeometry
      (E := E) (M := M)) (x y : M) :
    preferredScalarCurvature P.tangent P.connection x =
      preferredScalarCurvature P.tangent P.connection y := by
  obtain ⟨c, hc⟩ := exists_ne (0 : E)
  exact preferredScalarCurvature_eq_of_preconnected_fromEquation
    P.tangent P.connection
    (localEinsteinEquation P.toPositiveTwistorCompatibleFourGeometry)
    (by rw [P.realDimension]; omega) P.connected c hc x y

theorem localScalarCurvature_eq_at
    (P : CompactConnectedPositiveTwistorCompatibleFourGeometry
      (E := E) (M := M)) (x : M)
    (p : M) (y : E) (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target) :
    localScalarCurvature P.tangent P.connection p y hy =
      preferredScalarCurvature P.tangent P.connection x := by
  let z := (extChartAt 𝓘(ℝ,E) p).symm y
  have hz := (extChartAt 𝓘(ℝ,E) p).map_target hy
  have hlocal := localScalarCurvature_eq_preferred P.tangent P.connection
    p z hz (show (2 : WithTop ℕ∞) ≤ ∞ from ENat.LEInfty.out)
  have hlocal' : localScalarCurvature P.tangent P.connection p y hy =
      preferredScalarCurvature P.tangent P.connection z := by
    simpa only [z, (extChartAt 𝓘(ℝ,E) p).right_inv hy] using hlocal
  exact hlocal'.trans (preferredScalarCurvature_eq_of_connected P z x)

theorem preferredScalarCurvature_pos
    (P : CompactConnectedPositiveTwistorCompatibleFourGeometry
      (E := E) (M := M)) (x : M) :
    0 < preferredScalarCurvature P.tangent P.connection x := by
  exact P.scalar_pos x (extChartAt 𝓘(ℝ,E) x x)
    ((extChartAt 𝓘(ℝ,E) x).map_source (by simp))

/-- A connected positive Einstein four-geometry normalizes to scalar 48
without any supplied global scalar constant. The anchor only chooses its
already constant scalar value. -/
theorem scalar_48_of_connected
    (P : CompactConnectedPositiveTwistorCompatibleFourGeometry
      (E := E) (M := M)) (x : M)
    (p : M) (y : E) (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target) :
    localScalarCurvature
      (rescaleCompactFour P
        (scaleTo48 (preferredScalarCurvature P.tangent P.connection x))
        (scaleTo48_pos (preferredScalarCurvature_pos P x))).tangent
      (rescaleCompactFour P
        (scaleTo48 (preferredScalarCurvature P.tangent P.connection x))
        (scaleTo48_pos (preferredScalarCurvature_pos P x))).connection
      p y hy = 48 := by
  exact compact_scalar_48_of_global_constant P
    (preferredScalarCurvature P.tangent P.connection x)
    (preferredScalarCurvature_pos P x)
    (localScalarCurvature_eq_at P x) p y hy

end
end QuaternionicSymmetry.ManifoldPositiveTwistorCompatibleFourSchur
