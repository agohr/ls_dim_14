import QuaternionicSymmetry.ManifoldQuaternionicImmersionTotalGeodesy
import QuaternionicSymmetry.ManifoldRiemannianFixedTotalGeodesyInput

/-! The former BG-R2 total-geodesy contract follows from the already supplied
smooth isometric quaternionic inclusion and compatible connections. -/
namespace QuaternionicSymmetry.ManifoldRiemannianFixedTotalGeodesyFromMathlib
open ManifoldQuaternionicInducedTotalGeodesy
open ManifoldRiemannianFixedTotalGeodesyInput
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

theorem fixedComponentTotalGeodesy : FixedComponentTotalGeodesyOnModel (E := E) (M := M) := by
  intro _ _ P S x k C
  letI := C.charts
  letI := C.manifold
  intro R hR DP DR
  rcases subsingleton_or_nontrivial (EuclideanSpace ℝ (Fin k)) with h | h
  · letI := h
    intro q p y hy u v
    have hv : v = 0 := Subsingleton.elim _ _
    simp [covariantHessian, hv]
  · letI := h
    exact ManifoldQuaternionicImmersionTotalGeodesy.isTotallyGeodesic P R
      Subtype.val C.inclusion_smooth C.inclusion_injective_derivative hR DP DR

end
end QuaternionicSymmetry.ManifoldRiemannianFixedTotalGeodesyFromMathlib
