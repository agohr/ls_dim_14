import QuaternionicSymmetry.GeneralLeviCivitaSource
import Mathlib.Geometry.Manifold.MFDeriv.Atlas

/-! The metric of a genuine Riemannian manifold remains positive definite
when pulled into any valid self-model chart. This is an internal bridge for
coordinate Koszul uniqueness, not an additional source premise. -/

namespace QuaternionicSymmetry.GeneralLeviCivitaCoordinatePositive

open Manifold Bundle GeneralLeviCivitaSource
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

theorem chartMetric_pos
    (g : ContMDiffRiemannianMetric 𝓘(ℝ,E) ∞ E
      (TangentSpace 𝓘(ℝ,E) : M → Type _))
    (p : M) (y v : E) (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target)
    (hv : v ≠ 0) : 0 < chartMetric g p y v v := by
  let A := mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (extChartAt 𝓘(ℝ,E) p).symm y
  have hcomp := mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm
    (I := 𝓘(ℝ,E)) hy
  have hcomp' :
      (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (extChartAt 𝓘(ℝ,E) p)
        ((extChartAt 𝓘(ℝ,E) p).symm y)) ∘L A =
        ContinuousLinearMap.id ℝ E := by
    simpa only [A, ModelWithCorners.range_eq_univ, mfderivWithin_univ] using hcomp
  have hAv : A v ≠ 0 := by
    intro hz
    have h := congrArg (fun L : E →L[ℝ] E => L v) hcomp'
    change (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (extChartAt 𝓘(ℝ,E) p)
      ((extChartAt 𝓘(ℝ,E) p).symm y)) (A v) = v at h
    rw [hz, map_zero] at h
    exact hv h.symm
  exact g.pos ((extChartAt 𝓘(ℝ,E) p).symm y) (A v) hAv

end
end QuaternionicSymmetry.GeneralLeviCivitaCoordinatePositive
