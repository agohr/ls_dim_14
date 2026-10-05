import QuaternionicSymmetry.HomeomorphLieAtlasTransfer
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions

/-! The coordinate derivative of a homeomorphism in its literal pulled-back
real self-model atlas is the identity linear map. -/

namespace QuaternionicSymmetry.HomeomorphPulledAtlasDerivative
open Filter
open scoped Manifold ContDiff Topology
noncomputable section

variable {V X Y : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace X] [TopologicalSpace Y] [ChartedSpace V Y]
  [IsManifold 𝓘(ℝ,V) ∞ Y]

theorem mfderiv_toFun_eq_id (e : X ≃ₜ Y) (x : X) :
    letI := HomeomorphLieAtlasTransfer.charts (V := V) e
    mfderiv 𝓘(ℝ,V) 𝓘(ℝ,V) e x = ContinuousLinearMap.id ℝ V := by
  letI := HomeomorphLieAtlasTransfer.charts (V := V) e
  letI := HomeomorphLieAtlasTransfer.manifold (V := V) e
  apply HasMFDerivAt.mfderiv
  constructor
  · exact e.continuous.continuousAt
  · have htarget : (chartAt V x).target ∈ 𝓝 ((chartAt V x) x) :=
      (chartAt V x).open_target.mem_nhds
        ((chartAt V x).map_source (ChartedSpace.mem_chart_source x))
    have heq : writtenInExtChartAt 𝓘(ℝ,V) 𝓘(ℝ,V) x e =ᶠ[
        𝓝 ((extChartAt 𝓘(ℝ,V) x) x)] (id : V → V) := by
      filter_upwards [htarget] with y hy
      change (chartAt V (e x)) (e ((chartAt V x).symm y)) = y
      change (e.toOpenPartialHomeomorph ≫ₕ chartAt V (e x))
        ((e.toOpenPartialHomeomorph ≫ₕ chartAt V (e x)).symm y) = y
      exact (e.toOpenPartialHomeomorph ≫ₕ chartAt V (e x)).right_inv hy
    exact ((hasFDerivAt_id ((extChartAt 𝓘(ℝ,V) x) x)).congr_of_eventuallyEq
      heq).hasFDerivWithinAt

end
end QuaternionicSymmetry.HomeomorphPulledAtlasDerivative
