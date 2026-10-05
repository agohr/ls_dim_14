import QuaternionicSymmetry.ManifoldQuaternionicCoordinateConnection

/-! The first algebraic Bianchi identity for actual tangent curvature, derived
from the torsion-free compatible connection and actual adapted solder. -/
namespace QuaternionicSymmetry.ManifoldQuaternionicFirstBianchi
open QuaternionicSymmetry.ManifoldQuaternionicCoordinateConnection
open QuaternionicSymmetry.LocalConnectionFirstBianchi
open QuaternionicSymmetry.LocalConnectionGauge
open ManifoldQuaternionicConnection
open scoped Manifold ContDiff Topology
noncomputable section
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
local instance : NormedSpace ℝ E := inferInstance
local instance : NormedSpace ℝ (E →L[ℝ] E) := inferInstance
local instance : NormedAlgebra ℝ (E →L[ℝ] E) := inferInstance
variable (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
  (D : CompatibleTangentConnection Q)

omit [FiniteDimensional ℝ E] [Nontrivial E] in
private theorem coordinateConnection_differentiableAt (p : M) (y : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target) :
    DifferentiableAt ℝ (coordinateConnection Q D p) y := by
  have hΓ : DifferentiableAt ℝ (D.form p) y :=
    ((D.smooth_form p).differentiableOn (by norm_num)).differentiableAt
      ((isOpen_extChartAt_target (I := 𝓘(ℝ,E)) p).mem_nhds hy)
  have hg := solder_contDiffAt Q p y hy
  have hh := coordinateInverse_contDiffAt Q p y hy
  have hD : DifferentiableAt ℝ (fderiv ℝ (solder Q p)) y :=
    (hg.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  exact differentiableAt_transform (D.form p) (solder Q p)
    (coordinateInverse Q p) y hΓ (hg.differentiableAt (by norm_num))
      (hh.differentiableAt (by norm_num)) hD

omit [FiniteDimensional ℝ E] [Nontrivial E] in
private theorem coordinateConnection_symmetric_eventually (p : M) (y : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target) (u v : E) :
    (fun z => coordinateConnection Q D p z u v) =ᶠ[𝓝 y]
      (fun z => coordinateConnection Q D p z v u) := by
  filter_upwards [(isOpen_extChartAt_target (I := 𝓘(ℝ,E)) p).mem_nhds hy]
    with z hz
  exact coordinateConnection_symmetric Q D p z hz u v

set_option maxHeartbeats 800000 in
omit [FiniteDimensional ℝ E] [Nontrivial E] in
theorem tangentCurvature_first_bianchi (p : M) (y u v w : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target) :
    D.curvature Q p y u v (solder Q p y w) +
      D.curvature Q p y v w (solder Q p y u) +
      D.curvature Q p y w u (solder Q p y v) = 0 := by
  have hΓ : DifferentiableAt ℝ (D.form p) y :=
    ((D.smooth_form p).differentiableOn (by norm_num)).differentiableAt
      ((isOpen_extChartAt_target (I := 𝓘(ℝ,E)) p).mem_nhds hy)
  have hg := solder_contDiffAt Q p y hy
  have hh := coordinateInverse_contDiffAt Q p y hy
  have hleft : (fun z => coordinateInverse Q p z * solder Q p z) =ᶠ[𝓝 y]
      fun _ => 1 := by
    filter_upwards [(isOpen_extChartAt_target (I := 𝓘(ℝ,E)) p).mem_nhds hy]
      with z hz
    exact coordinateInverse_left Q p z hz
  have hright := coordinateInverse_right Q p y hy
  have hF (a b : E) :
      LocalConnection.curvature (coordinateConnection Q D p) y a b =
        coordinateInverse Q p y * D.curvature Q p y a b * solder Q p y :=
    curvature_transform (D.form p) (solder Q p) (coordinateInverse Q p)
      y hΓ hg (hh.differentiableAt (by norm_num)) hleft hright a b
  have hB := first_bianchi (coordinateConnection Q D p) y
    (coordinateConnection_differentiableAt Q D p y hy)
    (coordinateConnection_symmetric_eventually Q D p y hy) u v w
  simp only [hF, ContinuousLinearMap.mul_apply] at hB
  have hs : solder Q p y * coordinateInverse Q p y = 1 := hright
  have hs' (a : E) : solder Q p y (coordinateInverse Q p y a) = a := by
    have h := congrArg (fun F : E →L[ℝ] E => F a) hs
    exact h
  have hB' := congrArg (solder Q p y) hB
  simpa only [map_add, map_zero, hs'] using hB'

end
end QuaternionicSymmetry.ManifoldQuaternionicFirstBianchi
