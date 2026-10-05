import QuaternionicSymmetry.ManifoldQuaternionicCoordinateConnection
import QuaternionicSymmetry.LocalConnectionGaugeSmooth
import QuaternionicSymmetry.LocalConnectionRiemannSecondBianchi

/-! The actual tangent connection satisfies the differential second Bianchi
identity in chart coordinates. -/
namespace QuaternionicSymmetry.ManifoldQuaternionicCoordinateSecondBianchi
open ManifoldQuaternionicConnection
open ManifoldQuaternionicCoordinateConnection
open QuaternionicSymmetry.LocalConnectionGaugeSmooth
open QuaternionicSymmetry.LocalConnectionRiemannSecondBianchi
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
private theorem frame_mem (p : M) (y : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target) :
    (extChartAt 𝓘(ℝ,E) p).symm y ∈
      (tangentBundleCore 𝓘(ℝ,E) M).baseSet (achart E p) := by
  simpa only [tangentBundleCore_baseSet, coe_achart,
    ← extChartAt_source 𝓘(ℝ,E)] using
    (extChartAt 𝓘(ℝ,E) p).map_target hy

omit [FiniteDimensional ℝ E] [Nontrivial E] in
theorem coordinateInverse_contDiffAt (p : M) (y : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target) :
    ContDiffAt ℝ 2 (coordinateInverse Q p) y := by
  let x := (extChartAt 𝓘(ℝ,E) p).symm y
  have hframe : ContMDiffAt 𝓘(ℝ,E) 𝓘(ℝ,E →L[ℝ] E) 2
      (Q.frames.fromFrame (achart E p)) x :=
    ((Q.frames.smooth_from (achart E p) x (frame_mem p y hy)).of_le
      (show (2 : WithTop ℕ∞) ≤ ∞ from ENat.LEInfty.out)).contMDiffAt
        (((tangentBundleCore 𝓘(ℝ,E) M).isOpen_baseSet _).mem_nhds
          (frame_mem p y hy))
  have hsymm : ContMDiffAt 𝓘(ℝ,E) 𝓘(ℝ,E) 2
      (extChartAt 𝓘(ℝ,E) p).symm y :=
    (contMDiffOn_extChartAt_symm (n := 2) p y hy).contMDiffAt
      ((isOpen_extChartAt_target (I := 𝓘(ℝ,E)) p).mem_nhds hy)
  exact (hframe.comp y hsymm).contDiffAt

omit [FiniteDimensional ℝ E] [Nontrivial E] in
theorem solder_contDiffAt (p : M) (y : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target) :
    ContDiffAt ℝ 3 (solder Q p) y := by
  let x := (extChartAt 𝓘(ℝ,E) p).symm y
  have hframe : ContMDiffAt 𝓘(ℝ,E) 𝓘(ℝ,E →L[ℝ] E) 3
      (Q.frames.toFrame (achart E p)) x :=
    ((Q.frames.smooth_to (achart E p) x (frame_mem p y hy)).of_le
      (show (3 : WithTop ℕ∞) ≤ ∞ from ENat.LEInfty.out)).contMDiffAt
        (((tangentBundleCore 𝓘(ℝ,E) M).isOpen_baseSet _).mem_nhds
          (frame_mem p y hy))
  have hsymm : ContMDiffAt 𝓘(ℝ,E) 𝓘(ℝ,E) 3
      (extChartAt 𝓘(ℝ,E) p).symm y :=
    (contMDiffOn_extChartAt_symm (n := 3) p y hy).contMDiffAt
      ((isOpen_extChartAt_target (I := 𝓘(ℝ,E)) p).mem_nhds hy)
  have hh : ContDiffAt ℝ 3
      (fun z => Q.frames.toFrame (achart E p)
        ((extChartAt 𝓘(ℝ,E) p).symm z)) y :=
    (hframe.comp y hsymm).contDiffAt
  exact hh.congr_of_eventuallyEq (by
    filter_upwards [(isOpen_extChartAt_target (I := 𝓘(ℝ,E)) p).mem_nhds hy]
      with z hz
    exact solder_eq_toFrame Q p z hz)

omit [FiniteDimensional ℝ E] [Nontrivial E] in
theorem coordinateConnection_contDiffAt (p : M) (y : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target) :
    ContDiffAt ℝ 2 (coordinateConnection Q D p) y := by
  have hΓ : ContDiffAt ℝ 2 (D.form p) y :=
    ((D.smooth_form p).of_le
      (show (2 : WithTop ℕ∞) ≤ ∞ from ENat.LEInfty.out)).contDiffAt
        ((isOpen_extChartAt_target (I := 𝓘(ℝ,E)) p).mem_nhds hy)
  exact contDiffAt_transform (D.form p) (solder Q p) (coordinateInverse Q p)
    y hΓ (solder_contDiffAt Q p y hy) (coordinateInverse_contDiffAt Q p y hy)

omit [FiniteDimensional ℝ E] [Nontrivial E] in
theorem coordinate_second_bianchi (p : M) (y : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target) (u v w z : E) :
    covariantRiemannDerivative (coordinateConnection Q D p) y u v w z +
      covariantRiemannDerivative (coordinateConnection Q D p) y v w u z +
        covariantRiemannDerivative (coordinateConnection Q D p) y w u v z = 0 :=
  second_bianchi (coordinateConnection Q D p) y
    (coordinateConnection_contDiffAt Q D p y hy)
    (coordinateConnection_symmetric Q D p y hy) u v w z

end
end QuaternionicSymmetry.ManifoldQuaternionicCoordinateSecondBianchi
