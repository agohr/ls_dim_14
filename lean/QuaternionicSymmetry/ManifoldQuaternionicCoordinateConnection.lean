import QuaternionicSymmetry.LocalConnectionFirstBianchi
import QuaternionicSymmetry.ManifoldQuaternionicFourFormLocalCalculus
import QuaternionicSymmetry.LocalConnectionGauge

/-! The actual adapted tangent connection in the original chart-coordinate
frame. Torsion freeness becomes symmetry of its Christoffel operator. -/
namespace QuaternionicSymmetry.ManifoldQuaternionicCoordinateConnection
open ManifoldQuaternionicConnection
open ManifoldQuaternionicFourFormLocalCalculus
open QuaternionicSymmetry.LocalConnectionGauge
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

def coordinateInverse (p : M) (y : E) : E →L[ℝ] E :=
  Q.frames.fromFrame (achart E p) ((extChartAt 𝓘(ℝ,E) p).symm y)

def coordinateConnection (p : M) :
    LocalConnection.Form (E := E) (A := E →L[ℝ] E) :=
  LocalConnectionGauge.transform (D.form p) (solder Q p) (coordinateInverse Q p)

omit [FiniteDimensional ℝ E] [Nontrivial E] in
private theorem frame_mem (p : M) (y : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target) :
    (extChartAt 𝓘(ℝ,E) p).symm y ∈
      (tangentBundleCore 𝓘(ℝ,E) M).baseSet (achart E p) := by
  simpa only [tangentBundleCore_baseSet, coe_achart,
    ← extChartAt_source 𝓘(ℝ,E)] using
    (extChartAt 𝓘(ℝ,E) p).map_target hy

omit [FiniteDimensional ℝ E] [Nontrivial E] in
theorem coordinateInverse_left (p : M) (y : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target) :
    coordinateInverse Q p y * solder Q p y = 1 := by
  rw [solder_eq_toFrame Q p y hy]
  apply ContinuousLinearMap.ext
  intro v
  exact Q.frames.from_to (achart E p) _ (frame_mem p y hy) v

omit [FiniteDimensional ℝ E] [Nontrivial E] in
theorem coordinateInverse_right (p : M) (y : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target) :
    solder Q p y * coordinateInverse Q p y = 1 := by
  rw [solder_eq_toFrame Q p y hy]
  apply ContinuousLinearMap.ext
  intro v
  exact Q.frames.to_from (achart E p) _ (frame_mem p y hy) v

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
    ContDiffAt ℝ 2 (solder Q p) y := by
  let x := (extChartAt 𝓘(ℝ,E) p).symm y
  have hframe : ContMDiffAt 𝓘(ℝ,E) 𝓘(ℝ,E →L[ℝ] E) 2
      (Q.frames.toFrame (achart E p)) x :=
    ((Q.frames.smooth_to (achart E p) x (frame_mem p y hy)).of_le
      (show (2 : WithTop ℕ∞) ≤ ∞ from ENat.LEInfty.out)).contMDiffAt
        (((tangentBundleCore 𝓘(ℝ,E) M).isOpen_baseSet _).mem_nhds
          (frame_mem p y hy))
  have hsymm : ContMDiffAt 𝓘(ℝ,E) 𝓘(ℝ,E) 2
      (extChartAt 𝓘(ℝ,E) p).symm y :=
    (contMDiffOn_extChartAt_symm (n := 2) p y hy).contMDiffAt
      ((isOpen_extChartAt_target (I := 𝓘(ℝ,E)) p).mem_nhds hy)
  have hh : ContDiffAt ℝ 2
      (fun z => Q.frames.toFrame (achart E p)
        ((extChartAt 𝓘(ℝ,E) p).symm z)) y :=
    (hframe.comp y hsymm).contDiffAt
  exact hh.congr_of_eventuallyEq (by
    filter_upwards [(isOpen_extChartAt_target (I := 𝓘(ℝ,E)) p).mem_nhds hy]
      with z hz
    exact solder_eq_toFrame Q p z hz)

omit [FiniteDimensional ℝ E] [Nontrivial E] in
theorem coordinateConnection_symmetric (p : M) (y : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target) (u v : E) :
    coordinateConnection Q D p y u v = coordinateConnection Q D p y v u := by
  have ht := D.torsion p y u v hy
  have hleft := coordinateInverse_left Q p y hy
  change coordinateInverse Q p y
      (D.form p y u (solder Q p y v) + fderiv ℝ (solder Q p) y u v) =
    coordinateInverse Q p y
      (D.form p y v (solder Q p y u) + fderiv ℝ (solder Q p) y v u)
  apply congrArg (coordinateInverse Q p y)
  apply sub_eq_zero.mp
  calc
    _ = fderiv ℝ (solder Q p) y u v - fderiv ℝ (solder Q p) y v u +
        D.form p y u (solder Q p y v) -
        D.form p y v (solder Q p y u) := by abel
    _ = 0 := ht

end
end QuaternionicSymmetry.ManifoldQuaternionicCoordinateConnection
