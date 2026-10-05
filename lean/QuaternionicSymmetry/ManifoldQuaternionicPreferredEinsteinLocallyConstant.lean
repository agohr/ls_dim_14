import QuaternionicSymmetry.ManifoldQuaternionicPreferredEinsteinFactor

/-! The intrinsic Einstein factor is locally constant on the manifold.
The proof pulls the open constant fibers through genuine manifold charts. -/
namespace QuaternionicSymmetry.ManifoldQuaternionicPreferredEinsteinLocallyConstant
open ManifoldQuaternionicConnection
open ManifoldQuaternionicEinsteinFactor
open ManifoldQuaternionicEinsteinFactorLocallyConstant
open ManifoldQuaternionicPreferredEinsteinFactor
open ManifoldQuaternionicKSWEq38Input
open scoped Manifold ContDiff Topology
noncomputable section
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
local instance : NormedSpace ℝ E := inferInstance
variable (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
  (D : CompatibleTangentConnection Q)

theorem preferredEinsteinFactor_isLocallyConstant
    (S : QuaternionicStructure E)
    (hdecomp : KSWEq38Decomposition S Q D)
    (c : E) (hc : c ≠ 0)
    (hcard : 3 ≤ Module.finrank ℝ E) :
    IsLocallyConstant (preferredEinsteinFactor Q D c) := by
  intro r
  apply isOpen_iff_mem_nhds.mpr
  intro x hx
  let C := extChartAt 𝓘(ℝ,E) x
  let s := preferredEinsteinFactor Q D c x
  let T := C.target ∩ (einsteinFactor Q D x c) ⁻¹' {s}
  have hT : IsOpen T := target_factor_fiber_open Q D S hdecomp x c hc hcard s
  have hU : IsOpen (C.source ∩ C ⁻¹' T) :=
    (continuousOn_extChartAt x).isOpen_inter_preimage
      (isOpen_extChartAt_source x) hT
  have hxsrc : x ∈ C.source := by simp [C]
  have hy : C x ∈ C.target := C.map_source hxsrc
  have hxT : C x ∈ T := by
    refine ⟨hy, ?_⟩
    have h := factor_chart_eq_preferred Q D S hdecomp x c hc (C x) hy
    rw [C.left_inv hxsrc] at h
    simp [s, h]
  have hxU : x ∈ C.source ∩ C ⁻¹' T := ⟨hxsrc, hxT⟩
  have hsubset : C.source ∩ C ⁻¹' T ⊆
      (preferredEinsteinFactor Q D c) ⁻¹' r := by
    intro z hz
    have hfactor : einsteinFactor Q D x c (C z) = s := hz.2.2
    have h := factor_chart_eq_preferred Q D S hdecomp x c hc
      (C z) (hz.2.1)
    rw [C.left_inv hz.1] at h
    have hzx : preferredEinsteinFactor Q D c z = s := h.symm.trans hfactor
    change preferredEinsteinFactor Q D c z ∈ r
    rw [hzx]
    exact hx
  exact Filter.mem_of_superset (hU.mem_nhds hxU) hsubset

end
end QuaternionicSymmetry.ManifoldQuaternionicPreferredEinsteinLocallyConstant
