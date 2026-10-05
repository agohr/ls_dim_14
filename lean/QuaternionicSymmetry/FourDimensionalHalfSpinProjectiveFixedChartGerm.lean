import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveFixedChartPointwiseOverlap

/-! The fixed projective chart has a genuine open total-space source. On it
the explicit inverse is locally inverse, so actual chart-to-chart composition
is a germ identity rather than merely a formula at one chosen point. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveFixedChartGerm

open scoped Quaternion Manifold ContDiff Topology
open FourDimensionalHalfSpinProjectiveFixedChartCore
  FourDimensionalHalfSpinProjectiveFixedChartLeftInverse
  FourDimensionalHalfSpinProjectiveManifold
  FourDimensionalHalfSpinProjectiveCore
  FourDimensionalHalfSpinProjective
  ComplexProjectiveTopology
  ManifoldQuaternionicReduction

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℍ M]
  [IsManifold 𝓘(ℝ, ℍ) ∞ M]
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ, ℍ)) (M := M) (n := ∞))

def fixedChartSource (p : M) (i : Fin 2) : Set (SpinorBundleTotal Q) :=
  {z | z ∈ ((projectiveSpinorCore Q).localTriv (achart ℍ p)).toOpenPartialHomeomorph.source ∧
    ((projectiveSpinorCore Q).localTriv (achart ℍ p) z).2 ∈ affineDomain 1 i}

theorem fixedChartSource_isOpen (p : M) (i : Fin 2) :
    IsOpen (fixedChartSource Q p i) := by
  let L := ((projectiveSpinorCore Q).localTriv (achart ℍ p)).toOpenPartialHomeomorph
  have heq : fixedChartSource Q p i =
      L.source ∩ L ⁻¹' (Set.univ ×ˢ affineDomain 1 i) := by
    ext z
    simp only [fixedChartSource, Set.mem_setOf_eq, Set.mem_inter_iff,
      Set.mem_preimage, Set.mem_prod, Set.mem_univ, true_and]
    rfl
  rw [heq]
  exact L.continuousOn.isOpen_inter_preimage L.open_source
    (isOpen_univ.prod (isOpen_affineDomain 1 i))

theorem mem_fixedChartSource (p : M) (i : Fin 2)
    (z : SpinorBundleTotal Q)
    (hp : z.1 ∈ (extChartAt 𝓘(ℝ, ℍ) p).source)
    (hi : ((projectiveSpinorCore Q).localTriv (achart ℍ p) z).2 ∈
      affineDomain 1 i) : z ∈ fixedChartSource Q p i := by
  have hp' : z.1 ∈ (projectiveSpinorCore Q).baseSet (achart ℍ p) := by
    simpa only [projectiveSpinorCore,
      ManifoldQuaternionicReduction.TangentFrameGauge.adaptedCore,
      tangentBundleCore_baseSet, coe_achart,
      ← extChartAt_source 𝓘(ℝ, ℍ)] using hp
  exact ⟨((projectiveSpinorCore Q).mem_localTriv_source (achart ℍ p) z).mpr hp', hi⟩

theorem fixedProjectiveChartInv_left_eventually
    (p : M) (i : Fin 2) (z : SpinorBundleTotal Q)
    (hz : z ∈ fixedChartSource Q p i) :
    (fun w : SpinorBundleTotal Q =>
      fixedProjectiveChartInv Q p i (fixedProjectiveChart Q p i w)) =ᶠ[𝓝 z]
        id := by
  filter_upwards [(fixedChartSource_isOpen Q p i).mem_nhds hz] with w hw
  have hp' := ((projectiveSpinorCore Q).mem_localTriv_source (achart ℍ p) w).mp hw.1
  rw [← (projectiveSpinorCore Q).baseSet_at] at hp'
  have hp : w.1 ∈ (extChartAt 𝓘(ℝ, ℍ) p).source := by
    simpa only [projectiveSpinorCore,
      ManifoldQuaternionicReduction.TangentFrameGauge.adaptedCore,
      tangentBundleCore_baseSet, coe_achart,
      ← extChartAt_source 𝓘(ℝ, ℍ)] using hp'
  exact fixedProjectiveChartInv_left Q p i w hp hw.2

theorem fixedProjectiveChart_transition_eventually_at_total
    (p q : M) (i j : Fin 2) (z : SpinorBundleTotal Q)
    (hz : z ∈ fixedChartSource Q p i) :
    (fixedProjectiveChart Q q j) =ᶠ[𝓝 z]
      (fun w : SpinorBundleTotal Q => fixedProjectiveChart Q q j
        (fixedProjectiveChartInv Q p i (fixedProjectiveChart Q p i w))) := by
  filter_upwards [fixedProjectiveChartInv_left_eventually Q p i z hz] with w hw
  simpa only [id_eq] using congrArg (fixedProjectiveChart Q q j) hw.symm

end
end QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveFixedChartGerm
