import QuaternionicSymmetry.ManifoldTwistorSectionComparison

/-! The actual global section zero sets and complete linear-system base
locus are closed in the twistor space. -/
namespace QuaternionicSymmetry.ManifoldTwistorLinearSystem
open ManifoldTwistorLeBrunComplexAtlas ManifoldTwistorSphereCore
open ManifoldQuaternionicMetric ManifoldQuaternionicConnection TopologicalSpace
open scoped Manifold ContDiff
noncomputable section
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Nontrivial E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (Q : SmoothQuaternionicHermitianTangent (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
  (D : CompatibleTangentConnection Q)
variable {n : ℕ} {A : CompatibleComplexAtlas Q D n}
  (L : HolomorphicContactLine Q D n A) (r : ℤ)

theorem continuous_globalSection (s : GlobalSections Q D L r) :
    Continuous (fun x : SphereBundleTotal Q =>
      (⟨x, evaluation Q D L r x s⟩ : Bundle.TotalSpace ℂ
        (L.integerTwistCore Q D r).Fiber)) := by
  letI := A.charts
  letI := L.integerTwistCore_holomorphic Q D r
  exact ((global_coefficient_holomorphic_iff Q D L r _).mp s.2).continuous

theorem isClosed_zeroSet (s : GlobalSections Q D L r) :
    IsClosed (zeroSet Q D L r s) := by
  letI := A.charts
  letI := L.integerTwistCore_holomorphic Q D r
  let Z := L.integerTwistCore Q D r
  have hg := (global_coefficient_holomorphic_iff Q D L r
    (fun y => evaluation Q D L r y s)).mp s.2
  apply isOpen_compl_iff.mp
  apply isOpen_iff_mem_nhds.mpr
  intro x hx
  have hc : ContinuousAt (fun y : SphereBundleTotal Q =>
      Z.coordChange (Z.indexAt y) (Z.indexAt x) y
        (evaluation Q D L r y s)) x := by
    have h := ((Bundle.contMDiffAt_section x).mp (hg x)).continuousAt
    simpa only [VectorBundleCore.trivializationAt, VectorBundleCore.localTrivAt,
      VectorBundleCore.localTriv_apply] using h
  have hcx : Z.coordChange (Z.indexAt x) (Z.indexAt x) x
      (evaluation Q D L r x s) ≠ 0 := by
    rw [Z.coordChange_self _ _ (Z.mem_baseSet_at x)]
    exact hx
  have hne := (hc.ne_iff_eventually_ne continuousAt_const).mp hcx
  filter_upwards [hne] with y hy
  change evaluation Q D L r y s ≠ 0
  intro hz
  apply hy
  rw [hz, map_zero]

theorem isClosed_baseLocus :
    IsClosed (baseLocus Q D L r) := by
  rw [baseLocus_eq_iInter_zeroSet]
  exact isClosed_iInter (isClosed_zeroSet Q D L r)

end
end QuaternionicSymmetry.ManifoldTwistorLinearSystem
