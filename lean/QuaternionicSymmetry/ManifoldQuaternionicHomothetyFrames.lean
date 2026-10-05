import QuaternionicSymmetry.ManifoldQuaternionicReduction

/-! Constant homotheties of actual adapted tangent frame gauges. -/
namespace QuaternionicSymmetry.ManifoldQuaternionicHomothetyFrames
open ManifoldQuaternionicReduction
open scoped Manifold ContDiff
noncomputable section
variable {E H M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  {n : WithTop ℕ∞} [IsManifold I (n + 1) M]
variable (F : TangentFrameGauge I (M := M) (n := n))

def rescale (s : ℝ) (hs : s ≠ 0) : TangentFrameGauge I (M := M) (n := n) where
  toFrame i x := s • F.toFrame i x
  fromFrame i x := s⁻¹ • F.fromFrame i x
  to_from i x hx v := by
    simp only [ContinuousLinearMap.smul_apply, map_smul, smul_smul]
    rw [F.to_from i x hx]
    simp [hs]
  from_to i x hx v := by
    simp only [ContinuousLinearMap.smul_apply, map_smul, smul_smul]
    rw [F.from_to i x hx]
    simp [hs]
  smooth_to i := (contMDiffOn_const : ContMDiffOn I 𝓘(ℝ) n
    (fun _ : M => s) _).smul (F.smooth_to i)
  smooth_from i := (contMDiffOn_const : ContMDiffOn I 𝓘(ℝ) n
    (fun _ : M => s⁻¹) _).smul (F.smooth_from i)

theorem rescale_coordChange (s : ℝ) (hs : s ≠ 0)
    (i j : atlas H M) (x : M) :
    (rescale F s hs).coordChange i j x = F.coordChange i j x := by
  ext v
  simp only [TangentFrameGauge.coordChange_apply, rescale,
    ContinuousLinearMap.smul_apply, map_smul, smul_smul]
  simp [hs]

end
end QuaternionicSymmetry.ManifoldQuaternionicHomothetyFrames
