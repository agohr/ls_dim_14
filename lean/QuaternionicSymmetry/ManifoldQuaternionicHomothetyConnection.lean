import QuaternionicSymmetry.ManifoldQuaternionicHomothetyMetric
import QuaternionicSymmetry.ManifoldQuaternionicConnection

/-! The same geometric Levi-Civita connection in constant rescaled adapted frames. -/
namespace QuaternionicSymmetry.ManifoldQuaternionicHomothetyConnection
open ManifoldQuaternionicConnection ManifoldQuaternionicMetric
open ManifoldQuaternionicHomothetyFrames ManifoldQuaternionicHomothetyReduction
open scoped Manifold ContDiff
noncomputable section
variable {E H M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  {n : WithTop ℕ∞} [IsManifold I (n + 1) M]
variable (Q : SmoothQuaternionicHermitianTangent (I := I) (M := M) (n := n))

omit [I.Boundaryless] in
theorem adaptedGauge_rescale (s : ℝ) (hs : s ≠ 0)
    (p q : M) (y : E) :
    adaptedGauge (rescaleMetric Q s hs) p q y = adaptedGauge Q p q y := by
  exact rescale_coordChange Q.frames s hs _ _ _

omit [I.Boundaryless] in
theorem adaptedGaugeInv_rescale (s : ℝ) (hs : s ≠ 0)
    (p q : M) (y : E) :
    adaptedGaugeInv (rescaleMetric Q s hs) p q y = adaptedGaugeInv Q p q y := by
  exact rescale_coordChange Q.frames s hs _ _ _

omit [I.Boundaryless] in
theorem solder_rescale (s : ℝ) (hs : s ≠ 0) (p : M) (y : E) :
    solder (rescaleMetric Q s hs) p y = s • solder Q p y := by
  ext v
  simp only [solder, rescaleMetric, rescaleReduction, rescale,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply]

def rescaleConnection (D : CompatibleTangentConnection Q)
    (s : ℝ) (hs : s ≠ 0) :
    CompatibleTangentConnection (rescaleMetric Q s hs) where
  form := D.form
  smooth_form := D.smooth_form
  overlap := by
    intro p q y hy
    have hg : adaptedGauge (rescaleMetric Q s hs) p q = adaptedGauge Q p q :=
      funext (adaptedGauge_rescale Q s hs p q)
    have hh : adaptedGaugeInv (rescaleMetric Q s hs) p q = adaptedGaugeInv Q p q :=
      funext (adaptedGaugeInv_rescale Q s hs p q)
    rw [hg, hh]
    exact D.overlap p q y hy
  metric := D.metric
  quaternionic := D.quaternionic
  torsion := by
    intro p y u v hy
    have h := D.torsion p y u v hy
    have hsolder : solder (rescaleMetric Q s hs) p = fun z => s • solder Q p z :=
      funext (solder_rescale Q s hs p)
    have hf : fderiv ℝ (fun z => s • solder Q p z) y =
        s • fderiv ℝ (solder Q p) y := by
      simpa only [Pi.smul_apply] using congrArg (fun f : E → E →L[ℝ] (E →L[ℝ] E) => f y)
        (fderiv_const_smul_field (𝕜 := ℝ) (f := solder Q p) s)
    rw [hsolder, hf]
    simp only [ContinuousLinearMap.smul_apply, map_smul]
    simpa only [smul_sub, smul_add, smul_zero] using congrArg (s • ·) h

end
end QuaternionicSymmetry.ManifoldQuaternionicHomothetyConnection
