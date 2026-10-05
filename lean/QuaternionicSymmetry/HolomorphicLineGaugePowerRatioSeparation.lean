import QuaternionicSymmetry.HolomorphicLinePowerSeparationFiniteFibers
import QuaternionicSymmetry.HolomorphicLineGaugePowers
import QuaternionicSymmetry.HolomorphicLineGaugeSections

/-! Power-section ratio separation is invariant under a genuine
holomorphic line gauge: its scalar changes cancel between numerator and
the matching tensor-power denominator. -/

namespace QuaternionicSymmetry.HolomorphicLineGaugePowerRatioSeparation
open HolomorphicLineGauge HolomorphicLineGaugeSections
open HolomorphicLineCoreClasses HolomorphicLineCorePullback
open HolomorphicLineTensorPowerClasses HolomorphicLineSectionRatios
open HolomorphicLinePowerSeparationFiniteFibers
open scoped Manifold ContDiff
noncomputable section

variable {B F : Type} [TopologicalSpace B]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
  [ChartedSpace F B] [IsManifold 𝓘(ℂ,F) ∞ B]
  (L W : LineCore.{0} (B := B) 𝓘(ℂ,F))
  (e : letI := L.holomorphic; letI := W.holomorphic
    GaugeIso (IB := 𝓘(ℂ,F)) L.core W.core)

theorem powerRatioSeparates_of_gauge
    (e : letI := L.holomorphic; letI := W.holomorphic
      GaugeIso (IB := 𝓘(ℂ,F)) L.core W.core)
    (k : ℕ) (hW : PowerRatioSeparates W k) :
    PowerRatioSeparates L k := by
  letI := L.holomorphic
  letI := W.holomorphic
  let eP := e.power k
  let S := sectionLinearEquiv 𝓘(ℂ,F) L W e
  let T := sectionLinearEquiv 𝓘(ℂ,F)
    (powerCoreRep 𝓘(ℂ,F) L k) (powerCoreRep 𝓘(ℂ,F) W k) eP
  intro s x y hx hy hxy
  let sW := S s
  have hne (z : B) :
      e.forward (L.core.indexAt z) (W.core.indexAt z) z ≠ 0 :=
    e.forward_ne_zero _ _ z
      ⟨L.core.mem_baseSet_at z, W.core.mem_baseSet_at z⟩
  have hs (z : B) :
      (show ℂ from sW z) =
        e.forward (L.core.indexAt z) (W.core.indexAt z) z *
          (show ℂ from s z) := by
    exact sectionLinearEquiv_apply 𝓘(ℂ,F) L W e s z
  have hxW : x ∈ nonzeroSet 𝓘(ℂ,F) W sW := by
    change (show ℂ from sW x) ≠ 0
    rw [hs x]
    exact mul_ne_zero (hne x) hx
  have hyW : y ∈ nonzeroSet 𝓘(ℂ,F) W sW := by
    change (show ℂ from sW y) ≠ 0
    rw [hs y]
    exact mul_ne_zero (hne y) hy
  obtain ⟨tW,htW⟩ := hW sW x y hxW hyW hxy
  let tL := T.symm tW
  have ht (z : B) :
      (show ℂ from tW z) =
        (e.forward (L.core.indexAt z) (W.core.indexAt z) z) ^ k *
          (show ℂ from tL z) := by
    have heq := sectionLinearEquiv_apply 𝓘(ℂ,F)
      (powerCoreRep 𝓘(ℂ,F) L k) (powerCoreRep 𝓘(ℂ,F) W k)
      eP tL z
    change (show ℂ from T tL z) = _ at heq
    rw [T.apply_symm_apply] at heq
    exact heq
  have hratio (z : B) (hz : z ∈ nonzeroSet 𝓘(ℂ,F) L s) :
      sectionRatio 𝓘(ℂ,F) W k sW tW z =
        sectionRatio 𝓘(ℂ,F) L k s tL z := by
    change (show ℂ from tW z) / ((show ℂ from sW z) ^ k) =
      (show ℂ from tL z) / ((show ℂ from s z) ^ k)
    rw [ht, hs, mul_pow]
    have ha := hne z
    have hv : (show ℂ from s z) ≠ 0 := hz
    field_simp
  refine ⟨tL, ?_⟩
  intro hEq
  apply htW
  rw [hratio x hx, hratio y hy]
  exact hEq

end
end QuaternionicSymmetry.HolomorphicLineGaugePowerRatioSeparation
