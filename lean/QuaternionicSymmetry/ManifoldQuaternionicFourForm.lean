import QuaternionicSymmetry.QuaternionicFourFormRotation
import QuaternionicSymmetry.ManifoldChartFormGluing
import QuaternionicSymmetry.LocalConnectionExterior
import Mathlib.Geometry.Manifold.Algebra.Monoid

/-! Local Kähler two-forms and their normalized quaternionic four-form. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicFourForm

open Matrix QuaternionicSymmetry.ManifoldQuaternionicMetric
  QuaternionicSymmetry.ManifoldQuaternionicReduction
  QuaternionicSymmetry.ManifoldChartFormGluing
  QuaternionicSymmetry.LocalConnectionExterior
  QuaternionicSymmetry.QuaternionicFourFormRotation
  QuaternionicSymmetry.ContinuousWedge
open scoped Manifold Topology ContDiff

noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Nontrivial E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

local instance : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace
local instance : NormedAddCommGroup (E [⋀^Fin 2]→L[ℝ] ℝ) := inferInstance
local instance : NormedSpace ℝ (E [⋀^Fin 2]→L[ℝ] ℝ) := inferInstance
local instance : NormedAddCommGroup (E [⋀^Fin 4]→L[ℝ] ℝ) := inferInstance
local instance : NormedSpace ℝ (E [⋀^Fin 4]→L[ℝ] ℝ) := inferInstance

variable (Q : SmoothQuaternionicHermitianTangent
  (I := 𝓘(ℝ, E)) (M := M) (n := ∞))

/-- The chart Kähler two-form, obtained by alternating the metric paired
with the local quaternionic generator. The factor `1/2` corrects the
alternatization of a skew bilinear map. -/
def chartKahler (i : atlas E M) (x : M) (t : Fin 3) :
    E [⋀^Fin 2]→L[ℝ] ℝ :=
  (1 / 2 : ℝ) • LocalConnectionForms.alternatingPart
    ((Q.chartMetricForm i x).comp (Q.toSmoothAlmostQuaternionicTangent.chartGenerator i t x))

omit [Nontrivial E] [FiniteDimensional ℝ E] in
theorem chartKahler_smooth (i : atlas E M) (t : Fin 3) :
    ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E [⋀^Fin 2]→L[ℝ] ℝ) ∞
      (fun x => chartKahler Q i x t)
      ((tangentBundleCore 𝓘(ℝ, E) M).baseSet i) := by
  have hm := Q.smooth_chartMetricForm i
  have hJ := Q.toSmoothAlmostQuaternionicTangent.smooth_chartGenerator i t
  have hcomp := hm.clm_comp hJ
  have hconst : ContMDiffOn 𝓘(ℝ, E)
      𝓘(ℝ, (E →L[ℝ] E →L[ℝ] ℝ) →L[ℝ] (E [⋀^Fin 2]→L[ℝ] ℝ)) ∞
      (fun _ : M => alternatingPartCLM (E := E) (A := ℝ))
      ((tangentBundleCore 𝓘(ℝ, E) M).baseSet i) := contMDiffOn_const
  have halt := hconst.clm_apply hcomp
  have hscaled := (contMDiffOn_const : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ) ∞
    (fun _ : M => (1 / 2 : ℝ))
    ((tangentBundleCore 𝓘(ℝ, E) M).baseSet i)).smul halt
  simpa only [alternatingPartCLM_apply, chartKahler] using hscaled

/-- The canonical normalized sum of the three wedge squares in one adapted
chart. -/
def chartFour (i : atlas E M) (x : M) : E [⋀^Fin 4]→L[ℝ] ℝ :=
  ∑ t : Fin 3, wedge (ContinuousLinearMap.mul ℝ ℝ)
    (chartKahler Q i x t) (chartKahler Q i x t)

omit [Nontrivial E] [FiniteDimensional ℝ E] in
theorem chartFour_smooth (i : atlas E M) :
    ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E [⋀^Fin 4]→L[ℝ] ℝ) ∞
      (chartFour Q i) ((tangentBundleCore 𝓘(ℝ, E) M).baseSet i) := by
  unfold chartFour
  have hterm (t : Fin 3) : ContMDiffOn 𝓘(ℝ, E)
      𝓘(ℝ, E [⋀^Fin 4]→L[ℝ] ℝ) ∞
      (fun x => wedge (ContinuousLinearMap.mul ℝ ℝ)
        (chartKahler Q i x t) (chartKahler Q i x t))
      ((tangentBundleCore 𝓘(ℝ, E) M).baseSet i) := by
    have hconst : ContMDiffOn 𝓘(ℝ, E)
        𝓘(ℝ, (E [⋀^Fin 2]→L[ℝ] ℝ) →L[ℝ]
          (E [⋀^Fin 2]→L[ℝ] ℝ) →L[ℝ] (E [⋀^Fin 4]→L[ℝ] ℝ)) ∞
        (fun _ : M => wedgeCLM (E := E) (p := 2) (q := 2)
          (ContinuousLinearMap.mul ℝ ℝ))
        ((tangentBundleCore 𝓘(ℝ, E) M).baseSet i) := contMDiffOn_const
    have hleft := hconst.clm_apply (chartKahler_smooth Q i t)
    simpa only [wedgeCLM_apply] using
      hleft.clm_apply (chartKahler_smooth Q i t)
  classical
  exact contMDiffOn_finset_sum (fun t _ => hterm t)

omit [Nontrivial E] [FiniteDimensional ℝ E] in
theorem chartFour_rotate (i : atlas E M) (x : M)
    (R : Matrix (Fin 3) (Fin 3) ℝ) (hR : Rᵀ * R = 1) :
    ∑ t : Fin 3, wedge (ContinuousLinearMap.mul ℝ ℝ)
      (∑ s : Fin 3, R t s • chartKahler Q i x s)
      (∑ s : Fin 3, R t s • chartKahler Q i x s) =
        chartFour Q i x := by
  exact sum_wedge_square_rotate R hR (chartKahler Q i x)

end
end QuaternionicSymmetry.ManifoldQuaternionicFourForm
