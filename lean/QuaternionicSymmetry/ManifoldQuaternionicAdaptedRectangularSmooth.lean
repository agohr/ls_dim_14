import QuaternionicSymmetry.ManifoldQuaternionicInducedTotalGeodesy
import QuaternionicSymmetry.ManifoldQuaternionicInducedLocalDerivativeSmooth
import QuaternionicSymmetry.ManifoldQuaternionicInducedLocalCoefficientJointSmooth

/-! Smoothness of the adapted rectangular immersion derivative in fixed
orthonormal tangent gauges at their common center. -/
namespace QuaternionicSymmetry.ManifoldQuaternionicAdaptedRectangularSmooth
open ManifoldPositiveQuaternionicKahlerGeometry
open ManifoldQuaternionicInducedTotalGeodesy
open ManifoldQuaternionicInducedLocalIntertwining
open ManifoldQuaternionicInducedLocalDerivativeSmooth
open ManifoldQuaternionicInducedLocalCoefficientJointSmooth
open ManifoldQuaternionicSubmanifoldInput
open scoped Manifold ContDiff
noncomputable section

variable {E F M N : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [FiniteDimensional ℝ F] [Nontrivial F]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℝ,F) ∞ N]
variable (P : PositiveQuaternionicKahlerGeometry (E := E) (M := M))
  (R : PositiveQuaternionicKahlerGeometry (E := F) (M := N))
  (ι : N → M)
  (hSmooth : ContMDiff 𝓘(ℝ,F) 𝓘(ℝ,E) ∞ ι)

private def adaptedMapAt (c : N) (x : N) : F →L[ℝ] E :=
  (P.tangent.frames.toFrame (achart E (ι c)) (ι x)).comp
    ((localDerivative ι (achart F c) (achart E (ι c)) x).comp
      (R.tangent.frames.fromFrame (achart F c) x))

include hSmooth in
theorem adaptedMapAt_smoothAt_center (c : N) :
    ContMDiffAt 𝓘(ℝ,F) 𝓘(ℝ,F →L[ℝ] E) ∞
      (adaptedMapAt P R ι c) c := by
  let i := achart F c
  let j := achart E (ι c)
  have hs : c ∈ (tangentBundleCore 𝓘(ℝ,F) N).baseSet i :=
    (tangentBundleCore 𝓘(ℝ,F) N).mem_baseSet_at c
  have ht : ι c ∈ (tangentBundleCore 𝓘(ℝ,E) M).baseSet j :=
    (tangentBundleCore 𝓘(ℝ,E) M).mem_baseSet_at (ι c)
  have hfrom : ContMDiffAt 𝓘(ℝ,F) 𝓘(ℝ,F →L[ℝ] F) ∞
      (R.tangent.frames.fromFrame i) c :=
    (R.tangent.frames.smooth_from i c hs).contMDiffAt
      ((tangentBundleCore 𝓘(ℝ,F) N).isOpen_baseSet i |>.mem_nhds hs)
  have hto : ContMDiffAt 𝓘(ℝ,E) 𝓘(ℝ,E →L[ℝ] E) ∞
      (P.tangent.frames.toFrame j) (ι c) :=
    (P.tangent.frames.smooth_to j (ι c) ht).contMDiffAt
      ((tangentBundleCore 𝓘(ℝ,E) M).isOpen_baseSet j |>.mem_nhds ht)
  have hto' : ContMDiffAt 𝓘(ℝ,F) 𝓘(ℝ,E →L[ℝ] E) ∞
      (fun x => P.tangent.frames.toFrame j (ι x)) c :=
    hto.comp c hSmooth.contMDiffAt
  have hder : ContMDiffAt 𝓘(ℝ,F) 𝓘(ℝ,F →L[ℝ] E) ∞
      (localDerivative ι i j) c :=
    localDerivative_smoothAt_center ι hSmooth c
  have hcomp := hder.clm_comp hfrom
  have h := hto'.clm_comp hcomp
  exact h

include hSmooth in
theorem adaptedRectangularDerivative_differentiableAt_center (c : N) :
    DifferentiableAt ℝ
      (adaptedRectangularDerivative P R ι c (ι c))
      (extChartAt 𝓘(ℝ,F) c c) := by
  let e := extChartAt 𝓘(ℝ,F) c
  let y := e c
  have hc : c ∈ e.source := mem_extChartAt_source c
  have hy : y ∈ e.target := e.map_source hc
  have hsymm : ContMDiffAt 𝓘(ℝ,F) 𝓘(ℝ,F) ∞
      (e.symm : F → N) y :=
    (contMDiffOn_extChartAt_symm c y hy).contMDiffAt
      ((isOpen_extChartAt_target (I := 𝓘(ℝ,F)) c).mem_nhds hy)
  have heq : e.symm y = c := e.left_inv hc
  have hAt0 : ContMDiffAt 𝓘(ℝ,F) 𝓘(ℝ,F →L[ℝ] E) ∞
      (adaptedMapAt P R ι c) (e.symm y) := by
    simpa only [heq] using adaptedMapAt_smoothAt_center P R ι hSmooth c
  have hAt := hAt0.comp y hsymm
  change ContMDiffAt 𝓘(ℝ,F) 𝓘(ℝ,F →L[ℝ] E) ∞
    (adaptedRectangularDerivative P R ι c (ι c)) y at hAt
  exact hAt.contDiffAt.differentiableAt (by simp)

def localCoefficientInChart
    (hι : ∀ x, Function.Injective
      (mfderiv 𝓘(ℝ,F) 𝓘(ℝ,E) ι x))
    (hR : IsInducedQuaternionicGeometry P R ι)
    (c : N) (y : F) :
    (Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ) :=
  localCoefficientCLM P R ι hι hR
    (achart F c) (achart E (ι c))
    ((extChartAt 𝓘(ℝ,F) c).symm y)

include hSmooth in
theorem localCoefficientInChart_differentiableAt_center
    (hι : ∀ x, Function.Injective
      (mfderiv 𝓘(ℝ,F) 𝓘(ℝ,E) ι x))
    (hR : IsInducedQuaternionicGeometry P R ι)
    (c : N) :
    DifferentiableAt ℝ (localCoefficientInChart P R ι hι hR c)
      (extChartAt 𝓘(ℝ,F) c c) := by
  let e := extChartAt 𝓘(ℝ,F) c
  let y := e c
  have hc : c ∈ e.source := mem_extChartAt_source c
  have hy : y ∈ e.target := e.map_source hc
  have hsymm : ContMDiffAt 𝓘(ℝ,F) 𝓘(ℝ,F) ∞
      (e.symm : F → N) y :=
    (contMDiffOn_extChartAt_symm c y hy).contMDiffAt
      ((isOpen_extChartAt_target (I := 𝓘(ℝ,F)) c).mem_nhds hy)
  have heq : e.symm y = c := e.left_inv hc
  have hC0 : ContMDiffAt 𝓘(ℝ,F)
      𝓘(ℝ,(Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ)) ∞
      (fun x => localCoefficientCLM P R ι hι hR
        (achart F c) (achart E (ι c)) x) (e.symm y) := by
    simpa only [heq] using
      localCoefficientCLM_smoothAt_center P R ι hSmooth hι hR c
  have hC := hC0.comp y hsymm
  change ContMDiffAt 𝓘(ℝ,F)
    𝓘(ℝ,(Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ)) ∞
      (localCoefficientInChart P R ι hι hR c) y at hC
  exact hC.contDiffAt.differentiableAt (by simp)

end
end QuaternionicSymmetry.ManifoldQuaternionicAdaptedRectangularSmooth
