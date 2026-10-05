import QuaternionicSymmetry.ManifoldQuaternionicTwistorMetricEvaluationSmooth
import QuaternionicSymmetry.ManifoldFiniteDimensionalCLMSmooth
import Mathlib.Geometry.Manifold.VectorBundle.Hom

/-! Smooth local constant-frame tangent fields in a genuine twistor tangent
bundle trivialization, used to reconstruct the metric tensor from its
checked scalar evaluations. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicTwistorMetricFrameSmooth

open ManifoldTwistorSphereCore
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
  (I := 𝓘(ℝ,E)) (M := M) (n := ∞))

private abbrev J := (𝓘(ℝ,E)).prod (𝓡 2)
private abbrev F := E × EuclideanSpace ℝ (Fin 2)

def tangentFrameField (z₀ : SphereBundleTotal Q) (a : F (E := E))
    (z : SphereBundleTotal Q) : TangentSpace (J (E := E)) z :=
  (trivializationAt (F (E := E)) (TangentSpace (J (E := E))) z₀).symmL ℝ z a

theorem tangentFrameField_smoothOn (z₀ : SphereBundleTotal Q)
    (a : F (E := E)) :
    let e := trivializationAt (F (E := E)) (TangentSpace (J (E := E))) z₀
    ContMDiffOn (J (E := E)) (J (E := E)).tangent ∞
      (fun z => (⟨z,tangentFrameField Q z₀ a z⟩ :
        TangentBundle (J (E := E)) (SphereBundleTotal Q))) e.baseSet := by
  let e := trivializationAt (F (E := E)) (TangentSpace (J (E := E))) z₀
  have hpair : ContMDiffOn (J (E := E))
      ((J (E := E)).prod 𝓘(ℝ,F (E := E))) ∞
      (fun z : SphereBundleTotal Q => (z,a)) e.baseSet :=
    contMDiffOn_id.prodMk contMDiffOn_const
  have hmaps : Set.MapsTo (fun z : SphereBundleTotal Q => (z,a))
      e.baseSet e.target := by
    intro z hz
    exact e.mem_target.mpr hz
  have h := e.contMDiffOn_symm.comp hpair hmaps
  apply h.congr
  intro z hz
  have he := e.symm_apply_eq_mk_continuousLinearEquivAt_symm
    (R := ℝ) z hz a
  simpa only [tangentFrameField,
    e.symm_continuousLinearEquivAt_eq (R := ℝ) hz] using he.symm

end
end QuaternionicSymmetry.ManifoldQuaternionicTwistorMetricFrameSmooth
