import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.Diffeomorph

/-! For identity models, a fixed continuous linear change of chart
coordinates conjugates the actual tangent-bundle chart transition. -/

namespace QuaternionicSymmetry.ManifoldTangentCoordinateModelChange

open Manifold
open scoped Manifold ContDiff
noncomputable section

variable {R E M : Type*}
  [NormedAddCommGroup R] [NormedSpace ℝ R]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace R M]
  [IsManifold 𝓘(ℝ, R) 1 M]

theorem tangentCoordChange_transContinuousLinearEquiv
    (L : R ≃L[ℝ] E) (x y z : M) :
    tangentCoordChange ((𝓘(ℝ, R)).transContinuousLinearEquiv L) x y z =
      L.toContinuousLinearMap.comp
        ((tangentCoordChange 𝓘(ℝ, R) x y z).comp
          L.symm.toContinuousLinearMap) := by
  simp only [tangentCoordChange, tangentBundleCore_coordChange,
    OpenPartialHomeomorph.extend_coe,
    OpenPartialHomeomorph.extend_coe_symm,
    ModelWithCorners.coe_transContinuousLinearEquiv,
    ModelWithCorners.coe_transContinuousLinearEquiv_symm,
    modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
    Function.id_comp, Function.comp_id, Function.comp_assoc,
    Set.range_id, Set.image_univ,
    fderivWithin_univ]
  have hRange : Set.range (L : R → E) = Set.univ :=
    Set.range_eq_univ.mpr L.surjective
  rw [hRange, fderivWithin_univ]
  rw [L.comp_fderiv]
  simp only [← Function.comp_assoc]
  rw [L.symm.comp_right_fderiv]
  simp only [Function.comp_apply, L.symm_apply_apply]

end
end QuaternionicSymmetry.ManifoldTangentCoordinateModelChange
