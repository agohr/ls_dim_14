import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.Data.Complex.Basic

/-! Naturality in the second factor of the affine-scheme tensor-product
comparison. This is the remaining categorical square behind restricting a
torus × Proj chart action to an overlap. -/

namespace QuaternionicSymmetry.CategoryPullbackSpecTensorNaturality

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
noncomputable section

variable {S B B' : Type}
variable [CommRing S] [CommRing B] [CommRing B']
variable [Algebra ℂ S] [Algebra ℂ B] [Algebra ℂ B']

def secondFactorPullbackMap (β : B →ₐ[ℂ] B') :
    pullback
        (Spec.map (CommRingCat.ofHom (algebraMap ℂ S)))
        (Spec.map (CommRingCat.ofHom (algebraMap ℂ B'))) ⟶
      pullback
        (Spec.map (CommRingCat.ofHom (algebraMap ℂ S)))
        (Spec.map (CommRingCat.ofHom (algebraMap ℂ B))) := by
  refine pullback.map _ _ _ _ (𝟙 _) (Spec.map (CommRingCat.ofHom β.toRingHom))
    (𝟙 _) (by simp) ?_
  simp only [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 1
  congr 1
  apply RingHom.ext
  intro c
  exact (β.commutes c).symm

theorem pullbackSpecIso_natural_second (β : B →ₐ[ℂ] B') :
    (pullbackSpecIso ℂ S B').inv ≫ secondFactorPullbackMap β =
      Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.map (AlgHom.id S S) β).toRingHom) ≫
        (pullbackSpecIso ℂ S B).inv := by
  apply pullback.hom_ext
  · simp [secondFactorPullbackMap, Category.assoc, pullbackSpecIso_inv_fst]
    simp only [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    simpa only [AlgHom.comp_id] using congrArg AlgHom.toRingHom
      (Algebra.TensorProduct.map_comp_includeLeft (AlgHom.id S S) β).symm
  · simp [secondFactorPullbackMap, Category.assoc, pullbackSpecIso_inv_snd]
    simp only [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2

end
end QuaternionicSymmetry.CategoryPullbackSpecTensorNaturality
