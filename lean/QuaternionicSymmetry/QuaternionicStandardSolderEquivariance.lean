import QuaternionicSymmetry.QuaternionicStandardSolderQuaternionic

/-! Covariance of the genuine off-diagonal solder operator under the
standard product representation. -/
namespace QuaternionicSymmetry.QuaternionicStandardSolderEquivariance
open QuaternionicStandardSolderOperator QuaternionicProjectiveStandardL2
open QuaternionicProjectiveStandardRepresentation QuaternionicIsometryNormalizer
open QuaternionicUnitScalarIsometries
open scoped Quaternion
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] (S : QuaternionicStructure E)
local instance : NormedSpace ℝ E := inferInstance
local instance : NormedSpace ℝ (StandardSpace (E := E)) := inferInstance

def rightStarIsometry (q : unitary ℍ) : ℍ ≃ₗᵢ[ℝ] ℍ :=
  LinearIsometryEquiv.mk (rightStarEquiv q).toLinearEquiv (rightStarEquiv_norm q)

theorem column_covariant (p : symplecticKernel S × unitary ℍ) (v : E) (w : ℍ) :
    p.1.1.1 (column S v w) =
      column S ((symplecticProductAction S p).1 v) (rightStarIsometry p.2 w) := by
  obtain ⟨hI, hJ⟩ := (mem_symplecticKernel_iff S p.1.1).mp p.1.2
  change p.1.1.1 (S.action w v) =
    S.action (w * star (p.2 : ℍ)) (p.1.1.1 (S.action (p.2 : ℍ) v))
  have hc : p.1.1.1 (S.action (w * star (p.2 : ℍ)) (S.action (p.2 : ℍ) v)) =
      S.action (w * star (p.2 : ℍ)) (p.1.1.1 (S.action (p.2 : ℍ) v)) :=
    S.action_commutes p.1.1.1.toLinearEquiv.toLinearMap hI hJ _ _
  rw [← hc]
  apply congrArg p.1.1.1
  have hs := (Unitary.mem_iff.mp p.2.property).1
  rw [← Module.End.mul_apply, ← map_mul, mul_assoc, hs, mul_one]

theorem column_adjoint_covariant (p : symplecticKernel S × unitary ℍ)
    (v u : E) :
    (column S ((symplecticProductAction S p).1 v)).adjoint (p.1.1.1 u) =
      rightStarIsometry p.2 ((column S v).adjoint u) := by
  apply ext_inner_right ℝ
  intro x
  obtain ⟨w, rfl⟩ := (rightStarIsometry p.2).surjective x
  rw [ContinuousLinearMap.adjoint_inner_left, ← column_covariant,
    p.1.1.1.inner_map_map, (rightStarIsometry p.2).inner_map_map,
    ContinuousLinearMap.adjoint_inner_left]

theorem solderOperator_covariant (p : symplecticKernel S × unitary ℍ)
    (v : E) (z : StandardSpace (E := E)) :
    solderOperator S ((symplecticProductAction S p).1 v) (standardIsometryL2 S p z) =
      standardIsometryL2 S p (solderOperator S v z) := by
  apply (WithLp.prodContinuousLinearEquiv 2 ℝ E ℍ).injective
  apply Prod.ext
  · exact (column_covariant S p v z.snd).symm
  · change -(column S ((symplecticProductAction S p).1 v)).adjoint (p.1.1.1 z.fst) =
      rightStarIsometry p.2 (-(column S v).adjoint z.fst)
    rw [column_adjoint_covariant, map_neg]

end
end QuaternionicSymmetry.QuaternionicStandardSolderEquivariance
