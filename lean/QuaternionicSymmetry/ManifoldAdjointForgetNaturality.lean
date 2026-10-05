import QuaternionicSymmetry.VectorBundleFrameTransitions

/-! A genuine core transition acts on continuous endomorphisms by
conjugation; forgetting continuity gives conjugation by the corresponding
linear equivalence. The reverse core transition is proved to be the
inverse, not supplied as a new geometric premise. -/

namespace QuaternionicSymmetry.ManifoldAdjointForgetNaturality

open VectorBundleFrameTransitions
open scoped Topology Bundle
noncomputable section

variable {ι B V : Type*} [TopologicalSpace B]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

def forgetEnd : (V →L[ℝ] V) →ₗ[ℝ] Module.End ℝ V where
  toFun S := S.toLinearMap
  map_add' S T := by ext v; rfl
  map_smul' r S := by ext v; rfl

theorem forget_adjointCoordChange
    (Z : VectorBundleCore ℝ B V ι)
    (i j : ι) (x : B)
    (hi : x ∈ Z.baseSet i) (hj : x ∈ Z.baseSet j)
    (D : V ≃L[ℝ] V)
    (hD : (D : V →L[ℝ] V) = Z.coordChange i j x)
    (S : V →L[ℝ] V) :
    forgetEnd ((transitionAtlas Z).adjointCoordChange i j x S) =
      (D.toLinearEquiv.conjAlgEquiv ℝ) (forgetEnd S) := by
  have hReverse : (D.symm : V →L[ℝ] V) = Z.coordChange j i x := by
    apply ContinuousLinearMap.ext
    intro v
    apply D.injective
    change D (D.symm v) = D (Z.coordChange j i x v)
    rw [D.apply_symm_apply]
    have hDv := congrArg (fun L : V →L[ℝ] V => L (Z.coordChange j i x v)) hD
    change D (Z.coordChange j i x v) =
      Z.coordChange i j x (Z.coordChange j i x v) at hDv
    rw [hDv]
    exact ((Z.coordChange_comp j i j x ⟨⟨hj, hi⟩, hj⟩ v).trans
      (Z.coordChange_self j x hj v)).symm
  rw [adjointCoordChange_apply]
  apply LinearMap.ext
  intro v
  change Z.coordChange i j x (S (Z.coordChange j i x v)) =
    D (S (D.symm v))
  rw [← hD, ← hReverse]
  rfl

end
end QuaternionicSymmetry.ManifoldAdjointForgetNaturality
