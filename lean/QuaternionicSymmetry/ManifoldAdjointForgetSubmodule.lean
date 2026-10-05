import QuaternionicSymmetry.ManifoldAdjointForgetNaturality

/-! The pointwise adjoint/forgetful identity extends exactly to every
submodule of continuous tangent endomorphisms. -/

namespace QuaternionicSymmetry.ManifoldAdjointForgetSubmodule

open VectorBundleFrameTransitions
open ManifoldAdjointForgetNaturality
open scoped Topology Bundle
noncomputable section

variable {ι B V : Type*} [TopologicalSpace B]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem forget_map_adjoint
    (Z : VectorBundleCore ℝ B V ι)
    (i j : ι) (x : B)
    (hi : x ∈ Z.baseSet i) (hj : x ∈ Z.baseSet j)
    (D : V ≃L[ℝ] V)
    (hD : (D : V →L[ℝ] V) = Z.coordChange i j x)
    (P : Submodule ℝ (V →L[ℝ] V)) :
    Submodule.map forgetEnd
      (Submodule.map ((transitionAtlas Z).adjointCoordChange i j x).toLinearMap P) =
      Submodule.map (D.toLinearEquiv.conjAlgEquiv ℝ).toLinearMap
        (Submodule.map forgetEnd P) := by
  ext S
  constructor
  · rintro ⟨T, ⟨R, hR, rfl⟩, rfl⟩
    exact ⟨forgetEnd R, ⟨R, hR, rfl⟩,
      (forget_adjointCoordChange Z i j x hi hj D hD R).symm⟩
  · rintro ⟨T, ⟨R, hR, rfl⟩, rfl⟩
    exact ⟨(transitionAtlas Z).adjointCoordChange i j x R,
      ⟨R, hR, rfl⟩,
      forget_adjointCoordChange Z i j x hi hj D hD R⟩

end
end QuaternionicSymmetry.ManifoldAdjointForgetSubmodule
