import QuaternionicSymmetry.CompactSymplecticProjectorPlaneCocycle

/-! Source-free naturality of the span of linear endomorphisms under a
commuting square of genuine linear equivalences. This is the algebraic
step behind changing the actual projector Q-plane from real to Euclidean
tangent coordinates. -/

namespace QuaternionicSymmetry.LinearConjugationSubmoduleNaturality

noncomputable section

variable {V W : Type*} [AddCommGroup V] [Module ℝ V]
  [AddCommGroup W] [Module ℝ W]

private theorem conj_trans
    {A B C : Type*} [AddCommGroup A] [Module ℝ A]
    [AddCommGroup B] [Module ℝ B]
    [AddCommGroup C] [Module ℝ C]
    (f : A ≃ₗ[ℝ] B) (g : B ≃ₗ[ℝ] C) :
    (f.trans g).conjAlgEquiv ℝ =
      (f.conjAlgEquiv ℝ).trans (g.conjAlgEquiv ℝ) := by
  ext S v
  rfl

theorem submodule_map_conj_commutes
    (U : V ≃ₗ[ℝ] W) (C : V ≃ₗ[ℝ] V) (D : W ≃ₗ[ℝ] W)
    (h : C.trans U = U.trans D)
    (P : Submodule ℝ (Module.End ℝ V)) :
    (P.map (C.conjAlgEquiv ℝ).toLinearMap).map
        (U.conjAlgEquiv ℝ).toLinearMap =
      (P.map (U.conjAlgEquiv ℝ).toLinearMap).map
        (D.conjAlgEquiv ℝ).toLinearMap := by
  have hComm (S : Module.End ℝ V) :
      (U.conjAlgEquiv ℝ) ((C.conjAlgEquiv ℝ) S) =
        (D.conjAlgEquiv ℝ) ((U.conjAlgEquiv ℝ) S) := by
    calc
      _ = ((C.trans U).conjAlgEquiv ℝ) S := by rw [conj_trans]; rfl
      _ = ((U.trans D).conjAlgEquiv ℝ) S := by rw [h]
      _ = _ := by rw [conj_trans]; rfl
  ext S
  constructor
  · rintro ⟨T, ⟨R, hR, rfl⟩, rfl⟩
    exact ⟨(U.conjAlgEquiv ℝ) R, ⟨R, hR, rfl⟩, (hComm R).symm⟩
  · rintro ⟨T, ⟨R, hR, rfl⟩, rfl⟩
    exact ⟨(C.conjAlgEquiv ℝ) R, ⟨R, hR, rfl⟩, hComm R⟩

end
end QuaternionicSymmetry.LinearConjugationSubmoduleNaturality
