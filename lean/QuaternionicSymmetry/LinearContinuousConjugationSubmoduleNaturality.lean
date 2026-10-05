import Mathlib.Analysis.Normed.Operator.ContinuousAlgEquiv
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! Passing a finite-dimensional real endomorphism plane to continuous
endomorphisms commutes with conjugation by a continuous linear equivalence. -/

namespace QuaternionicSymmetry.LinearContinuousConjugationSubmoduleNaturality

noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V]

theorem map_toContinuous_conj
    (D : V ≃L[ℝ] V) (P : Submodule ℝ (Module.End ℝ V)) :
    Submodule.map (Module.End.toContinuousLinearMap (𝕜 := ℝ) V).toLinearMap
      (Submodule.map (D.toLinearEquiv.conjAlgEquiv ℝ).toLinearMap P) =
    Submodule.map (D.conjContinuousAlgEquiv.toLinearMap)
      (Submodule.map (Module.End.toContinuousLinearMap (𝕜 := ℝ) V).toLinearMap P) := by
  ext S
  constructor
  · rintro ⟨T, ⟨R, hR, rfl⟩, rfl⟩
    refine ⟨Module.End.toContinuousLinearMap (𝕜 := ℝ) V R, ⟨R, hR, rfl⟩, ?_⟩
    ext v
    rfl
  · rintro ⟨T, ⟨R, hR, rfl⟩, rfl⟩
    refine ⟨(D.toLinearEquiv.conjAlgEquiv ℝ) R, ⟨R, hR, rfl⟩, ?_⟩
    ext v
    rfl

end
end QuaternionicSymmetry.LinearContinuousConjugationSubmoduleNaturality
