import QuaternionicSymmetry.SmoothLieGroupEquivDerivativeBracket

/-! Bracket preservation by the genuine identity differential of a smooth
group diffeomorphism, derived from Mathlib's naturality of vector-field
brackets. -/

namespace QuaternionicSymmetry.SmoothLieGroupEquivBracket

open SmoothLieGroupEquivDerivativeBracket
open VectorField
open scoped Manifold ContDiff
noncomputable section

variable {V G H : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [CompleteSpace V]
  [TopologicalSpace G] [TopologicalSpace H]
  [ChartedSpace V G] [ChartedSpace V H] [Group G] [Group H]
  [LieGroup 𝓘(ℂ,V) ∞ G] [LieGroup 𝓘(ℂ,V) ∞ H]

/-- The identity differential of a holomorphic group diffeomorphism
preserves the actual Mathlib `GroupLieAlgebra` bracket. -/
theorem mfderiv_one_map_lie
    (Φ : Diffeomorph 𝓘(ℂ,V) 𝓘(ℂ,V) G H ∞)
    (hOne : Φ (1 : G) = 1)
    (hMul : ∀ g x : G, Φ (g*x) = Φ g * Φ x)
    (v w : GroupLieAlgebra 𝓘(ℂ,V) G) :
    let d : GroupLieAlgebra 𝓘(ℂ,V) G →L[ℂ]
        GroupLieAlgebra 𝓘(ℂ,V) H :=
      by simpa only [hOne] using (mfderiv 𝓘(ℂ,V) 𝓘(ℂ,V) Φ 1)
    d ⁅v,w⁆ = ⁅d v,d w⁆ := by
  letI : ENat.LEInfty (minSmoothness ℂ 3) := by
    simpa only [minSmoothness_of_isRCLikeNormedField] using
      (inferInstance : ENat.LEInfty (3 : WithTop ℕ∞))
  letI : LieGroup 𝓘(ℂ,V) (minSmoothness ℂ 3) G := LieGroup.of_le (ENat.LEInfty.out)
  letI : LieGroup 𝓘(ℂ,V) (minSmoothness ℂ 3) H := LieGroup.of_le (ENat.LEInfty.out)
  let d : GroupLieAlgebra 𝓘(ℂ,V) G →L[ℂ]
      GroupLieAlgebra 𝓘(ℂ,V) H :=
    by simpa only [hOne] using (mfderiv 𝓘(ℂ,V) 𝓘(ℂ,V) Φ 1)
  have hInv (x : G) :
      (mfderiv 𝓘(ℂ,V) 𝓘(ℂ,V) Φ x).IsInvertible := by
    exact ⟨Φ.mfderivToContinuousLinearEquiv (by simp) x, rfl⟩
  have hField (u : GroupLieAlgebra 𝓘(ℂ,V) G) :
      mpullback 𝓘(ℂ,V) 𝓘(ℂ,V) Φ
        (mulInvariantVectorField
          ((mfderiv 𝓘(ℂ,V) 𝓘(ℂ,V) Φ 1) u)) =
      mulInvariantVectorField u := by
    funext x
    change (mfderiv 𝓘(ℂ,V) 𝓘(ℂ,V) Φ x).inverse
      (mulInvariantVectorField
        ((mfderiv 𝓘(ℂ,V) 𝓘(ℂ,V) Φ 1) u) (Φ x)) =
      mulInvariantVectorField u x
    rw [← mfderiv_mulInvariantVectorField Φ Φ.contMDiff hOne hMul x u]
    exact (hInv x).inverse_apply_self _
  have hNaturality := mpullback_mlieBracket
    (mdifferentiableAt_mulInvariantVectorField
      ((mfderiv 𝓘(ℂ,V) 𝓘(ℂ,V) Φ 1) v) (g := Φ (1 : G)))
    (mdifferentiableAt_mulInvariantVectorField
      ((mfderiv 𝓘(ℂ,V) 𝓘(ℂ,V) Φ 1) w) (g := Φ (1 : G)))
    (Φ.contMDiff.contMDiffAt)
    (by simpa only [minSmoothness_of_isRCLikeNormedField] using
      (inferInstance : ENat.LEInfty (2 : WithTop ℕ∞)).out)
  rw [hField v, hField w] at hNaturality
  simp only [mpullback] at hNaturality
  rw [hOne] at hNaturality
  have hBracket :
      (mfderiv 𝓘(ℂ,V) 𝓘(ℂ,V) Φ 1).inverse
        (cast (congrArg (TangentSpace 𝓘(ℂ,V)) hOne.symm) ⁅d v,d w⁆) = ⁅v,w⁆ := by
    simpa [TangentSpace, GroupLieAlgebra.bracket_def, mpullback,
      d, hOne] using hNaturality
  have h := congrArg (mfderiv 𝓘(ℂ,V) 𝓘(ℂ,V) Φ 1) hBracket
  simpa [d, hOne, (hInv (1 : G)).self_apply_inverse] using h.symm

end
end QuaternionicSymmetry.SmoothLieGroupEquivBracket
