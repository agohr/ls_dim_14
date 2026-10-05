import QuaternionicSymmetry.GeneralRealAdjointDifferentialSource
import QuaternionicSymmetry.GeneralComplexAdjointDifferentialSource

/-! The complex-atlas adjoint identity is an internal consequence of Lee's
real theorem: the complex Lie charts have their canonical real companion,
the two conjugation derivatives coincide after scalar restriction, and the
actual left-invariant brackets coincide. -/

namespace QuaternionicSymmetry.GeneralComplexAdjointFromReal

open GeneralRealAdjointDifferentialSource
open GeneralComplexAdjointDifferentialSource
open ComplexLieRealCompanion
open ComplexManifoldDerivativeScalarRestriction
open ComplexGroupLieBracketRestriction
open scoped Manifold ContDiff
noncomputable section

/-- Lee's real adjoint derivative yields the exact same-atlas complex
adjoint differential contract; no additional external complex theorem is
used. -/
theorem complexAdjointDifferential_of_real
    (hLee : LeeRealAdjointDifferentialSource) :
    LeeComplexAdjointDifferentialSource := by
  intro V G _ _ _ _ _ _ _ _ _ _
  letI : CompleteSpace V := FiniteDimensional.complete ℂ V
  letI : IsManifold 𝓘(ℝ,V) ∞ G := realManifold
  letI : LieGroup 𝓘(ℝ,V) ∞ G := realLieGroup
  letI : ENat.LEInfty (minSmoothness ℝ 3) := by
    simpa only [minSmoothness_of_isRCLikeNormedField] using
      (inferInstance : ENat.LEInfty (3 : WithTop ℕ∞))
  letI : ENat.LEInfty (minSmoothness ℂ 3) := by
    simpa only [minSmoothness_of_isRCLikeNormedField] using
      (inferInstance : ENat.LEInfty (3 : WithTop ℕ∞))
  intro v
  obtain ⟨hRealDiff,hRealBracket⟩ := hLee (V := V) (G := G) v
  have hOrbit : adjointOrbitReal v = adjointOrbit v := by
    funext g
    unfold adjointOrbitReal adjointOrbit
    have hr : MDifferentiableAt 𝓘(ℝ,V) 𝓘(ℝ,V)
        (fun h : G => g * h * g⁻¹) 1 := by
      have hs : ContMDiff 𝓘(ℝ,V) 𝓘(ℝ,V) ∞
          (fun h : G => g * h * g⁻¹) := by
        simpa only [Function.comp_def] using
          (contMDiff_mul_right (I := 𝓘(ℝ,V)) (n := ∞) (a := g⁻¹)).comp
            (contMDiff_mul_left (I := 𝓘(ℝ,V)) (n := ∞) (a := g))
      exact hs.mdifferentiableAt (by simp)
    have hc : MDifferentiableAt 𝓘(ℂ,V) 𝓘(ℂ,V)
        (fun h : G => g * h * g⁻¹) 1 := by
      have hs : ContMDiff 𝓘(ℂ,V) 𝓘(ℂ,V) ∞
          (fun h : G => g * h * g⁻¹) := by
        simpa only [Function.comp_def] using
          (contMDiff_mul_right (I := 𝓘(ℂ,V)) (n := ∞) (a := g⁻¹)).comp
            (contMDiff_mul_left (I := 𝓘(ℂ,V)) (n := ∞) (a := g))
      exact hs.mdifferentiableAt (by simp)
    rw [mfderiv_real_eq_complex hr hc]
    rfl
  constructor
  · simpa only [← hOrbit] using hRealDiff
  · intro u
    rw [← hOrbit, hRealBracket]
    exact bracket_real_eq_complex (V := V) (K := G) u v

end
end QuaternionicSymmetry.GeneralComplexAdjointFromReal
