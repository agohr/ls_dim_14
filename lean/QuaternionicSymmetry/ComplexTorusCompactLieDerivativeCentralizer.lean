import QuaternionicSymmetry.ComplexGroupLieBracketRestriction
import QuaternionicSymmetry.SelectedTorusCompactInclusionSmooth

/-! In any genuine complex Lie target, the real differential image of
an actual complex-torus homomorphism centralizes the differential image
of its literal compact restriction. This uses actual commuting group
images and the checked Lie-bracket naturality, not a formal marker. -/

namespace QuaternionicSymmetry.ComplexTorusCompactLieDerivativeCentralizer

open TorusLaurentRepresentation
open ComplexTorusHolomorphicStructure ComplexTorusLieGroup
open ComplexLieRealCompanion ComplexGroupLieBracketRestriction
open scoped Manifold ContDiff
noncomputable section

variable {r d : ℕ} {VC K : Type}
  [NormedAddCommGroup VC] [NormedSpace ℂ VC]
  [FiniteDimensional ℂ VC]
  [Group K] [TopologicalSpace K] [ChartedSpace VC K]
  [IsManifold 𝓘(ℂ,VC) ∞ K] [LieGroup 𝓘(ℂ,VC) ∞ K]
  (f : ComplexTorus r →* K)
  (hChart : ChartedSpace (Fin d → ℝ) (Fin r → Circle))
  (hManifold : letI := hChart
    IsManifold 𝓘(ℝ,Fin d → ℝ) ∞ (Fin r → Circle))
  (hLie : letI := hChart
    LieGroup 𝓘(ℝ,Fin d → ℝ) ∞ (Fin r → Circle))

include hManifold hLie

theorem compact_restriction_derivatives_commute
    (hf : ContMDiff 𝓘(ℝ,Fin r → ℂ) 𝓘(ℝ,VC) ∞ f)
    (hInc : letI := hChart
      ContMDiff 𝓘(ℝ,Fin d → ℝ) 𝓘(ℝ,Fin r → ℂ) ∞
        (compactInclusion r))
    (v : Fin r → ℂ) (w : Fin d → ℝ) :
    letI := hChart
    @Bracket.bracket (GroupLieAlgebra 𝓘(ℂ,VC) K)
      (GroupLieAlgebra 𝓘(ℂ,VC) K) inferInstance
      (mfderiv 𝓘(ℝ,Fin r → ℂ) 𝓘(ℝ,VC) f 1 v)
      (mfderiv 𝓘(ℝ,Fin d → ℝ) 𝓘(ℝ,VC)
        (f.comp (compactInclusion r)) 1 w) = 0 := by
  letI : ChartedSpace (Fin d → ℝ) (Fin r → Circle) := hChart
  letI : IsManifold 𝓘(ℝ,Fin d → ℝ) ∞ (Fin r → Circle) := hManifold
  letI : LieGroup 𝓘(ℝ,Fin d → ℝ) ∞ (Fin r → Circle) := hLie
  letI : IsManifold 𝓘(ℝ,VC) ∞ K := realManifold
  letI : LieGroup 𝓘(ℝ,VC) ∞ K := realLieGroup
  letI : IsManifold 𝓘(ℝ,Fin r → ℂ) ∞ (ComplexTorus r) := realManifold
  letI : LieGroup 𝓘(ℝ,Fin r → ℂ) ∞ (ComplexTorus r) := realLieGroup
  letI : CompleteSpace VC := FiniteDimensional.complete ℂ VC
  have hg : ContMDiff 𝓘(ℝ,Fin d → ℝ) 𝓘(ℝ,VC) ∞
      (f.comp (compactInclusion r)) := hf.comp hInc
  have hComm : ∀ z : ComplexTorus r, ∀ t : Fin r → Circle,
      Commute (f z) ((f.comp (compactInclusion r)) t) := by
    intro z t
    change f z * f (compactInclusion r t) =
      f (compactInclusion r t) * f z
    rw [← map_mul, ← map_mul]
    exact congrArg f (mul_comm z (compactInclusion r t))
  exact complex_bracket_real_derivatives_eq_zero
    f (f.comp (compactInclusion r)) hf hg hComm v w

end
end QuaternionicSymmetry.ComplexTorusCompactLieDerivativeCentralizer
