import QuaternionicSymmetry.AbelianLieSpanSubalgebra
import QuaternionicSymmetry.ComplexGroupLieBracketRestriction
import QuaternionicSymmetry.ComplexLieRealCompanion
import QuaternionicSymmetry.ManifoldQuaternionicTorusAction

/-! The complex span of the actual differential image of a real-smooth
compact-torus homomorphism in a genuine complex Lie group is an abelian
Lie subalgebra. This does not claim Cartan, maximality, or a root system. -/

namespace QuaternionicSymmetry.ComplexLieToralDifferentialSubalgebra

open AbelianLieSpanSubalgebra
open ComplexGroupLieBracketRestriction ComplexLieRealCompanion
open ManifoldQuaternionicTorusAction
open scoped Manifold ContDiff
noncomputable section

variable {V K : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [FiniteDimensional ℂ V]
  [Group K] [TopologicalSpace K] [ChartedSpace V K]
  [IsManifold 𝓘(ℂ,V) ∞ K] [LieGroup 𝓘(ℂ,V) ∞ K]
  {r d : ℕ}
  (ρ : Torus r →* K)
  (hChart : ChartedSpace (Fin d → ℝ) (Torus r))
  (hManifold : letI := hChart
    IsManifold 𝓘(ℝ,Fin d → ℝ) ∞ (Torus r))
  (hLie : letI := hChart
    LieGroup 𝓘(ℝ,Fin d → ℝ) ∞ (Torus r))
  (hSmooth : letI := hChart
    ContMDiff 𝓘(ℝ,Fin d → ℝ) 𝓘(ℝ,V) ∞ ρ)

local instance complexMin : ENat.LEInfty (minSmoothness ℂ 3) := by
  simpa only [minSmoothness_of_isRCLikeNormedField] using
    (inferInstance : ENat.LEInfty (3 : WithTop ℕ∞))

/-- Literal generator set in the SAME complex Lie algebra model `V`. -/
def differentialGenerators : Set (GroupLieAlgebra 𝓘(ℂ,V) K) := by
  letI : ChartedSpace (Fin d → ℝ) (Torus r) := hChart
  exact Set.range (fun w : GroupLieAlgebra 𝓘(ℝ,Fin d → ℝ) (Torus r) =>
    mfderiv 𝓘(ℝ,Fin d → ℝ) 𝓘(ℝ,V) ρ 1 w)

include hManifold hLie hSmooth

theorem differentialGenerators_bracket_zero
    {x y : GroupLieAlgebra 𝓘(ℂ,V) K}
    (hx : x ∈ differentialGenerators ρ hChart)
    (hy : y ∈ differentialGenerators ρ hChart) : ⁅x,y⁆ = 0 := by
  letI : ChartedSpace (Fin d → ℝ) (Torus r) := hChart
  letI : IsManifold 𝓘(ℝ,Fin d → ℝ) ∞ (Torus r) := hManifold
  letI : LieGroup 𝓘(ℝ,Fin d → ℝ) ∞ (Torus r) := hLie
  letI : IsManifold 𝓘(ℝ,V) ∞ K := realManifold
  letI : LieGroup 𝓘(ℝ,V) ∞ K := realLieGroup
  letI : CompleteSpace V := FiniteDimensional.complete ℂ V
  obtain ⟨u, rfl⟩ := hx
  obtain ⟨w, rfl⟩ := hy
  apply complex_bracket_real_derivatives_eq_zero ρ ρ hSmooth hSmooth
  · intro a b
    change ρ a * ρ b = ρ b * ρ a
    rw [← map_mul, ← map_mul]
    exact congrArg ρ (mul_comm a b)

/-- The selected torus differential generates a genuine abelian complex
Lie subalgebra; no maximality of the torus in `K` is needed. -/
def toralLieSubalgebra : LieSubalgebra ℂ (GroupLieAlgebra 𝓘(ℂ,V) K) :=
  AbelianLieSpanSubalgebra.lieSubalgebra
    (differentialGenerators ρ hChart)
    (fun x hx y hy => differentialGenerators_bracket_zero
      ρ hChart hManifold hLie hSmooth hx hy)

theorem toralLieSubalgebra_abelian
    (x y : toralLieSubalgebra ρ hChart hManifold hLie hSmooth) :
    ⁅(x : GroupLieAlgebra 𝓘(ℂ,V) K), (y : GroupLieAlgebra 𝓘(ℂ,V) K)⁆ = 0 :=
  AbelianLieSpanSubalgebra.lieSubalgebra_abelian _ _ x y

end
end QuaternionicSymmetry.ComplexLieToralDifferentialSubalgebra
