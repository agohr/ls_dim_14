import QuaternionicSymmetry.GeneralEquivariantWeightSpace
import QuaternionicSymmetry.TorusWeightSeparation
import Mathlib.LinearAlgebra.Basis.Defs
import QuaternionicSymmetry.ExtremeWeightsSpanTransfer
import QuaternionicSymmetry.TorusIntegralVertexExposure

/-! A nonzero eigenspace of an actual integral-character eigenbasis has
one of its literal basis weights. This prevents occurrence adapters from
silently replacing the selected representation. -/
namespace QuaternionicSymmetry.IntegralEigenbasisWeightOccurrence
open GeneralEquivariantWeightSpace TorusWeightSeparation ManifoldQuaternionicTorusAction
noncomputable section
variable {r : ℕ} {V ι : Type*} [AddCommGroup V] [Module ℂ V] [Fintype ι]

theorem weight_mem_range_of_ne_bot
    (ρ : Torus r → V →ₗ[ℂ] V) (b : Module.Basis ι ℂ V)
    (μ : ι → Fin r → ℤ)
    (hEig : ∀ t i, ρ t (b i) = (weightCharacter (μ i) t : ℂ) • b i)
    (ν : Fin r → ℤ)
    (hW : weightSubmodule ρ (fun t => (weightCharacter ν t : ℂ)) ≠ ⊥) :
    ν ∈ Set.range μ := by
  classical
  obtain ⟨v,hv,hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW
  have hrepr : b.repr v ≠ 0 := fun h => hv0 (b.repr.injective (by simpa using h))
  have hex : ∃ j, b.repr v j ≠ 0 := by
    by_contra h
    apply hrepr
    ext j
    simpa using not_exists_not.mp h j
  obtain ⟨j,hj⟩ := hex
  refine ⟨j, TorusWeightSeparation.weight_eq_of_character_eq ?_⟩
  intro t
  apply Subtype.ext
  have he := congrArg (fun w => b.repr w j) (hv t)
  have hcoeff : b.repr (ρ t v) j =
      (weightCharacter (μ j) t : ℂ) * b.repr v j := by
    have hexp : ρ t v = ∑ i, b.repr v i • (ρ t (b i)) := by
      calc
        ρ t v = ρ t (∑ i, b.repr v i • b i) := congrArg (ρ t) (b.sum_repr v).symm
        _ = ∑ i, b.repr v i • (ρ t (b i)) := by simp only [map_sum, map_smul]
    rw [hexp]
    simp [hEig, mul_comm, Finsupp.sum_apply, Finsupp.single_apply]
  dsimp only at he
  rw [hcoeff] at he
  simp only [map_smul, Finsupp.smul_apply, smul_eq_mul] at he
  exact mul_right_cancel₀ hj he

/-- The same eigenbasis spans in real character coordinates once every
vertex of a finite full-spanning geometric polytope occurs in its actual
weight spaces. No dimension bound or zero centre is involved. -/
theorem real_weight_span_of_extremal_occurrence
    (ρ : Torus r → V →ₗ[ℂ] V) (b : Module.Basis ι ℂ V)
    (μ : ι → Fin r → ℤ)
    (hEig : ∀ t i, ρ t (b i) = (weightCharacter (μ i) t : ℂ) • b i)
    (W : Set (Fin r → ℝ)) (hFinite : W.Finite)
    (hSpan : Submodule.span ℝ W = ⊤)
    (hVertices : ∀ w ∈ (convexHull ℝ W).extremePoints ℝ,
      ∃ ν : Fin r → ℤ, TorusIntegralVertexExposure.realWeight ν = w ∧
        weightSubmodule ρ (fun t => (weightCharacter ν t : ℂ)) ≠ ⊥) :
    Submodule.span ℝ (Set.range (fun i => TorusIntegralVertexExposure.realWeight (μ i))) = ⊤ := by
  apply ExtremeWeightsSpanTransfer.span_eq_top_of_finite_extremeWeights_subset hFinite hSpan
  intro w hw
  obtain ⟨ν,hν,hW⟩ := hVertices w hw
  obtain ⟨i,hi⟩ := weight_mem_range_of_ne_bot ρ b μ hEig ν hW
  refine ⟨i,?_⟩
  change TorusIntegralVertexExposure.realWeight (μ i) = w
  rw [hi]
  exact hν

end
end QuaternionicSymmetry.IntegralEigenbasisWeightOccurrence
