import QuaternionicSymmetry.QuaternionicStandardTraceProduct

/-! Every positive trace power of the standard infinitesimal representation
splits into its quaternionic tangent and extra quaternionic-line blocks. -/
namespace QuaternionicSymmetry.QuaternionicStandardTracePowers
open QuaternionicProjectiveStandardLie QuaternionicProjectiveStandardL2
  QuaternionicLieAlgebraProjection LocalEndomorphismTrace
open scoped Quaternion
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  (S : QuaternionicStructure E) (A : E →L[ℝ] E)

private theorem standardLie_pow_blocks (j : ℕ)
    (z : StandardSpace (E := E)) :
    (WithLp.prodContinuousLinearEquiv 2 ℝ E ℍ) (((standardLie S A) ^ j) z) =
      (((symplecticProjection S A) ^ j)
          ((WithLp.prodContinuousLinearEquiv 2 ℝ E ℍ) z).1,
       ((scalarLineLie S A) ^ j)
          ((WithLp.prodContinuousLinearEquiv 2 ℝ E ℍ) z).2) := by
  induction j generalizing z with
  | zero =>
      cases z
      rfl
  | succ j ih =>
      rw [pow_succ, ContinuousLinearMap.mul_apply,
        ih (standardLie S A z), standardLie_blocks]
      simp [pow_succ, ContinuousLinearMap.mul_apply]

theorem standardLie_pow_trace (j : ℕ) :
    traceCLM ((standardLie S A) ^ j) =
      traceCLM ((symplecticProjection S A) ^ j) +
        traceCLM ((scalarLineLie S A) ^ j) := by
  let c := WithLp.prodContinuousLinearEquiv 2 ℝ E ℍ
  have hblock :
      c.toLinearEquiv.conj (((standardLie S A) ^ j).toLinearMap) =
        LinearMap.prodMap
          (((symplecticProjection S A) ^ j).toLinearMap)
          (((scalarLineLie S A) ^ j).toLinearMap) := by
    apply LinearMap.ext
    intro z
    apply Prod.ext
    · exact congrArg Prod.fst (standardLie_pow_blocks S A j (c.symm z))
    · exact congrArg Prod.snd (standardLie_pow_blocks S A j (c.symm z))
  have htrace := LinearMap.trace_conj'
    (((standardLie S A) ^ j).toLinearMap) c.toLinearEquiv
  rw [hblock, LinearMap.trace_prodMap'] at htrace
  exact htrace.symm

end
end QuaternionicSymmetry.QuaternionicStandardTracePowers
