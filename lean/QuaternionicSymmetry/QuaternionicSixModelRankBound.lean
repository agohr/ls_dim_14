import QuaternionicSymmetry.QuaternionicTwoSixNormalizedBounds

/-! A dimension-six bound with a variable matrix rank, so an actual model
indexed by its quaternionic dimension can specialize without rewriting the
unrelated six polynomial variables. -/
namespace QuaternionicSymmetry.QuaternionicSixModelRankBound
open Module MvPolynomial QuaternionicFundamental QuaternionicTracePositivity
open PrintedProjectionCubicPositivity QuaternionicNormalizedDensityValues
open QuaternionicTwoSixNormalizedBounds ReconstructionExamples
noncomputable section

variable {ι β V : Type*} [Fintype ι] [Fintype β] [DecidableEq β]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

theorem density6_lower_bound_normalized_model
    (rank : ℕ) (hrank : rank = 6)
    (Q : QuaternionicStructure V) (b : Basis ι ℝ V)
    (hn : Q.quaternionicDimension = rank) (s : ℝ) (hs : 0 < s)
    (B : β → Matrix (Fin rank ⊕ Fin rank) (Fin rank ⊕ Fin rank) ℂ)
    (hB : ∀ a, (B a).IsHermitian)
    (η : β → E V) (hη : ∀ a, η a ∈ HyperholomorphicExterior.formSpace Q b)
    (L : CE V →ₗ[ℝ] ℝ) (hL : 0 ≤ L (embed (V := V) (topForm Q b))) :
    96 * L ((s ^ 2 • embed (V := V) (form Q b)) ^ 6) ≤
      L (aeval (normalizedValues Q b s B η) k6) := by
  subst rank
  exact density6_lower_bound_normalized Q b hn s hs B hB η hη L hL

end
end QuaternionicSymmetry.QuaternionicSixModelRankBound
