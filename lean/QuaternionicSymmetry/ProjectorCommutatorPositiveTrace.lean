import QuaternionicSymmetry.ProjectorCommutatorBilinearBasis

/-! A nonzero tangent commutator makes the full finite orthonormal-basis
Frobenius curvature contraction strictly positive: every term is a square,
and bilinearity forces one basis-pair square to be nonzero. -/

namespace QuaternionicSymmetry.ProjectorCommutatorPositiveTrace

open Matrix
open CompactSymplecticProjectorAmbientMetric
open ProjectorPeirceCurvatureBracket
open ProjectorCommutatorBilinearBasis
open scoped Matrix.Norms.Operator
noncomputable section

private abbrev I (n : ℕ) := Fin (n + 1) ⊕ Fin (n + 1)
private abbrev Mat (n : ℕ) := Matrix (I n) (I n) ℂ

theorem commutator_square_double_sum_pos {E ι : Type*}
    [Fintype ι] [DecidableEq ι]
    [AddCommGroup E] [Module ℝ E]
    (n : ℕ) (T : E →ₗ[ℝ] Mat n) (b : Module.Basis ι ℝ E)
    (h : ∃ u v : E,
      ProjectorPeirceCurvatureBracket.commutator (T u) (T v) ≠ 0) :
    0 < ∑ i : ι, ∑ j : ι,
      frobeniusPairing n
        (ProjectorPeirceCurvatureBracket.commutator (T (b i)) (T (b j)))
        (ProjectorPeirceCurvatureBracket.commutator (T (b i)) (T (b j))) := by
  obtain ⟨i, j, hij⟩ := exists_basis_noncommuting n T b h
  apply Finset.sum_pos' (fun k _ => Finset.sum_nonneg fun l _ =>
    frobeniusPairing_self_nonneg n _)
  refine ⟨i, Finset.mem_univ _, ?_⟩
  apply Finset.sum_pos' (fun l _ => frobeniusPairing_self_nonneg n _)
  exact ⟨j, Finset.mem_univ _, by
    simpa only [frobeniusCLM_apply] using frobeniusCLM_pos n _ hij⟩

end
end QuaternionicSymmetry.ProjectorCommutatorPositiveTrace
