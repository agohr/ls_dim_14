import Mathlib.Tactic

/-! A bilinear map nonzero on some pair is nonzero on a pair from every
genuine basis. This is the algebraic step needed to turn one positive
curvature plane and nonnegative curvature squares into positive scalar trace. -/

namespace QuaternionicSymmetry.FiniteBilinearBasisWitness

variable {ι E V : Type*}
  [AddCommGroup E] [Module ℝ E]
  [AddCommGroup V] [Module ℝ V]

theorem exists_basis_pair_nonzero (b : Module.Basis ι ℝ E)
    (L : E →ₗ[ℝ] E →ₗ[ℝ] V)
    (h : ∃ u v : E, L u v ≠ 0) :
    ∃ i j : ι, L (b i) (b j) ≠ 0 := by
  by_contra hnone
  have hpair (i j : ι) : L (b i) (b j) = 0 := by
    by_contra hne
    exact hnone ⟨i, j, hne⟩
  have hL : L = 0 := b.ext fun i => b.ext fun j => hpair i j
  rcases h with ⟨u, v, huv⟩
  exact huv (by rw [hL]; simp)

end QuaternionicSymmetry.FiniteBilinearBasisWitness
