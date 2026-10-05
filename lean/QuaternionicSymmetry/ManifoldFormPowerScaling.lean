import QuaternionicSymmetry.ManifoldFormPowers

/-! Exact scaling of normalized wedge powers of manifold forms. -/
namespace QuaternionicSymmetry.ManifoldFormPowers
open ManifoldDifferentialForms ManifoldDeRhamWedge
open scoped Manifold ContDiff
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] {d : ℕ}

theorem formPower_smul (c : ℝ) (α : Form 𝓘(ℝ,E) M d) (n : ℕ) :
    formPower (c • α) n = c^n • formPower α n := by
  induction n with
  | zero => simp [formPower]
  | succ n ih =>
    simp only [formPower, ih, formWedge_smul_left, formWedge_smul_right,
      smul_smul, castForm_smul, pow_succ, mul_comm]

end QuaternionicSymmetry.ManifoldFormPowers
