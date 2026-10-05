import QuaternionicSymmetry.ManifoldQuaternionicInducedSkew

/-! Infinitesimal orthogonal cancellation for sums of bilinear squares. -/

namespace QuaternionicSymmetry.QuaternionicFourFormInfinitesimal

open Matrix

theorem sum_bilinear_skew_cancel {V W : Type*}
    [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
    (B : V →ₗ[ℝ] V →ₗ[ℝ] W)
    (A : Matrix (Fin 3) (Fin 3) ℝ) (hA : Aᵀ = -A)
    (ω : Fin 3 → V) :
    (∑ i : Fin 3, B (∑ j : Fin 3, A i j • ω j) (ω i)) +
      (∑ i : Fin 3, B (ω i) (∑ j : Fin 3, A i j • ω j)) = 0 := by
  have hskew (i j : Fin 3) : A j i = -A i j := by
    have h := congrArg (fun T : Matrix (Fin 3) (Fin 3) ℝ => T i j) hA
    simpa only [transpose_apply, neg_apply] using h
  simp only [map_sum, map_smul, LinearMap.sum_apply,
    LinearMap.smul_apply]
  have hswap :
      (∑ i : Fin 3, ∑ j : Fin 3, A i j • B (ω i) (ω j)) =
      ∑ i : Fin 3, ∑ j : Fin 3, A j i • B (ω j) (ω i) := by
    rw [Finset.sum_comm]
  rw [hswap, ← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro i _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro j _
  rw [hskew i j]
  simp

theorem sum_wedge_skew_cancel {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : Matrix (Fin 3) (Fin 3) ℝ) (hA : Aᵀ = -A)
    (ω : Fin 3 → E [⋀^Fin 2]→L[ℝ] ℝ) :
    (∑ i : Fin 3, QuaternionicSymmetry.ContinuousWedge.wedge
      (ContinuousLinearMap.mul ℝ ℝ)
        (∑ j : Fin 3, A i j • ω j) (ω i)) +
      (∑ i : Fin 3, QuaternionicSymmetry.ContinuousWedge.wedge
        (ContinuousLinearMap.mul ℝ ℝ)
        (ω i) (∑ j : Fin 3, A i j • ω j)) = 0 := by
  exact sum_bilinear_skew_cancel
    (QuaternionicSymmetry.ContinuousWedge.wedgeLinear
      (E := E) (p := 2) (q := 2) (ContinuousLinearMap.mul ℝ ℝ))
    A hA ω

end QuaternionicSymmetry.QuaternionicFourFormInfinitesimal
