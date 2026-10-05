import QuaternionicSymmetry.QuaternionicFourFormInfinitesimal

/-! Matrix form of the tangent-induced quaternionic connection and its
infinitesimal cancellation on the Kähler-square expression. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicFourFormConnection

open Matrix QuaternionicSymmetry.ManifoldQuaternionicAdjointConnection
  QuaternionicSymmetry.ManifoldQuaternionicConnection
  QuaternionicSymmetry.ManifoldQuaternionicInducedSkew
  QuaternionicSymmetry.QuaternionicFourFormInfinitesimal
open scoped Manifold ContDiff

noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Nontrivial E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

variable (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
  (I := 𝓘(ℝ, E)) (M := M) (n := ∞))
variable (D : CompatibleTangentConnection Q)

def inducedMatrix (p : M) (y u : E) : Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j => (inducedForm Q D p y u (Pi.basisFun ℝ (Fin 3) j)) i

theorem inducedMatrix_mulVec (p : M) (y u : E) (a : Fin 3 → ℝ) :
    inducedMatrix Q D p y u *ᵥ a = inducedForm Q D p y u a := by
  funext i
  have hrepr : a = ∑ j : Fin 3, a j • Pi.basisFun ℝ (Fin 3) j := by
    simpa [Pi.basisFun_repr] using ((Pi.basisFun ℝ (Fin 3)).sum_repr a).symm
  conv_rhs => rw [hrepr]
  simp [inducedMatrix, Matrix.mulVec, dotProduct, map_sum, map_smul,
    Finset.sum_apply, mul_comm]

theorem inducedMatrix_skew (p : M) (y u : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ, E) p).target) :
    (inducedMatrix Q D p y u)ᵀ = -inducedMatrix Q D p y u := by
  ext i j
  have h := inducedForm_dot_skew Q D p y u hy
    (Pi.basisFun ℝ (Fin 3) i) (Pi.basisFun ℝ (Fin 3) j)
  simp [inducedMatrix, Matrix.transpose_apply, Pi.basisFun_apply,
    Pi.single_apply, Finset.sum_ite_eq'] at h ⊢
  linarith

theorem inducedKahlerSquare_cancel (p : M) (y u : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ, E) p).target)
    (omegaForms : Fin 3 → E [⋀^Fin 2]→L[ℝ] ℝ) :
    (∑ i : Fin 3, QuaternionicSymmetry.ContinuousWedge.wedge
      (ContinuousLinearMap.mul ℝ ℝ)
        (∑ j : Fin 3, inducedMatrix Q D p y u i j • omegaForms j) (omegaForms i)) +
      (∑ i : Fin 3, QuaternionicSymmetry.ContinuousWedge.wedge
        (ContinuousLinearMap.mul ℝ ℝ)
        (omegaForms i) (∑ j : Fin 3, inducedMatrix Q D p y u i j • omegaForms j)) = 0 :=
  sum_wedge_skew_cancel _ (inducedMatrix_skew Q D p y u hy) omegaForms

end
end QuaternionicSymmetry.ManifoldQuaternionicFourFormConnection
