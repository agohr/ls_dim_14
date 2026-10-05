import QuaternionicSymmetry.ComplexProjectiveLaurentCoefficient

/-! Finite reconstruction of a Laurent-parameter polynomial family from
its ordinary complex-polynomial Laurent coefficients. -/

namespace QuaternionicSymmetry.ComplexProjectiveLaurentReconstruction

open ComplexProjectiveDiagonalAlgebraicCharts
open ComplexProjectiveLaurentCoefficient
noncomputable section

variable {r d : ℕ}

def weightSupport
    (p : MvPolynomial (Fin (d + 1)) (TorusCoordinateRing r)) :
    Finset (Fin r → ℤ) :=
  p.support.biUnion (fun m => (MvPolynomial.coeff m p).support)

theorem coefficient_support_subset_weightSupport
    (p : MvPolynomial (Fin (d + 1)) (TorusCoordinateRing r))
    (m : Fin (d + 1) →₀ ℕ) :
    (MvPolynomial.coeff m p).support ⊆ weightSupport p := by
  intro μ hμ
  have hm : m ∈ p.support := by
    by_contra h
    have hz : MvPolynomial.coeff m p = 0 :=
      Finsupp.notMem_support_iff.mp h
    simp [hz] at hμ
  exact Finset.mem_biUnion.mpr ⟨m, hm, hμ⟩

theorem sum_single_weightSupport
    (p : MvPolynomial (Fin (d + 1)) (TorusCoordinateRing r))
    (m : Fin (d + 1) →₀ ℕ) :
    (∑ μ ∈ weightSupport p,
      AddMonoidAlgebra.single μ ((MvPolynomial.coeff m p) μ)) =
        MvPolynomial.coeff m p := by
  let c := MvPolynomial.coeff m p
  calc
    (∑ μ ∈ weightSupport p, AddMonoidAlgebra.single μ (c μ)) =
        c.sum AddMonoidAlgebra.single := by
      symm
      exact c.sum_of_support_subset (coefficient_support_subset_weightSupport p m)
        _ (by intro μ h; simp)
    _ = c := AddMonoidAlgebra.sum_single c

theorem reconstruct
    (p : MvPolynomial (Fin (d + 1)) (TorusCoordinateRing r)) :
    p = ∑ μ ∈ weightSupport p,
      MvPolynomial.C (laurentMonomial μ) *
        MvPolynomial.map (algebraMap ℂ (TorusCoordinateRing r))
          (laurentCoefficient μ p) := by
  classical
  apply MvPolynomial.ext
  intro m
  simp only [MvPolynomial.coeff_sum, MvPolynomial.coeff_C_mul,
    MvPolynomial.coeff_map, coeff_laurentCoefficient]
  simp only [laurentMonomial]
  have hterm (μ : Fin r → ℤ) :
      AddMonoidAlgebra.single μ 1 *
        algebraMap ℂ (TorusCoordinateRing r) ((MvPolynomial.coeff m p) μ) =
          AddMonoidAlgebra.single μ ((MvPolynomial.coeff m p) μ) := by
    change AddMonoidAlgebra.single μ 1 *
        AddMonoidAlgebra.single 0 ((MvPolynomial.coeff m p) μ) = _
    simp
  simp_rw [hterm]
  exact (sum_single_weightSupport p m).symm

end
end QuaternionicSymmetry.ComplexProjectiveLaurentReconstruction
