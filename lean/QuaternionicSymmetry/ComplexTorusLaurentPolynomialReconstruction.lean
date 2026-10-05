import QuaternionicSymmetry.ComplexProjectiveLaurentReconstruction

/-! Index-type-generic Laurent coefficient extraction and finite
reconstruction for polynomial families. The projective chart variables
have type `Fin d`, rather than the homogeneous variables `Fin (d+1)`. -/

namespace QuaternionicSymmetry.ComplexTorusLaurentPolynomialReconstruction

open ComplexProjectiveDiagonalAlgebraicCharts
noncomputable section

variable {r : ℕ} {σ : Type*}

def coefficient (ν : Fin r → ℤ)
    (p : MvPolynomial σ (TorusCoordinateRing r)) : MvPolynomial σ ℂ :=
  p.sum (fun m c => MvPolynomial.monomial m (c ν))

theorem coeff_coefficient (ν : Fin r → ℤ)
    (p : MvPolynomial σ (TorusCoordinateRing r)) (m : σ →₀ ℕ) :
    MvPolynomial.coeff m (coefficient ν p) = (MvPolynomial.coeff m p) ν := by
  classical
  simp only [coefficient, MvPolynomial.sum_def,
    MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]
  by_cases hm : m ∈ p.support
  · simpa [hm] using
      (Finset.sum_ite_eq' p.support m
        (fun n => (MvPolynomial.coeff n p) ν))
  · have hzero : MvPolynomial.coeff m p = 0 :=
      Finsupp.notMem_support_iff.mp hm
    simp [hm, hzero]

def weightSupport (p : MvPolynomial σ (TorusCoordinateRing r)) :
    Finset (Fin r → ℤ) :=
  p.support.biUnion (fun m => (MvPolynomial.coeff m p).support)

theorem coefficient_support_subset_weightSupport
    (p : MvPolynomial σ (TorusCoordinateRing r)) (m : σ →₀ ℕ) :
    (MvPolynomial.coeff m p).support ⊆ weightSupport p := by
  intro ν hν
  have hm : m ∈ p.support := by
    by_contra h
    have hz : MvPolynomial.coeff m p = 0 :=
      Finsupp.notMem_support_iff.mp h
    simp [hz] at hν
  exact Finset.mem_biUnion.mpr ⟨m, hm, hν⟩

theorem sum_single_weightSupport
    (p : MvPolynomial σ (TorusCoordinateRing r)) (m : σ →₀ ℕ) :
    (∑ ν ∈ weightSupport p,
      AddMonoidAlgebra.single ν ((MvPolynomial.coeff m p) ν)) =
        MvPolynomial.coeff m p := by
  let c := MvPolynomial.coeff m p
  calc
    (∑ ν ∈ weightSupport p, AddMonoidAlgebra.single ν (c ν)) =
        c.sum AddMonoidAlgebra.single := by
      symm
      exact c.sum_of_support_subset (coefficient_support_subset_weightSupport p m)
        _ (by intro ν h; simp)
    _ = c := AddMonoidAlgebra.sum_single c

theorem reconstruct (p : MvPolynomial σ (TorusCoordinateRing r)) :
    p = ∑ ν ∈ weightSupport p,
      MvPolynomial.C (laurentMonomial ν) *
        MvPolynomial.map (algebraMap ℂ (TorusCoordinateRing r))
          (coefficient ν p) := by
  classical
  apply MvPolynomial.ext
  intro m
  simp only [MvPolynomial.coeff_sum, MvPolynomial.coeff_C_mul,
    MvPolynomial.coeff_map, coeff_coefficient]
  simp only [laurentMonomial]
  have hterm (ν : Fin r → ℤ) :
      AddMonoidAlgebra.single ν 1 *
        algebraMap ℂ (TorusCoordinateRing r) ((MvPolynomial.coeff m p) ν) =
          AddMonoidAlgebra.single ν ((MvPolynomial.coeff m p) ν) := by
    change AddMonoidAlgebra.single ν 1 *
        AddMonoidAlgebra.single 0 ((MvPolynomial.coeff m p) ν) = _
    simp
  simp_rw [hterm]
  exact (sum_single_weightSupport p m).symm

end
end QuaternionicSymmetry.ComplexTorusLaurentPolynomialReconstruction
