import QuaternionicSymmetry.ComplexProjectiveDiagonalFamilyZeroIdeal
import QuaternionicSymmetry.ComplexTorusLaurentEvaluationInjective

/-! Extract the ordinary complex polynomial multiplying a specified
Laurent character in a polynomial family. -/

namespace QuaternionicSymmetry.ComplexProjectiveLaurentCoefficient

open ComplexProjectiveDiagonalAlgebraicCharts
open ComplexProjectiveDiagonalVanishingIdeal
open ComplexProjectiveDiagonalFamilyZeroIdeal
open ComplexTorusLaurentEvaluationInjective
open TorusLaurentRepresentation
noncomputable section

variable {r d : ℕ}

def laurentCoefficient (μ : Fin r → ℤ)
    (p : MvPolynomial (Fin (d + 1)) (TorusCoordinateRing r)) :
    MvPolynomial (Fin (d + 1)) ℂ :=
  p.sum (fun m c => MvPolynomial.monomial m (c μ))

theorem coeff_laurentCoefficient (μ : Fin r → ℤ)
    (p : MvPolynomial (Fin (d + 1)) (TorusCoordinateRing r))
    (m : Fin (d + 1) →₀ ℕ) :
    MvPolynomial.coeff m (laurentCoefficient μ p) =
      (MvPolynomial.coeff m p) μ := by
  classical
  simp only [laurentCoefficient, MvPolynomial.sum_def,
    MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]
  by_cases hm : m ∈ p.support
  · simpa [hm] using
      (Finset.sum_ite_eq' p.support m
        (fun n => (MvPolynomial.coeff n p) μ))
  · have hzero : MvPolynomial.coeff m p = 0 :=
      Finsupp.notMem_support_iff.mp hm
    simp [hm, hzero]

theorem eval_laurentCoefficient (μ : Fin r → ℤ)
    (p : MvPolynomial (Fin (d + 1)) (TorusCoordinateRing r))
    (v : Fin (d + 1) → ℂ) :
    MvPolynomial.eval v (laurentCoefficient μ p) =
      (MvPolynomial.eval₂ (RingHom.id (TorusCoordinateRing r))
        (fun i => algebraMap ℂ (TorusCoordinateRing r) (v i)) p) μ := by
  classical
  simp only [laurentCoefficient, MvPolynomial.sum_def,
    MvPolynomial.eval_sum, MvPolynomial.eval_monomial,
    MvPolynomial.eval₂_eq]
  rw [Finset.sum_apply']
  apply Finset.sum_congr rfl
  intro m hm
  simp only [RingHom.id_apply]
  have hprod :
      (∏ i ∈ m.support,
        (algebraMap ℂ (TorusCoordinateRing r)) (v i) ^ m i) =
        algebraMap ℂ (TorusCoordinateRing r)
          (m.prod fun i e => v i ^ e) := by
    change (∏ i ∈ m.support,
        (algebraMap ℂ (TorusCoordinateRing r)) (v i) ^ m i) =
      algebraMap ℂ (TorusCoordinateRing r)
        (∏ i ∈ m.support, v i ^ m i)
    rw [map_prod]
    simp only [map_pow]
  rw [hprod]
  rw [mul_comm (MvPolynomial.coeff m p)]
  rw [← Algebra.smul_def]
  rw [AddMonoidAlgebra.coeff_smul]
  simp only [smul_eq_mul]
  ring

/-- Every Laurent coefficient of a regular function vanishing on all
torus parameters and all points of the actual cone is an equation of that
cone. -/
theorem laurentCoefficient_mem_vanishingIdeal
    (A : Set (ComplexProjectiveTopology.Space d))
    (p : MvPolynomial (Fin (d + 1)) (TorusCoordinateRing r))
    (hp : p ∈ familyZeroIdeal (r := r) A)
    (μ : Fin r → ℤ) :
    laurentCoefficient μ p ∈ vanishingIdeal A := by
  rw [mem_vanishingIdeal_iff]
  intro v hv
  let q : TorusCoordinateRing r :=
    MvPolynomial.eval₂ (RingHom.id (TorusCoordinateRing r))
      (fun i => algebraMap ℂ (TorusCoordinateRing r) (v i)) p
  have hq : q = 0 := by
    apply evalTorus_joint_injective
    intro z
    have hvan := (mem_familyZeroIdeal_iff A p).mp hp z v hv
    change evalTorus z
      (MvPolynomial.eval₂ (RingHom.id (TorusCoordinateRing r))
        (fun i => algebraMap ℂ (TorusCoordinateRing r) (v i)) p) = 0
    rw [MvPolynomial.eval₂_comp_left]
    have hc : (evalTorus z).comp (algebraMap ℂ (TorusCoordinateRing r)) =
        RingHom.id ℂ := by
      ext c
      simp [evalTorus]
    have hv' : (fun i => evalTorus z
        (algebraMap ℂ (TorusCoordinateRing r) (v i))) = v := by
      funext i
      exact congrArg (fun f : ℂ →+* ℂ => f (v i)) hc
    change MvPolynomial.eval₂ (evalTorus z)
      (fun i => evalTorus z
        (algebraMap ℂ (TorusCoordinateRing r) (v i))) p = 0
    rw [hv']
    exact hvan
  rw [eval_laurentCoefficient]
  exact congrArg (fun f : TorusCoordinateRing r => f μ) hq

end
end QuaternionicSymmetry.ComplexProjectiveLaurentCoefficient
