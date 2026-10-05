import QuaternionicSymmetry.ComplexProjectiveManifold
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-! Literal homogeneous polynomial equations on the actual complex
projectivization. Their zero loci are independent of the representative. -/
namespace QuaternionicSymmetry.ComplexProjectivePolynomialLocus

open ComplexProjectiveTopology
open scoped LinearAlgebra.Projectivization
noncomputable section

theorem homogeneous_eval_smul {σ : Type*} (P : MvPolynomial σ ℂ)
    (m : ℕ) (hP : P.IsHomogeneous m) (c : ℂ) (v : σ → ℂ) :
    MvPolynomial.eval (c • v) P = c ^ m * MvPolynomial.eval v P := by
  classical
  simp only [MvPolynomial.eval_eq, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  have hdeg : (∑ i ∈ a.support, a i) = m := by
    rw [← Finsupp.degree_apply, Finsupp.degree_eq_weight_one]
    exact hP (MvPolynomial.mem_support_iff.mp ha)
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow, Finset.prod_mul_distrib]
  rw [Finset.prod_pow_eq_pow_sum, hdeg]
  ring

structure Equation (d : ℕ) where
  degree : ℕ
  polynomial : MvPolynomial (Fin (d + 1)) ℂ
  homogeneous : polynomial.IsHomogeneous degree

def Equation.Vanishes {d : ℕ} (P : Equation d) (x : Space d) : Prop :=
  MvPolynomial.eval x.rep P.polynomial = 0

theorem Equation.vanishes_mk_iff {d : ℕ} (P : Equation d)
    (v : Coord d) (hv : v ≠ 0) :
    P.Vanishes (Projectivization.mk ℂ v hv) ↔
      MvPolynomial.eval v P.polynomial = 0 := by
  obtain ⟨c,hc⟩ := Projectivization.exists_smul_eq_mk_rep ℂ v hv
  unfold Equation.Vanishes
  rw [← hc]
  change MvPolynomial.eval ((c : ℂ) • v) P.polynomial = 0 ↔ _
  rw [homogeneous_eval_smul P.polynomial P.degree P.homogeneous]
  exact mul_eq_zero_iff_left (pow_ne_zero _ c.ne_zero)

def zeroLocus {d N : ℕ} (P : Fin N → Equation d) : Set (Space d) :=
  {x | ∀ j, (P j).Vanishes x}

theorem mem_zeroLocus_mk_iff {d N : ℕ} (P : Fin N → Equation d)
    (v : Coord d) (hv : v ≠ 0) :
    Projectivization.mk ℂ v hv ∈ zeroLocus P ↔
      ∀ j, MvPolynomial.eval v (P j).polynomial = 0 := by
  simp only [zeroLocus, Set.mem_setOf_eq, Equation.vanishes_mk_iff]

/-- Algebraicity means actual finite homogeneous equations on this precise
projective space, not an opaque label on a manifold. -/
def HasHomogeneousEquations {d : ℕ} (A : Set (Space d)) : Prop :=
  ∃ (N : ℕ) (P : Fin N → Equation d), A = zeroLocus P

end
end QuaternionicSymmetry.ComplexProjectivePolynomialLocus
