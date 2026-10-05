import QuaternionicSymmetry.ComplexProjectiveDiagonalChartVanishingIdeal
import QuaternionicSymmetry.ComplexTorusLaurentPolynomialEvaluation

/-! The joint vanishing ideal on torus × an actual invariant standard
projective chart is exactly the Laurent extension of that chart's
complex-polynomial vanishing ideal. -/

namespace QuaternionicSymmetry.ComplexProjectiveDiagonalChartIdealDescent

open ComplexProjectiveTopology
open ComplexProjectiveDiagonalAlgebraicCharts
open ComplexProjectiveDiagonalChartLocus
open ComplexProjectiveDiagonalChartVanishingIdeal
open ComplexTorusLaurentPolynomialReconstruction
open ComplexTorusLaurentPolynomialEvaluation
open ComplexTorusLaurentEvaluationInjective
open TorusLaurentRepresentation
noncomputable section

variable {r d : ℕ}

def chartFamilyZeroIdeal (A : Set (Space d)) (i : Fin (d + 1)) :
    Ideal (MvPolynomial (Fin d) (TorusCoordinateRing r)) :=
  ⨅ z : ComplexTorus r,
    ⨅ w : chartLocus A i,
      RingHom.ker (MvPolynomial.eval₂Hom (evalTorus z) w.1)

theorem mem_chartFamilyZeroIdeal_iff (A : Set (Space d))
    (i : Fin (d + 1))
    (p : MvPolynomial (Fin d) (TorusCoordinateRing r)) :
    p ∈ chartFamilyZeroIdeal (r := r) A i ↔
      ∀ z : ComplexTorus r, ∀ w : Fin d → ℂ,
        w ∈ chartLocus A i →
          MvPolynomial.eval₂ (evalTorus z) w p = 0 := by
  simp [chartFamilyZeroIdeal]

def chartBaseChange : MvPolynomial (Fin d) ℂ →+*
    MvPolynomial (Fin d) (TorusCoordinateRing r) :=
  MvPolynomial.map (algebraMap ℂ (TorusCoordinateRing r))

def extendedChartIdeal (A : Set (Space d)) (i : Fin (d + 1)) :
    Ideal (MvPolynomial (Fin d) (TorusCoordinateRing r)) :=
  Ideal.map (chartBaseChange (r := r)) (chartVanishingIdeal A i)

theorem coefficient_mem_chartVanishingIdeal
    (A : Set (Space d)) (i : Fin (d + 1))
    (p : MvPolynomial (Fin d) (TorusCoordinateRing r))
    (hp : p ∈ chartFamilyZeroIdeal (r := r) A i)
    (ν : Fin r → ℤ) :
    coefficient ν p ∈ chartVanishingIdeal A i := by
  rw [mem_chartVanishingIdeal_iff]
  intro w hw
  let q : TorusCoordinateRing r :=
    MvPolynomial.eval₂ (RingHom.id (TorusCoordinateRing r))
      (fun i => algebraMap ℂ (TorusCoordinateRing r) (w i)) p
  have hq : q = 0 := by
    apply evalTorus_joint_injective
    intro z
    have hvan := (mem_chartFamilyZeroIdeal_iff A i p).mp hp z w hw
    change evalTorus z
      (MvPolynomial.eval₂ (RingHom.id (TorusCoordinateRing r))
        (fun i => algebraMap ℂ (TorusCoordinateRing r) (w i)) p) = 0
    rw [MvPolynomial.eval₂_comp_left]
    have hc : (evalTorus z).comp (algebraMap ℂ (TorusCoordinateRing r)) =
        RingHom.id ℂ := by
      ext c
      simp [evalTorus]
    have hw' : (fun i => evalTorus z
        (algebraMap ℂ (TorusCoordinateRing r) (w i))) = w := by
      funext i
      exact congrArg (fun f : ℂ →+* ℂ => f (w i)) hc
    change MvPolynomial.eval₂ (evalTorus z)
      (fun i => evalTorus z
        (algebraMap ℂ (TorusCoordinateRing r) (w i))) p = 0
    rw [hw']
    exact hvan
  rw [eval_coefficient]
  exact congrArg (fun f : TorusCoordinateRing r => f ν) hq

theorem chartFamilyZeroIdeal_le_extendedChartIdeal
    (A : Set (Space d)) (i : Fin (d + 1)) :
    chartFamilyZeroIdeal (r := r) A i ≤ extendedChartIdeal (r := r) A i := by
  intro p hp
  rw [reconstruct p]
  apply Ideal.sum_mem
  intro ν hν
  exact Ideal.mul_mem_left _ _
    (Ideal.mem_map_of_mem (chartBaseChange (r := r))
      (coefficient_mem_chartVanishingIdeal A i p hp ν))

theorem extendedChartIdeal_le_chartFamilyZeroIdeal
    (A : Set (Space d)) (i : Fin (d + 1)) :
    extendedChartIdeal (r := r) A i ≤ chartFamilyZeroIdeal (r := r) A i := by
  apply (Ideal.map_le_iff_le_comap).mpr
  intro p hp
  rw [Ideal.mem_comap, mem_chartFamilyZeroIdeal_iff]
  intro z w hw
  change MvPolynomial.eval₂ (evalTorus z) w
    (MvPolynomial.map (algebraMap ℂ (TorusCoordinateRing r)) p) = 0
  rw [MvPolynomial.eval₂_map]
  have hc : (evalTorus z).comp (algebraMap ℂ (TorusCoordinateRing r)) =
      RingHom.id ℂ := by
    ext c
    simp [evalTorus]
  rw [hc]
  simpa using (mem_chartVanishingIdeal_iff A i p).mp hp w hw

theorem chartFamilyZeroIdeal_eq_extendedChartIdeal
    (A : Set (Space d)) (i : Fin (d + 1)) :
    chartFamilyZeroIdeal (r := r) A i = extendedChartIdeal (r := r) A i :=
  le_antisymm (chartFamilyZeroIdeal_le_extendedChartIdeal A i)
    (extendedChartIdeal_le_chartFamilyZeroIdeal A i)

end
end QuaternionicSymmetry.ComplexProjectiveDiagonalChartIdealDescent
