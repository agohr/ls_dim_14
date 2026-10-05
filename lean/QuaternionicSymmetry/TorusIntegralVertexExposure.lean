import QuaternionicSymmetry.TorusRationalConeIntegralPoint
import QuaternionicSymmetry.TorusIntegralCocharacter
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Convex.Topology

/-! An extreme point of the convex hull of a finite family of integral torus
weights is uniquely exposed, up to repeated equal weights, by an integral
cocharacter. All separation and rational approximation are internal. -/

namespace QuaternionicSymmetry.TorusIntegralVertexExposure

open Set TorusIntegralCocharacter TorusRationalConeIntegralPoint
open scoped BigOperators
noncomputable section

variable {r : ℕ} {ι : Type*} [Fintype ι]

def realWeight (μ : Fin r → ℤ) : Fin r → ℝ := fun i => (μ i : ℝ)

private def realPairing (μ : Fin r → ℤ) (u : Fin r → ℝ) : ℝ :=
  ∑ i : Fin r, (μ i : ℝ) * u i

private theorem realPairing_continuous (μ : Fin r → ℤ) :
    Continuous (realPairing μ) := by
  unfold realPairing
  fun_prop

private theorem realPairing_smul (μ : Fin r → ℤ) (a : ℝ) (u : Fin r → ℝ) :
    realPairing μ (a • u) = a * realPairing μ u := by
  simp [realPairing, Finset.mul_sum, mul_comm, mul_assoc]

private theorem realPairing_int (μ u : Fin r → ℤ) :
    realPairing μ (fun i => (u i : ℝ)) = (pairing μ u : ℝ) := by
  simp [realPairing, pairing]

private theorem functional_realPairing
    (f : (Fin r → ℝ) →L[ℝ] ℝ) (μ : Fin r → ℤ) :
    f (realWeight μ) =
      realPairing μ (fun i => f (Pi.single i (1 : ℝ))) := by
  let x := realWeight μ
  calc
    f x = f (∑ i : Fin r, Pi.single i (x i)) := by
      have hsum : (∑ i : Fin r, Pi.single i (x i)) = x := by
        ext j
        simp [Pi.single_apply]
      exact congrArg f hsum.symm
    _ = ∑ i : Fin r, f (Pi.single i (x i)) := map_sum f _ _
    _ = ∑ i : Fin r, (μ i : ℝ) * f (Pi.single i (1 : ℝ)) := by
      apply Finset.sum_congr rfl
      intro i hi
      have hs : (Pi.single i (x i) : Fin r → ℝ) =
          (x i) • (Pi.single i (1 : ℝ) : Fin r → ℝ) := by
        ext j
        by_cases hji : j = i <;> simp [Pi.single_apply, hji, x]
      rw [hs, map_smul]
      rfl
    _ = realPairing μ (fun i => f (Pi.single i (1 : ℝ))) := rfl

theorem exists_integral_exposing_cocharacter
    (μ : ι → Fin r → ℤ) (j : ι)
    (hj : realWeight (μ j) ∈
      (convexHull ℝ (Set.range (fun i => realWeight (μ i)))).extremePoints ℝ) :
    ∃ u : Fin r → ℤ,
      (∀ i, pairing (μ j) u ≤ pairing (μ i) u) ∧
      ∀ i, pairing (μ i) u = pairing (μ j) u → μ i = μ j := by
  classical
  let W : Set (Fin r → ℝ) := Set.range (fun i => realWeight (μ i))
  let x := realWeight (μ j)
  have hNot : x ∉ convexHull ℝ (W \ {x}) := by
    have hh := ((convex_convexHull ℝ W).mem_extremePoints_iff_mem_diff_convexHull_diff.mp hj).2
    exact fun hx => hh (convexHull_mono (diff_subset_diff_left (subset_convexHull ℝ W)) hx)
  have hClosed : IsClosed (convexHull ℝ (W \ {x})) := by
    exact (Set.toFinite (W \ {x})).isCompact_convexHull.isClosed
  obtain ⟨f,c,hfc,hcf⟩ :=
    geometric_hahn_banach_point_closed
      (convex_convexHull ℝ (W \ {x})) hClosed hNot
  let a : Fin r → ℝ := fun k => f (Pi.single k (1 : ℝ))
  let U : Set (Fin r → ℝ) :=
    {u | ∀ i, μ i ≠ μ j → realPairing (μ j) u < realPairing (μ i) u}
  have hOpen : IsOpen U := by
    simp only [U, Set.setOf_forall]
    apply isOpen_iInter_of_finite
    intro i
    by_cases hi : μ i = μ j
    · simp [hi]
    · simpa [hi] using isOpen_lt (realPairing_continuous (μ j))
        (realPairing_continuous (μ i))
  have ha : a ∈ U := by
    intro i hi
    have hOther : realWeight (μ i) ∈ W \ {x} := by
      refine ⟨⟨i,rfl⟩, ?_⟩
      intro he
      apply hi
      funext k
      have hk : ((μ i k : ℤ) : ℝ) = ((μ j k : ℤ) : ℝ) := congrFun he k
      exact_mod_cast hk
    have hSep := lt_trans hfc (hcf _ (subset_convexHull ℝ _ hOther))
    simpa [a, x, functional_realPairing] using hSep
  have hCone : ∀ t : ℝ, 0 < t → ∀ u ∈ U, t • u ∈ U := by
    intro t ht u hu i hi
    simpa [realPairing_smul] using mul_lt_mul_of_pos_left (hu i hi) ht
  obtain ⟨u,hu⟩ := exists_integer_of_open_cone U hOpen ⟨a,ha⟩ hCone
  refine ⟨u, ?_, ?_⟩
  · intro i
    by_cases hi : μ i = μ j
    · simp [hi]
    · exact le_of_lt (by simpa [realPairing_int] using hu i hi)
  · intro i he
    by_contra hi
    have hlt : pairing (μ j) u < pairing (μ i) u := by
      simpa [realPairing_int] using hu i hi
    omega

end
end QuaternionicSymmetry.TorusIntegralVertexExposure
