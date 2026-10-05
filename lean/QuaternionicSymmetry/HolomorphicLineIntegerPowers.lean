import QuaternionicSymmetry.HolomorphicLinePowers

/-! Integer tensor powers of a genuine holomorphic complex line core. The
negative powers use the dual transition functions, so this construction also
provides the actual bundles needed for negative Hilbert twists. -/

namespace QuaternionicSymmetry.HolomorphicLineIntegerPowers

open QuaternionicSymmetry.HolomorphicLinePowers
open scoped Manifold ContDiff
noncomputable section

variable {B H F : Type*} [TopologicalSpace B] [TopologicalSpace H]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
  [ChartedSpace H B] {IB : ModelWithCorners ℂ F H}
  {ι : Type*} (Z : VectorBundleCore ℂ B ℂ ι)

/-- Reversing a line transition is fiberwise inversion on an overlap. -/
theorem transitionScalar_reverse (i j : ι) (x : B)
    (hx : x ∈ Z.baseSet i ∩ Z.baseSet j) :
    transitionScalar Z j i x = (transitionScalar Z i j x)⁻¹ := by
  have hcomp := Z.coordChange_comp i j i x ⟨hx,hx.1⟩ (1 : ℂ)
  have hself := Z.coordChange_self i x hx.1 (1 : ℂ)
  have hmul : transitionScalar Z j i x * transitionScalar Z i j x = 1 := by
    exact (linear_apply_one (Z.coordChange j i x) (Z.coordChange i j x 1)).symm.trans
      (hcomp.trans hself)
  exact eq_inv_of_mul_eq_one_left hmul

/-- The dual complex line, represented in a fixed one-dimensional fiber
by reversing the scalar transition functions. -/
def dualCore : VectorBundleCore ℂ B ℂ ι where
  baseSet := Z.baseSet
  isOpen_baseSet := Z.isOpen_baseSet
  indexAt := Z.indexAt
  mem_baseSet_at := Z.mem_baseSet_at
  coordChange i j x := transitionScalar Z j i x • ContinuousLinearMap.id ℂ ℂ
  coordChange_self i x hx v := by
    change transitionScalar Z i i x * v = v
    rw [show transitionScalar Z i i x = 1 by exact Z.coordChange_self i x hx 1]
    simp
  continuousOn_coordChange i j := by
    have h : ContinuousOn (fun x => transitionScalar Z j i x)
        (Z.baseSet i ∩ Z.baseSet j) := by
      have hj : ContinuousOn (fun x => transitionScalar Z j i x)
          (Z.baseSet j ∩ Z.baseSet i) :=
        (Z.continuousOn_coordChange j i).clm_apply continuousOn_const
      exact hj.mono (by intro x hx; exact ⟨hx.2,hx.1⟩)
    exact h.smul continuousOn_const
  coordChange_comp i j l x hx v := by
    have hcomp := Z.coordChange_comp l j i x ⟨⟨hx.2,hx.1.2⟩,hx.1.1⟩ (1 : ℂ)
    have hs : transitionScalar Z j i x * transitionScalar Z l j x =
        transitionScalar Z l i x := by
      change (Z.coordChange j i x 1) * (Z.coordChange l j x 1) =
        (Z.coordChange l i x 1)
      exact (linear_apply_one (Z.coordChange j i x) (Z.coordChange l j x 1)).symm.trans
        hcomp
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul]
    calc
      transitionScalar Z l j x * (transitionScalar Z j i x * v) =
          (transitionScalar Z j i x * transitionScalar Z l j x) * v := by ring
      _ = transitionScalar Z l i x * v := by rw [hs]

instance dualCore_isContMDiff [Z.IsContMDiff IB ∞] :
    (dualCore Z).IsContMDiff IB ∞ where
  contMDiffOn_coordChange i j := by
    have h : ContMDiffOn IB 𝓘(ℂ,ℂ) ∞
        (fun x => transitionScalar Z j i x) (Z.baseSet i ∩ Z.baseSet j) := by
      have hj : ContMDiffOn IB 𝓘(ℂ,ℂ) ∞
          (fun x => transitionScalar Z j i x) (Z.baseSet j ∩ Z.baseSet i) :=
        (Z.contMDiffOn_coordChange IB j i).clm_apply contMDiffOn_const
      exact hj.mono (by intro x hx; exact ⟨hx.2,hx.1⟩)
    exact h.smul contMDiffOn_const

/-- All integral tensor powers. At exponent zero this is the trivial line;
at a negative exponent it is the corresponding power of the dual line. -/
def integerPowerCore (r : ℤ) : VectorBundleCore ℂ B ℂ ι :=
  if 0 ≤ r then powerCore Z r.toNat else powerCore (dualCore Z) (-r).toNat

instance integerPowerCore_isContMDiff [Z.IsContMDiff IB ∞] (r : ℤ) :
    (integerPowerCore Z r).IsContMDiff IB ∞ := by
  unfold integerPowerCore
  split <;> infer_instance

theorem integerPowerCore_natCast (k : ℕ) :
    integerPowerCore Z (k : ℤ) = powerCore Z k := by
  simp [integerPowerCore]

theorem integerPowerCore_neg_natCast (k : ℕ) (hk : 0 < k) :
    integerPowerCore Z (-(k : ℤ)) = powerCore (dualCore Z) k := by
  have hk0 : k ≠ 0 := Nat.ne_of_gt hk
  simp [integerPowerCore, hk0]

end
end QuaternionicSymmetry.HolomorphicLineIntegerPowers
