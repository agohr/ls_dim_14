import QuaternionicSymmetry.HolomorphicLineCoreClasses

/-! The tensor product of the `k`-th represented line power with the
original line is holomorphically gauge-isomorphic to its `(k+1)`-st power. -/

namespace QuaternionicSymmetry.HolomorphicLinePowerTensorGauge

open QuaternionicSymmetry.HolomorphicLineGauge
open QuaternionicSymmetry.HolomorphicLinePowers
open scoped Manifold ContDiff
noncomputable section

variable {B H F : Type*} [TopologicalSpace B] [TopologicalSpace H]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
  [ChartedSpace H B] {IB : ModelWithCorners ℂ F H}
  {ι : Type*} (Z : VectorBundleCore ℂ B ℂ ι)
  [Z.IsContMDiff IB ∞]

private theorem power_scalar (m : ℕ) (i j : ι) (x : B) :
    transitionScalar (powerCore Z m) i j x = (transitionScalar Z i j x)^m := by
  simp [transitionScalar, powerCore, ContinuousLinearMap.smul_apply, smul_eq_mul]

private theorem tensor_power_scalar (m : ℕ) (p q : ι × ι) (x : B) :
    transitionScalar (HolomorphicLineTensor.tensorCore (powerCore Z m) Z) p q x =
      (transitionScalar Z p.1 q.1 x)^m * transitionScalar Z p.2 q.2 x := by
  rw [HolomorphicLineTensor.tensorCore_transitionScalar, power_scalar]

/-- The all-overlap comparison of a tensor product and the next power;
the two source factors retain their independent local-chart choices. -/
def powerTensorGauge (k : ℕ) :
    GaugeIso (IB := IB)
      (HolomorphicLineTensor.tensorCore (powerCore Z k) Z)
      (powerCore Z (k + 1)) where
  forward p j x := (transitionScalar Z p.1 j x)^k * transitionScalar Z p.2 j x
  backward j p x := (transitionScalar Z j p.1 x)^k * transitionScalar Z j p.2 x
  forward_holomorphic p j := by
    change ContMDiffOn IB 𝓘(ℂ,ℂ) ∞
      (fun x => (transitionScalar Z p.1 j x)^k * transitionScalar Z p.2 j x)
      ((Z.baseSet p.1 ∩ Z.baseSet p.2) ∩ Z.baseSet j)
    have h1 : ContMDiffOn IB 𝓘(ℂ,ℂ) ∞ (fun x => transitionScalar Z p.1 j x)
        ((Z.baseSet p.1 ∩ Z.baseSet p.2) ∩ Z.baseSet j) :=
      ((Z.contMDiffOn_coordChange IB p.1 j).clm_apply contMDiffOn_const).mono
        (by intro x hx; exact ⟨hx.1.1, hx.2⟩)
    have h2 : ContMDiffOn IB 𝓘(ℂ,ℂ) ∞ (fun x => transitionScalar Z p.2 j x)
        ((Z.baseSet p.1 ∩ Z.baseSet p.2) ∩ Z.baseSet j) :=
      ((Z.contMDiffOn_coordChange IB p.2 j).clm_apply contMDiffOn_const).mono
        (by intro x hx; exact ⟨hx.1.2, hx.2⟩)
    exact (h1.pow k).mul h2
  backward_holomorphic j p := by
    change ContMDiffOn IB 𝓘(ℂ,ℂ) ∞
      (fun x => (transitionScalar Z j p.1 x)^k * transitionScalar Z j p.2 x)
      (Z.baseSet j ∩ (Z.baseSet p.1 ∩ Z.baseSet p.2))
    have h1 : ContMDiffOn IB 𝓘(ℂ,ℂ) ∞ (fun x => transitionScalar Z j p.1 x)
        (Z.baseSet j ∩ (Z.baseSet p.1 ∩ Z.baseSet p.2)) :=
      ((Z.contMDiffOn_coordChange IB j p.1).clm_apply contMDiffOn_const).mono
        (by intro x hx; exact ⟨hx.1, hx.2.1⟩)
    have h2 : ContMDiffOn IB 𝓘(ℂ,ℂ) ∞ (fun x => transitionScalar Z j p.2 x)
        (Z.baseSet j ∩ (Z.baseSet p.1 ∩ Z.baseSet p.2)) :=
      ((Z.contMDiffOn_coordChange IB j p.2).clm_apply contMDiffOn_const).mono
        (by intro x hx; exact ⟨hx.1, hx.2.2⟩)
    exact (h1.pow k).mul h2
  forward_compat p q c d x hx := by
    have hi : x ∈ Z.baseSet p.1 := hx.1.1.1.1
    have ha : x ∈ Z.baseSet p.2 := hx.1.1.1.2
    have hj : x ∈ Z.baseSet q.1 := hx.1.1.2.1
    have hb : x ∈ Z.baseSet q.2 := hx.1.1.2.2
    have hc : x ∈ Z.baseSet c := hx.1.2
    have hd : x ∈ Z.baseSet d := hx.2
    have h1 := scalar_comp Z p.1 c d x ⟨⟨hi, hc⟩, hd⟩
    have h2 := scalar_comp Z p.2 c d x ⟨⟨ha, hc⟩, hd⟩
    have h3 := scalar_comp Z p.1 q.1 d x ⟨⟨hi, hj⟩, hd⟩
    have h4 := scalar_comp Z p.2 q.2 d x ⟨⟨ha, hb⟩, hd⟩
    rw [power_scalar Z (k + 1) c d x, tensor_power_scalar Z k p q x]
    calc
      transitionScalar Z c d x ^ (k + 1) *
          (transitionScalar Z p.1 c x ^ k * transitionScalar Z p.2 c x) =
        (transitionScalar Z c d x * transitionScalar Z p.1 c x)^k *
          (transitionScalar Z c d x * transitionScalar Z p.2 c x) := by
          rw [pow_succ, mul_pow]
          ring
      _ = transitionScalar Z p.1 d x ^ k * transitionScalar Z p.2 d x := by
        rw [h1, h2]
      _ = (transitionScalar Z q.1 d x ^ k * transitionScalar Z q.2 d x) *
          (transitionScalar Z p.1 q.1 x ^ k * transitionScalar Z p.2 q.2 x) := by
        rw [← h3, ← h4, mul_pow]
        ring
  backward_compat c d p q x hx := by
    have hc : x ∈ Z.baseSet c := hx.1.1.1
    have hd : x ∈ Z.baseSet d := hx.1.1.2
    have hi : x ∈ Z.baseSet p.1 := hx.1.2.1
    have ha : x ∈ Z.baseSet p.2 := hx.1.2.2
    have hj : x ∈ Z.baseSet q.1 := hx.2.1
    have hb : x ∈ Z.baseSet q.2 := hx.2.2
    have h1 := scalar_comp Z c p.1 q.1 x ⟨⟨hc, hi⟩, hj⟩
    have h2 := scalar_comp Z c p.2 q.2 x ⟨⟨hc, ha⟩, hb⟩
    have h3 := scalar_comp Z c d q.1 x ⟨⟨hc, hd⟩, hj⟩
    have h4 := scalar_comp Z c d q.2 x ⟨⟨hc, hd⟩, hb⟩
    rw [tensor_power_scalar Z k p q x, power_scalar Z (k + 1) c d x]
    calc
      (transitionScalar Z p.1 q.1 x ^ k * transitionScalar Z p.2 q.2 x) *
          (transitionScalar Z c p.1 x ^ k * transitionScalar Z c p.2 x) =
        (transitionScalar Z p.1 q.1 x * transitionScalar Z c p.1 x)^k *
          (transitionScalar Z p.2 q.2 x * transitionScalar Z c p.2 x) := by
          rw [mul_pow]
          ring
      _ = transitionScalar Z c q.1 x ^ k * transitionScalar Z c q.2 x := by
        rw [h1, h2]
      _ = (transitionScalar Z d q.1 x ^ k * transitionScalar Z d q.2 x) *
          transitionScalar Z c d x ^ (k + 1) := by
        rw [← h3, ← h4, pow_succ, mul_pow]
        ring
  left_inverse p j x hx := by
    have hi : x ∈ Z.baseSet p.1 := hx.1.1
    have ha : x ∈ Z.baseSet p.2 := hx.1.2
    have hj : x ∈ Z.baseSet j := hx.2
    have h1 := scalar_comp Z p.1 j p.1 x ⟨⟨hi, hj⟩, hi⟩
    have h2 := scalar_comp Z p.2 j p.2 x ⟨⟨ha, hj⟩, ha⟩
    have hs1 : transitionScalar Z p.1 p.1 x = 1 := Z.coordChange_self p.1 x hi 1
    have hs2 : transitionScalar Z p.2 p.2 x = 1 := Z.coordChange_self p.2 x ha 1
    rw [hs1] at h1
    rw [hs2] at h2
    change (transitionScalar Z j p.1 x ^ k * transitionScalar Z j p.2 x) *
      (transitionScalar Z p.1 j x ^ k * transitionScalar Z p.2 j x) = 1
    calc
      (transitionScalar Z j p.1 x ^ k * transitionScalar Z j p.2 x) *
          (transitionScalar Z p.1 j x ^ k * transitionScalar Z p.2 j x) =
        (transitionScalar Z j p.1 x * transitionScalar Z p.1 j x)^k *
          (transitionScalar Z j p.2 x * transitionScalar Z p.2 j x) := by
          rw [mul_pow]
          ring
      _ = 1 := by rw [h1, h2]; simp
  right_inverse j p x hx := by
    have hi : x ∈ Z.baseSet p.1 := hx.2.1
    have ha : x ∈ Z.baseSet p.2 := hx.2.2
    have hj : x ∈ Z.baseSet j := hx.1
    have h1 := scalar_comp Z p.1 j p.1 x ⟨⟨hi, hj⟩, hi⟩
    have h2 := scalar_comp Z p.2 j p.2 x ⟨⟨ha, hj⟩, ha⟩
    have hs1 : transitionScalar Z p.1 p.1 x = 1 := Z.coordChange_self p.1 x hi 1
    have hs2 : transitionScalar Z p.2 p.2 x = 1 := Z.coordChange_self p.2 x ha 1
    rw [hs1] at h1
    rw [hs2] at h2
    change (transitionScalar Z p.1 j x ^ k * transitionScalar Z p.2 j x) *
      (transitionScalar Z j p.1 x ^ k * transitionScalar Z j p.2 x) = 1
    calc
      (transitionScalar Z p.1 j x ^ k * transitionScalar Z p.2 j x) *
          (transitionScalar Z j p.1 x ^ k * transitionScalar Z j p.2 x) =
        (transitionScalar Z j p.1 x * transitionScalar Z p.1 j x)^k *
          (transitionScalar Z j p.2 x * transitionScalar Z p.2 j x) := by
          rw [mul_pow]
          ring
      _ = 1 := by rw [h1, h2]; simp

end
end QuaternionicSymmetry.HolomorphicLinePowerTensorGauge
