import QuaternionicSymmetry.HolomorphicLineIntegerPowers

/-! Tensor product of two genuine holomorphic complex line-bundle cores
on possibly different covers of the same base. The product cover uses
intersections, so this is not limited to a fixed contact-line cocycle.
It is a bundle-core construction, not yet a Picard-group quotient by
cover-invariant holomorphic isomorphism. -/

namespace QuaternionicSymmetry.HolomorphicLineTensor

open QuaternionicSymmetry.HolomorphicLinePowers
open scoped Manifold ContDiff
noncomputable section

variable {B H F : Type*} [TopologicalSpace B] [TopologicalSpace H]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
  [ChartedSpace H B] {IB : ModelWithCorners ℂ F H}
  {ι κ : Type*}
  (Z : VectorBundleCore ℂ B ℂ ι) (W : VectorBundleCore ℂ B ℂ κ)

/-- Tensoring complex lines multiplies their scalar transition laws.
The index type is the common refinement `ι × κ`, whose basic open sets
are intersections of the two original basic opens. -/
def tensorCore : VectorBundleCore ℂ B ℂ (ι × κ) where
  baseSet p := Z.baseSet p.1 ∩ W.baseSet p.2
  isOpen_baseSet p := (Z.isOpen_baseSet p.1).inter (W.isOpen_baseSet p.2)
  indexAt x := (Z.indexAt x, W.indexAt x)
  mem_baseSet_at x := ⟨Z.mem_baseSet_at x, W.mem_baseSet_at x⟩
  coordChange p q x :=
    (transitionScalar Z p.1 q.1 x * transitionScalar W p.2 q.2 x) •
      ContinuousLinearMap.id ℂ ℂ
  coordChange_self p x hx v := by
    have hz : transitionScalar Z p.1 p.1 x = 1 :=
      Z.coordChange_self p.1 x hx.1 1
    have hw : transitionScalar W p.2 p.2 x = 1 :=
      W.coordChange_self p.2 x hx.2 1
    simp [hz, hw]
  continuousOn_coordChange p q := by
    have hz : ContinuousOn (fun x => transitionScalar Z p.1 q.1 x)
        ((Z.baseSet p.1 ∩ W.baseSet p.2) ∩
          (Z.baseSet q.1 ∩ W.baseSet q.2)) :=
      ((Z.continuousOn_coordChange p.1 q.1).clm_apply continuousOn_const).mono
        (by intro x hx; exact ⟨hx.1.1, hx.2.1⟩)
    have hw : ContinuousOn (fun x => transitionScalar W p.2 q.2 x)
        ((Z.baseSet p.1 ∩ W.baseSet p.2) ∩
          (Z.baseSet q.1 ∩ W.baseSet q.2)) :=
      ((W.continuousOn_coordChange p.2 q.2).clm_apply continuousOn_const).mono
        (by intro x hx; exact ⟨hx.1.2, hx.2.2⟩)
    exact (hz.mul hw).smul continuousOn_const
  coordChange_comp p q t x hx v := by
    have hzcomp := Z.coordChange_comp p.1 q.1 t.1 x
      ⟨⟨hx.1.1.1, hx.1.2.1⟩, hx.2.1⟩ (1 : ℂ)
    have hwcomp := W.coordChange_comp p.2 q.2 t.2 x
      ⟨⟨hx.1.1.2, hx.1.2.2⟩, hx.2.2⟩ (1 : ℂ)
    have hz : transitionScalar Z q.1 t.1 x * transitionScalar Z p.1 q.1 x =
        transitionScalar Z p.1 t.1 x :=
      (linear_apply_one (Z.coordChange q.1 t.1 x)
        (Z.coordChange p.1 q.1 x 1)).symm.trans hzcomp
    have hw : transitionScalar W q.2 t.2 x * transitionScalar W p.2 q.2 x =
        transitionScalar W p.2 t.2 x :=
      (linear_apply_one (W.coordChange q.2 t.2 x)
        (W.coordChange p.2 q.2 x 1)).symm.trans hwcomp
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul]
    rw [← hz, ← hw]
    ring

/-- Holomorphicity of the tensor product follows from holomorphicity
of the two transition cocycles on their common refinement. -/
instance tensorCore_isContMDiff [Z.IsContMDiff IB ∞] [W.IsContMDiff IB ∞] :
    (tensorCore Z W).IsContMDiff IB ∞ where
  contMDiffOn_coordChange p q := by
    have hz : ContMDiffOn IB 𝓘(ℂ,ℂ) ∞
        (fun x => transitionScalar Z p.1 q.1 x)
        ((Z.baseSet p.1 ∩ W.baseSet p.2) ∩
          (Z.baseSet q.1 ∩ W.baseSet q.2)) :=
      ((Z.contMDiffOn_coordChange IB p.1 q.1).clm_apply contMDiffOn_const).mono
        (by intro x hx; exact ⟨hx.1.1, hx.2.1⟩)
    have hw : ContMDiffOn IB 𝓘(ℂ,ℂ) ∞
        (fun x => transitionScalar W p.2 q.2 x)
        ((Z.baseSet p.1 ∩ W.baseSet p.2) ∩
          (Z.baseSet q.1 ∩ W.baseSet q.2)) :=
      ((W.contMDiffOn_coordChange IB p.2 q.2).clm_apply contMDiffOn_const).mono
        (by intro x hx; exact ⟨hx.1.2, hx.2.2⟩)
    exact (hz.mul hw).smul contMDiffOn_const

/-- The transition of the tensor core is exactly the product of the
two original scalar transitions, on the common-refinement chart. -/
theorem tensorCore_transitionScalar (p q : ι × κ) (x : B) :
    transitionScalar (tensorCore Z W) p q x =
      transitionScalar Z p.1 q.1 x * transitionScalar W p.2 q.2 x := by
  simp [transitionScalar, tensorCore]

/-- Tensoring integer powers is computed by multiplying the powered
transition scalars. This is the chartwise comparison used for true
line-bundle tensor powers, without identifying different covers by fiat. -/
theorem tensorCore_power_transitionScalar (a b : ℕ)
    (p q : ι × κ) (x : B) :
    transitionScalar (tensorCore (powerCore Z a) (powerCore W b)) p q x =
      (transitionScalar Z p.1 q.1 x) ^ a *
        (transitionScalar W p.2 q.2 x) ^ b := by
  rw [tensorCore_transitionScalar]
  simp [transitionScalar, powerCore, ContinuousLinearMap.smul_apply, smul_eq_mul]

/-- Dualization reverses the transition scalar, so a tensor product
with the dual of a second line has the expected ratio cocycle. -/
theorem tensorCore_dual_transitionScalar (p : ι × κ) (q : ι × κ)
    (x : B) :
    transitionScalar (tensorCore Z (HolomorphicLineIntegerPowers.dualCore W))
        p q x =
      transitionScalar Z p.1 q.1 x * transitionScalar W q.2 p.2 x := by
  rw [tensorCore_transitionScalar]
  simp [transitionScalar, HolomorphicLineIntegerPowers.dualCore,
    ContinuousLinearMap.smul_apply, smul_eq_mul]

/-- On the diagonal refinement, the tensor square and ordinary second
power have the same transition scalar. The statement is deliberately
chartwise; a Picard-class equality needs cover-invariant isomorphisms. -/
theorem tensorCore_self_diagonal_transitionScalar (i j : ι) (x : B) :
    transitionScalar (tensorCore Z Z) (i, i) (j, j) x =
      transitionScalar (powerCore Z 2) i j x := by
  rw [tensorCore_transitionScalar]
  simp [transitionScalar, powerCore, pow_two,
    ContinuousLinearMap.smul_apply, smul_eq_mul]

end
end QuaternionicSymmetry.HolomorphicLineTensor
