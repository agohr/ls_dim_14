import QuaternionicSymmetry.LocalChernWeilOrderedTransgression
import QuaternionicSymmetry.LocalChernWeilPowerPolynomial
import QuaternionicSymmetry.LocalPolynomialTransgressionIntegral

/-! Finite time-polynomial expansion of the ordered local Chern--Simons primitive. -/

namespace QuaternionicSymmetry.LocalChernWeilOrderedPolynomial

open QuaternionicSymmetry.LocalConnection
  QuaternionicSymmetry.LocalConnectionForms
  QuaternionicSymmetry.LocalConnectionExterior
  QuaternionicSymmetry.LocalChernWeilTracePowers
  QuaternionicSymmetry.LocalChernWeilPowerPolynomial
  QuaternionicSymmetry.LocalChernWeilOrderedTransgression
  QuaternionicSymmetry.LocalPolynomialTransgressionIntegral
  QuaternionicSymmetry.DifferentialFormCoefficient
  QuaternionicSymmetry.ContinuousWedge

noncomputable section
open scoped Topology

variable {E R B : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedRing R] [NormedAlgebra ℝ R]
  [NormedAddCommGroup B] [NormedSpace ℝ B]

local instance : NormedSpace ℝ R := NormedAlgebra.toNormedSpace R

theorem degreeCast_sum {m n : ℕ} (h : m = n) {ι : Type*}
    [Fintype ι] (f : ι → E [⋀^Fin m]→L[ℝ] R) :
    degreeCast h (∑ i, f i) = ∑ i, degreeCast h (f i) := by
  cases h
  rfl

theorem degreeCast_smul {m n : ℕ} (h : m = n)
    (c : ℝ) (ω : E [⋀^Fin m]→L[ℝ] R) :
    degreeCast h (c • ω) = c • degreeCast h ω := by
  cases h
  rfl

/-- Ordered choices in the affine-path primitive recursion. -/
def PrimitiveWordIndex : ℕ → Type
  | 0 => PUnit
  | k + 1 => TimeWordIndex k ⊕ (Fin 3 × PrimitiveWordIndex k)

instance primitiveWordIndexFintype : (k : ℕ) → Fintype (PrimitiveWordIndex k)
  | 0 => by
      change Fintype PUnit
      infer_instance
  | k + 1 => by
      letI := timeWordIndexFintype k
      letI := primitiveWordIndexFintype k
      dsimp [PrimitiveWordIndex]
      infer_instance

def primitiveWordExponent : (k : ℕ) → PrimitiveWordIndex k → ℕ
  | 0, _ => 0
  | k + 1, Sum.inl w => timeWordExponent k w
  | k + 1, Sum.inr (i, w) => i.val + primitiveWordExponent k w

/-- A single ordered coefficient form, retaining its noncommutative product order. -/
def primitivePathCoeff (Γ θ : Form (E := E) (A := R)) :
    (k : ℕ) → PrimitiveWordIndex k →
      E → E [⋀^Fin (primitiveDegree k)]→L[ℝ] R
  | 0, _ => connectionForm θ
  | k + 1, Sum.inl w => fun y =>
      degreeCast (show 1 + powerDegree k = primitiveDegree (k + 1) by rfl)
        (wedge (ContinuousLinearMap.mul ℝ R)
          (connectionForm θ y) (curvaturePowerPathCoeff Γ θ k w y))
  | k + 1, Sum.inr (i, w) => fun y =>
      degreeCast (primitiveDegree_succ_cast k)
        (wedge (ContinuousLinearMap.mul ℝ R)
          (curvatureBaseCoeff Γ θ i y) (primitivePathCoeff Γ θ k w y))

theorem differentiableAt_primitivePathCoeff
    (Γ θ : Form (E := E) (A := R)) (x : E)
    (hΓ : ContDiffAt ℝ 2 Γ x) (hθ : ContDiffAt ℝ 2 θ x)
    (k : ℕ) (w : PrimitiveWordIndex k) :
    DifferentiableAt ℝ (primitivePathCoeff Γ θ k w) x := by
  have hθform : DifferentiableAt ℝ (connectionForm θ) x :=
    (oneFormMap (E := E) (A := R)).differentiableAt.comp x
      (hθ.differentiableAt (by norm_num))
  induction k with
  | zero => exact hθform
  | succ k ih =>
      rcases w with w | ⟨i, w⟩
      · exact differentiableAt_degreeCast
          (show 1 + powerDegree k = primitiveDegree (k + 1) by rfl) _ x
          (differentiableAt_wedge (ContinuousLinearMap.mul ℝ R)
            (connectionForm θ) (curvaturePowerPathCoeff Γ θ k w)
            x hθform
            (differentiableAt_curvaturePowerPathCoeff Γ θ x hΓ hθ k w))
      · exact differentiableAt_degreeCast (primitiveDegree_succ_cast k) _ x
          (differentiableAt_wedge (ContinuousLinearMap.mul ℝ R)
            (curvatureBaseCoeff Γ θ i) (primitivePathCoeff Γ θ k w)
            x (differentiableAt_curvatureBaseCoeff Γ θ x hΓ hθ i)
            (ih w))

/-- Each ordered primitive on the affine connection path is a finite real
time polynomial with differentiable coefficient forms. -/
theorem orderedPrimitive_path_sum
    (Γ θ : Form (E := E) (A := R)) (y : E)
    (hΓ : DifferentiableAt ℝ Γ y) (hθ : DifferentiableAt ℝ θ y)
    (t : ℝ) (k : ℕ) :
    orderedPrimitive (Γ + t • θ) θ k y =
      ∑ w : PrimitiveWordIndex k,
        t ^ primitiveWordExponent k w • primitivePathCoeff Γ θ k w y := by
  induction k with
  | zero => simp [orderedPrimitive, PrimitiveWordIndex,
        primitiveWordExponent, primitivePathCoeff]
  | succ k ih =>
      let h₁ : 1 + powerDegree k = primitiveDegree (k + 1) := rfl
      let h₂ := primitiveDegree_succ_cast k
      have hleft :
          wedge (ContinuousLinearMap.mul ℝ R)
              (connectionForm θ y) (curvaturePowerForm (Γ + t • θ) k y) =
            ∑ w : TimeWordIndex k,
              t ^ timeWordExponent k w •
                wedge (ContinuousLinearMap.mul ℝ R)
                  (connectionForm θ y) (curvaturePowerPathCoeff Γ θ k w y) := by
        rw [curvaturePowerForm_path_sum Γ θ y hΓ hθ t k]
        change (wedgeCLM (E := E) (A := R) (B := R) (C := R)
          (p := 1) (q := powerDegree k) (ContinuousLinearMap.mul ℝ R)
            (connectionForm θ y))
            (∑ w : TimeWordIndex k,
              t ^ timeWordExponent k w • curvaturePowerPathCoeff Γ θ k w y) = _
        simp only [map_sum, map_smul, wedgeCLM_apply]
      have hright :
          wedge (ContinuousLinearMap.mul ℝ R)
              (curvatureForm (Γ + t • θ) y)
              (orderedPrimitive (Γ + t • θ) θ k y) =
            ∑ i : Fin 3, ∑ w : PrimitiveWordIndex k,
              t ^ (i.val + primitiveWordExponent k w) •
                wedge (ContinuousLinearMap.mul ℝ R)
                  (curvatureBaseCoeff Γ θ i y)
                  (primitivePathCoeff Γ θ k w y) := by
        rw [curvatureForm_path_sum Γ θ y hΓ hθ t, ih]
        rw [wedge_sum_sum]
        simp only [pow_add]
      change degreeCast h₁
          (wedge (ContinuousLinearMap.mul ℝ R)
            (connectionForm θ y) (curvaturePowerForm (Γ + t • θ) k y)) +
        degreeCast h₂
          (wedge (ContinuousLinearMap.mul ℝ R)
            (curvatureForm (Γ + t • θ) y)
            (orderedPrimitive (Γ + t • θ) θ k y)) = _
      rw [hleft, hright, degreeCast_sum, degreeCast_sum]
      simp only [degreeCast_sum, degreeCast_smul, PrimitiveWordIndex,
        Fintype.sum_sum_type, Fintype.sum_prod_type,
        primitiveWordExponent, primitivePathCoeff]

private theorem extDeriv_congr_eventually {p : ℕ}
    (ω η : E → E [⋀^Fin p]→L[ℝ] B) (x : E)
    (h : ω =ᶠ[𝓝 x] η) : extDeriv ω x = extDeriv η x := by
  simp only [extDeriv]
  rw [h.fderiv_eq]

/-- Spatial exterior differentiation commutes with integration along the
affine connection path of the traced ordered primitive in every degree. -/
theorem extDeriv_integral_traceOrderedPrimitive [CompleteSpace B]
    (T : R →L[ℝ] B) (Γ θ : Form (E := E) (A := R))
    (k : ℕ) (x : E)
    (hΓ : ContDiffAt ℝ 2 Γ x) (hθ : ContDiffAt ℝ 2 θ x) :
    extDeriv (fun y => ∫ t in (0 : ℝ)..1,
      T.compContinuousAlternatingMap
        (orderedPrimitive (Γ + t • θ) θ k y)) x =
    ∫ t in (0 : ℝ)..1,
      extDeriv (fun y => T.compContinuousAlternatingMap
        (orderedPrimitive (Γ + t • θ) θ k y)) x := by
  let L := (ContinuousLinearMap.compContinuousAlternatingMapCLM
    (ι := Fin (primitiveDegree k)) ℝ E R B) T
  let A : PrimitiveWordIndex k →
      E → E [⋀^Fin (primitiveDegree k)]→L[ℝ] B :=
    fun w y => L (primitivePathCoeff Γ θ k w y)
  let degree : PrimitiveWordIndex k → ℕ := primitiveWordExponent k
  have hA : ∀ w ∈ (Finset.univ : Finset (PrimitiveWordIndex k)),
      DifferentiableAt ℝ (A w) x := by
    intro w _
    exact L.differentiableAt.comp x
      (differentiableAt_primitivePathCoeff Γ θ x hΓ hθ k w)
  have hpoly :=
    LocalPolynomialTransgressionIntegral.extDeriv_integral_weighted_polynomial
      (Finset.univ : Finset (PrimitiveWordIndex k)) degree A x hA
  have hdiff : ∀ᶠ y in 𝓝 x,
      DifferentiableAt ℝ Γ y ∧ DifferentiableAt ℝ θ y := by
    filter_upwards [hΓ.eventually (by norm_num), hθ.eventually (by norm_num)]
      with y hΓy hθy
    exact ⟨hΓy.differentiableAt (by norm_num),
      hθy.differentiableAt (by norm_num)⟩
  have hpath (y : E) (hy : DifferentiableAt ℝ Γ y ∧
      DifferentiableAt ℝ θ y) (t : ℝ) :
      T.compContinuousAlternatingMap
          (orderedPrimitive (Γ + t • θ) θ k y) =
        ∑ w : PrimitiveWordIndex k, t ^ degree w • A w y := by
    change L (orderedPrimitive (Γ + t • θ) θ k y) = _
    rw [orderedPrimitive_path_sum Γ θ y hy.1 hy.2 t k]
    simp only [map_sum, map_smul, A, degree]
  have hleft : (fun y => ∫ t in (0 : ℝ)..1,
      T.compContinuousAlternatingMap
        (orderedPrimitive (Γ + t • θ) θ k y)) =ᶠ[𝓝 x]
      (fun y => ∫ t in (0 : ℝ)..1,
        ∑ w : PrimitiveWordIndex k, t ^ degree w • A w y) := by
    filter_upwards [hdiff] with y hy
    apply intervalIntegral.integral_congr
    intro t _
    exact hpath y hy t
  have hright (t : ℝ) :
      extDeriv (fun y => T.compContinuousAlternatingMap
        (orderedPrimitive (Γ + t • θ) θ k y)) x =
      extDeriv (fun y =>
        ∑ w : PrimitiveWordIndex k, t ^ degree w • A w y) x := by
    apply extDeriv_congr_eventually
    exact hdiff.mono (fun y hy => hpath y hy t)
  calc
    extDeriv (fun y => ∫ t in (0 : ℝ)..1,
        T.compContinuousAlternatingMap
          (orderedPrimitive (Γ + t • θ) θ k y)) x =
      extDeriv (fun y => ∫ t in (0 : ℝ)..1,
        ∑ w : PrimitiveWordIndex k, t ^ degree w • A w y) x :=
          extDeriv_congr_eventually _ _ x hleft
    _ = ∫ t in (0 : ℝ)..1,
        extDeriv (fun y =>
          ∑ w : PrimitiveWordIndex k, t ^ degree w • A w y) x := hpoly
    _ = ∫ t in (0 : ℝ)..1,
        extDeriv (fun y => T.compContinuousAlternatingMap
          (orderedPrimitive (Γ + t • θ) θ k y)) x := by
          apply intervalIntegral.integral_congr
          intro t _
          exact (hright t).symm

end
end QuaternionicSymmetry.LocalChernWeilOrderedPolynomial
