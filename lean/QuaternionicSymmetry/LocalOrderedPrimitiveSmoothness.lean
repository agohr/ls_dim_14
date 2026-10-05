import QuaternionicSymmetry.LocalChernWeilSmoothness
import QuaternionicSymmetry.LocalChernWeilOrderedPolynomial
import QuaternionicSymmetry.LocalChernWeilOrderedExact

/-!
Smoothness of the integrated ordered Chern--Simons primitive on an open
chart target. The path integral is evaluated as a finite polynomial in the
time parameter, so no integral regularity is left as a premise.
-/

namespace QuaternionicSymmetry.LocalOrderedPrimitiveSmoothness

open QuaternionicSymmetry.LocalConnection
  QuaternionicSymmetry.LocalConnectionForms
  QuaternionicSymmetry.LocalConnectionExterior
  QuaternionicSymmetry.LocalChernWeilTracePowers
  QuaternionicSymmetry.LocalChernWeilOrderedTransgression
  QuaternionicSymmetry.LocalChernWeilOrderedExact
  QuaternionicSymmetry.LocalChernWeilOrderedPolynomial
  QuaternionicSymmetry.LocalChernWeilPowerPolynomial
  QuaternionicSymmetry.LocalChernWeilSmoothness
  QuaternionicSymmetry.LocalPolynomialTransgressionIntegral
  QuaternionicSymmetry.ContinuousWedge
open scoped ContDiff Topology

variable {E R B : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedRing R] [NormedAlgebra ℝ R]
  [NormedAddCommGroup B] [NormedSpace ℝ B] [CompleteSpace B]

noncomputable section

local instance : NormedSpace ℝ R := NormedAlgebra.toNormedSpace R
local instance : NormedAddCommGroup (E →L[ℝ] R) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (E →L[ℝ] R) :=
  ContinuousLinearMap.toNormedSpace
local instance : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] R) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] R) :=
  ContinuousLinearMap.toNormedSpace

private theorem product_contDiffOn (Γ θ : Form (E := E) (A := R))
    {s : Set E} (hΓ : ContDiffOn ℝ ∞ Γ s)
    (hθ : ContDiffOn ℝ ∞ θ s) :
    ContDiffOn ℝ ∞ (product Γ θ) s := by
  have hleft : ContDiffOn ℝ ∞
      (fun x => productCLM (E := E) (A := R) (Γ x)) s :=
    hΓ.continuousLinearMap_comp _
  simpa only [productCLM_apply] using hleft.clm_apply hθ

private theorem wedge_contDiffOn {p q : ℕ}
    (a : E → E [⋀^Fin p]→L[ℝ] R)
    (b : E → E [⋀^Fin q]→L[ℝ] R)
    {s : Set E} (ha : ContDiffOn ℝ ∞ a s)
    (hb : ContDiffOn ℝ ∞ b s) :
    ContDiffOn ℝ ∞
      (fun x => wedge (ContinuousLinearMap.mul ℝ R) (a x) (b x)) s := by
  have hleft : ContDiffOn ℝ ∞
      (fun x => (wedgeCLM (E := E) (p := p) (q := q)
        (ContinuousLinearMap.mul ℝ R)) (a x)) s :=
    ha.continuousLinearMap_comp _
  simpa only [wedgeCLM_apply] using hleft.clm_apply hb

private theorem degreeCast_contDiffOn {m n : ℕ} (e : m = n)
    (a : E → E [⋀^Fin m]→L[ℝ] R)
    {s : Set E} (ha : ContDiffOn ℝ ∞ a s) :
    ContDiffOn ℝ ∞ (fun x => degreeCast e (a x)) s := by
  cases e
  exact ha

private theorem alternatingPart_contDiffOn
    (a : E → LocalConnection.Bilinear (E := E) (A := R))
    {s : Set E} (ha : ContDiffOn ℝ ∞ a s) :
    ContDiffOn ℝ ∞ (fun x => alternatingPart (a x)) s := by
  simpa only [alternatingPartCLM_apply] using
    ha.continuousLinearMap_comp (alternatingPartCLM (E := E) (A := R))

private theorem covariantDerivativeForm_contDiffOn
    (Γ θ : Form (E := E) (A := R))
    {s : Set E} (hs : IsOpen s)
    (hΓ : ContDiffOn ℝ ∞ Γ s)
    (hθ : ContDiffOn ℝ ∞ θ s) :
    ContDiffOn ℝ ∞ (covariantDerivativeForm Γ θ) s := by
  have hfd : ContDiffOn ℝ ∞ (fderiv ℝ θ) s := by
    simpa using hθ.fderiv_of_isOpen hs (by simp)
  have hprod₁ := product_contDiffOn Γ θ hΓ hθ
  have hprod₂ := product_contDiffOn θ Γ hθ hΓ
  have hsum : ContDiffOn ℝ ∞
      (fun x => fderiv ℝ θ x + product Γ θ x + product θ Γ x) s :=
    (hfd.add hprod₁).add hprod₂
  exact alternatingPart_contDiffOn _ hsum

private theorem wedgeSquareForm_contDiffOn
    (θ : Form (E := E) (A := R))
    {s : Set E} (hθ : ContDiffOn ℝ ∞ θ s) :
    ContDiffOn ℝ ∞ (wedgeSquareForm θ) s :=
  alternatingPart_contDiffOn _ (product_contDiffOn θ θ hθ hθ)

private theorem curvatureBaseCoeff_contDiffOn
    (Γ θ : Form (E := E) (A := R))
    {s : Set E} (hs : IsOpen s)
    (hΓ : ContDiffOn ℝ ∞ Γ s)
    (hθ : ContDiffOn ℝ ∞ θ s)
    (i : Fin 3) :
    ContDiffOn ℝ ∞ (curvatureBaseCoeff Γ θ i) s := by
  unfold curvatureBaseCoeff
  split_ifs with h0 h1
  · exact curvatureForm_contDiffOn Γ hs hΓ
  · exact covariantDerivativeForm_contDiffOn Γ θ hs hΓ hθ
  · exact wedgeSquareForm_contDiffOn θ hθ

private theorem curvaturePowerPathCoeff_contDiffOn
    (Γ θ : Form (E := E) (A := R))
    {s : Set E} (hs : IsOpen s)
    (hΓ : ContDiffOn ℝ ∞ Γ s)
    (hθ : ContDiffOn ℝ ∞ θ s)
    (k : ℕ) (w : TimeWordIndex k) :
    ContDiffOn ℝ ∞ (curvaturePowerPathCoeff Γ θ k w) s := by
  induction k with
  | zero => exact curvatureBaseCoeff_contDiffOn Γ θ hs hΓ hθ w
  | succ k ih =>
      rcases w with ⟨i, w⟩
      exact wedge_contDiffOn _ _
        (curvatureBaseCoeff_contDiffOn Γ θ hs hΓ hθ i) (ih w)

private theorem primitivePathCoeff_contDiffOn
    (Γ θ : Form (E := E) (A := R))
    {s : Set E} (hs : IsOpen s)
    (hΓ : ContDiffOn ℝ ∞ Γ s)
    (hθ : ContDiffOn ℝ ∞ θ s)
    (k : ℕ) (w : PrimitiveWordIndex k) :
    ContDiffOn ℝ ∞ (primitivePathCoeff Γ θ k w) s := by
  have hθform : ContDiffOn ℝ ∞ (connectionForm θ) s :=
    hθ.continuousLinearMap_comp (oneFormMap (E := E) (A := R))
  induction k with
  | zero => exact hθform
  | succ k ih =>
      rcases w with w | ⟨i, w⟩
      · exact degreeCast_contDiffOn
          (show 1 + powerDegree k = primitiveDegree (k + 1) by rfl) _
          (wedge_contDiffOn _ _ hθform
            (curvaturePowerPathCoeff_contDiffOn Γ θ hs hΓ hθ k w))
      · exact degreeCast_contDiffOn (primitiveDegree_succ_cast k) _
          (wedge_contDiffOn _ _
            (curvatureBaseCoeff_contDiffOn Γ θ hs hΓ hθ i)
            (ih w))

theorem traceOrderedTransgressionForm_contDiffOn
    (T : R →L[ℝ] B) (Γ θ : Form (E := E) (A := R))
    {s : Set E} (hs : IsOpen s)
    (hΓ : ContDiffOn ℝ ∞ Γ s)
    (hθ : ContDiffOn ℝ ∞ θ s)
    (k : ℕ) :
    ContDiffOn ℝ ∞ (traceOrderedTransgressionForm T Γ θ k) s := by
  let F := ContinuousLinearMap.compContinuousAlternatingMapCLM
    (ι := Fin (primitiveDegree k)) ℝ E R B T
  let a : E → E [⋀^Fin (primitiveDegree k)]→L[ℝ] B :=
    fun x => ∑ w : PrimitiveWordIndex k,
      (1 / (primitiveWordExponent k w + 1) : ℝ) •
        F (primitivePathCoeff Γ θ k w x)
  have ha : ContDiffOn ℝ ∞ a s := by
    apply ContDiffOn.sum
    intro w _
    exact ((primitivePathCoeff_contDiffOn Γ θ hs hΓ hθ k w).continuousLinearMap_comp F).const_smul _
  apply ha.congr
  intro x hx
  have hΓx : DifferentiableAt ℝ Γ x :=
    ((hΓ.contDiffAt (hs.mem_nhds hx)).differentiableAt (by norm_num))
  have hθx : DifferentiableAt ℝ θ x :=
    ((hθ.contDiffAt (hs.mem_nhds hx)).differentiableAt (by norm_num))
  change (∫ t in (0 : ℝ)..1,
    T.compContinuousAlternatingMap
      (orderedPrimitive (Γ + t • θ) θ k x)) = _
  calc
    _ = ∫ t in (0 : ℝ)..1,
        ∑ w : PrimitiveWordIndex k,
          t ^ primitiveWordExponent k w •
            F (primitivePathCoeff Γ θ k w x) := by
      apply intervalIntegral.integral_congr
      intro t _
      change F (orderedPrimitive (Γ + t • θ) θ k x) = _
      rw [orderedPrimitive_path_sum Γ θ x hΓx hθx t k]
      simp only [map_sum, map_smul]
    _ = _ := by
      exact integral_weighted_polynomial
        (Finset.univ : Finset (PrimitiveWordIndex k))
        (primitiveWordExponent k)
        (fun w => F (primitivePathCoeff Γ θ k w x))

end
end QuaternionicSymmetry.LocalOrderedPrimitiveSmoothness
