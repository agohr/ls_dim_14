import QuaternionicSymmetry.QuaternionicSevenTenNormalizedBounds
import QuaternionicSymmetry.QuaternionicWeylNormalizedDensity

/-! Apply the exact normalized printed bounds to the finite Hermitian
coefficients of an actual algebraic quaternionic Weyl curvature tensor. -/
namespace QuaternionicSymmetry.QuaternionicSevenTenWeylBounds
open Module QuaternionicCurvatureFiniteExpansion QuaternionicCurvatureOrbitalSign
open QuaternionicWeylMatrixCoefficients ManifoldQuaternionicKSWEq38Input
open QuaternionicFundamental QuaternionicTracePositivity
open QuaternionicNormalizedDensityValues QuaternionicSevenTenNormalizedBounds
open DimensionElevenTwelveDensity PrintedCertificatesSevenTen
noncomputable section

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Fintype ι] (S : QuaternionicStructure E)
  (W : LocalConnection.Bilinear (E := E) (A := E →L[ℝ] E))
  (hW : HyperWeylFiber S W) (b : Basis ι ℝ E)

theorem density7_weyl_lower_bound
    (hn : S.quaternionicDimension = 7) (s : ℝ) (hs : 0 < s)
    (L : CE E →ₗ[ℝ] ℝ) (hL : 0 ≤ L (embed (V := E) (topForm S b))) :
    128 * L ((s ^ 2 • embed (V := E) (form S b)) ^ 7) ≤
      L (MvPolynomial.aeval (normalizedValues S b s
        (fun a : Index S => (tangentSourceMatrixMap S (operatorBasis S a)).val)
        (coefficientExterior S W (HyperWeylFiber.mem_skewCentralizer S hW) b)) rhs7) := by
  have h := density7_lower_bound_normalized (β := Index S) S b hn s hs
  rw [← hn] at h
  simpa only [hn] using h _
    (fun a => (tangentSourceMatrixMap S (operatorBasis S a)).property.1) _
    (coefficientExterior_mem S W (HyperWeylFiber.mem_skewCentralizer S hW)
      b hW.1 hW.2.2.2.2.1) L hL


theorem density8_weyl_lower_bound
    (hn : S.quaternionicDimension = 8) (s : ℝ) (hs : 0 < s)
    (L : CE E →ₗ[ℝ] ℝ) (hL : 0 ≤ L (embed (V := E) (topForm S b))) :
    160 * L ((s ^ 2 • embed (V := E) (form S b)) ^ 8) ≤
      L (MvPolynomial.aeval (normalizedValues S b s
        (fun a : Index S => (tangentSourceMatrixMap S (operatorBasis S a)).val)
        (coefficientExterior S W (HyperWeylFiber.mem_skewCentralizer S hW) b)) rhs8) := by
  have h := density8_lower_bound_normalized (β := Index S) S b hn s hs
  rw [← hn] at h
  simpa only [hn] using h _
    (fun a => (tangentSourceMatrixMap S (operatorBasis S a)).property.1) _
    (coefficientExterior_mem S W (HyperWeylFiber.mem_skewCentralizer S hW)
      b hW.1 hW.2.2.2.2.1) L hL

theorem density9_weyl_lower_bound
    (hn : S.quaternionicDimension = 9) (s : ℝ) (hs : 0 < s)
    (L : CE E →ₗ[ℝ] ℝ) (hL : 0 ≤ L (embed (V := E) (topForm S b))) :
    200 * L ((s ^ 2 • embed (V := E) (form S b)) ^ 9) ≤
      L (MvPolynomial.aeval (normalizedValues S b s
        (fun a : Index S => (tangentSourceMatrixMap S (operatorBasis S a)).val)
        (coefficientExterior S W (HyperWeylFiber.mem_skewCentralizer S hW) b)) rhs9) := by
  have h := density9_lower_bound_normalized (β := Index S) S b hn s hs
  rw [← hn] at h
  simpa only [hn] using h _
    (fun a => (tangentSourceMatrixMap S (operatorBasis S a)).property.1) _
    (coefficientExterior_mem S W (HyperWeylFiber.mem_skewCentralizer S hW)
      b hW.1 hW.2.2.2.2.1) L hL

theorem density10_weyl_lower_bound
    (hn : S.quaternionicDimension = 10) (s : ℝ) (hs : 0 < s)
    (L : CE E →ₗ[ℝ] ℝ) (hL : 0 ≤ L (embed (V := E) (topForm S b))) :
    240 * L ((s ^ 2 • embed (V := E) (form S b)) ^ 10) ≤
      L (MvPolynomial.aeval (normalizedValues S b s
        (fun a : Index S => (tangentSourceMatrixMap S (operatorBasis S a)).val)
        (coefficientExterior S W (HyperWeylFiber.mem_skewCentralizer S hW) b)) rhs10) := by
  have h := density10_lower_bound_normalized (β := Index S) S b hn s hs
  rw [← hn] at h
  simpa only [hn] using h _
    (fun a => (tangentSourceMatrixMap S (operatorBasis S a)).property.1) _
    (coefficientExterior_mem S W (HyperWeylFiber.mem_skewCentralizer S hW)
      b hW.1 hW.2.2.2.2.1) L hL

end
end QuaternionicSymmetry.QuaternionicSevenTenWeylBounds
