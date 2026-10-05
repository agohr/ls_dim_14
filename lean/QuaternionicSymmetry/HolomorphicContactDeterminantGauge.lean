import QuaternionicSymmetry.HolomorphicContactDeterminantDensity

/-! Assembly of the contact determinant density into a genuine holomorphic
line-bundle isomorphism. -/
namespace QuaternionicSymmetry.HolomorphicContactDeterminantGauge
open HolomorphicContactDeterminantDensity HolomorphicDeterminantLine
  HolomorphicLinePowers HolomorphicLineGauge
open scoped Manifold ContDiff
noncomputable section
variable {V M : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [FiniteDimensional ℂ V] [TopologicalSpace M] [ChartedSpace V M]
  [IsManifold 𝓘(ℂ,V) ∞ M]
  {ι : Type*} (L : VectorBundleCore ℂ M ℂ ι) [L.IsContMDiff 𝓘(ℂ,V) ∞]
  (θ : ∀ x : M, TangentSpace 𝓘(ℂ,V) x →ₗ[ℂ] L.Fiber x)
  (hθ : ContMDiff (𝓘(ℂ,V)).tangent ((𝓘(ℂ,V)).prod 𝓘(ℂ,ℂ)) ∞
      (fun t : TangentBundle 𝓘(ℂ,V) M =>
        (⟨t.1, θ t.1 t.2⟩ : Bundle.TotalSpace ℂ L.Fiber)))
  (hN : ∀ (i : atlas V M) (a : ι) (x : M), x ∈ i.1.source → x ∈ L.baseSet a →
    density L θ i a x ≠ 0)

/-- The squared determinant line of the tangent bundle. -/
def squareAnticanonicalCore : VectorBundleCore ℂ M ℂ (atlas V M) :=
  powerCore (determinantCore (tangentBundleCore 𝓘(ℂ,V) M)) 2

instance squareAnticanonicalCore_holomorphic :
    (squareAnticanonicalCore (V := V) (M := M)).IsContMDiff 𝓘(ℂ,V) ∞ := by
  letI : IsManifold 𝓘(ℂ,V) (∞+1) M := by simpa using (inferInstance : IsManifold 𝓘(ℂ,V) ∞ M)
  letI : (tangentBundleCore 𝓘(ℂ,V) M).IsContMDiff 𝓘(ℂ,V) ∞ := tangentBundleCore.isContMDiff
  exact powerCore_isContMDiff (Z := determinantCore (tangentBundleCore 𝓘(ℂ,V) M))
    (IB := 𝓘(ℂ,V)) 2

/-- The contact determinant proves `(det TZ)^2 ≅ L^(dim Z + 1)`. -/
def squareGauge : GaugeIso (IB := 𝓘(ℂ,V))
    (squareAnticanonicalCore (V := V) (M := M))
    (powerCore L (Module.finrank ℂ V + 1)) where
  forward := density L θ
  backward a i x := (density L θ i a x)⁻¹
  forward_holomorphic i a x hx :=
    (density_contMDiffAt L θ hθ i a x hx.1 hx.2).contMDiffWithinAt
  backward_holomorphic a i x hx :=
    ((density_contMDiffAt L θ hθ i a x hx.2 hx.1).inv₀ (hN i a x hx.2 hx.1)).contMDiffWithinAt
  forward_compat i j a b x hx := by
    have h := density_covariance L θ hθ i j a b x hx.1.1.1 hx.1.1.2 hx.1.2 hx.2
    simpa [squareAnticanonicalCore, powerCore, determinantCore, transitionDet,
      transitionScalar, mul_comm] using h.symm
  backward_compat a b i j x hx := by
    have h := density_covariance L θ hθ i j a b x hx.1.2 hx.2 hx.1.1.1 hx.1.1.2
    have hni := hN i a x hx.1.2 hx.1.1.1
    have hnj := hN j b x hx.2 hx.1.1.2
    simp only [squareAnticanonicalCore, powerCore, determinantCore, transitionScalar,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul,
      mul_one, transitionDet]
    field_simp
    simpa only [transitionScalar, mul_comm] using h
  left_inverse i a x hx := inv_mul_cancel₀ (hN i a x hx.1 hx.2)
  right_inverse a i x hx := mul_inv_cancel₀ (hN i a x hx.2 hx.1)

end
end QuaternionicSymmetry.HolomorphicContactDeterminantGauge
