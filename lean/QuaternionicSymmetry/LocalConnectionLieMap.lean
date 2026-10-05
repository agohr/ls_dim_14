import QuaternionicSymmetry.LocalConnection

/-! Actual curvature commutes with a continuous linear map that preserves
the Lie brackets of the connection values. -/
namespace QuaternionicSymmetry.LocalConnectionLieMap
open scoped Topology
noncomputable section
variable {E A B : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedRing A] [NormedAlgebra ℝ A] [NormedRing B] [NormedAlgebra ℝ B]

def mapForm (L : A →L[ℝ] B) (Γ : LocalConnection.Form (E := E) (A := A)) :
    LocalConnection.Form (E := E) (A := B) := fun y => L.comp (Γ y)

theorem fderiv_mapForm (L : A →L[ℝ] B)
    (Γ : LocalConnection.Form (E := E) (A := A)) (x : E)
    (hΓ : DifferentiableAt ℝ Γ x) :
    fderiv ℝ (mapForm L Γ) x =
      (ContinuousLinearMap.compL ℝ E A B L).comp (fderiv ℝ Γ x) := by
  let T := ContinuousLinearMap.compL ℝ E A B L
  change fderiv ℝ (T ∘ Γ) x = T.comp (fderiv ℝ Γ x)
  simpa only [T.fderiv] using fderiv_comp x (g := T) T.differentiableAt hΓ

theorem curvature_map (L : A →L[ℝ] B)
    (Γ : LocalConnection.Form (E := E) (A := A)) (x u v : E)
    (hΓ : DifferentiableAt ℝ Γ x)
    (hbracket : L (Γ x u * Γ x v - Γ x v * Γ x u) =
      L (Γ x u) * L (Γ x v) - L (Γ x v) * L (Γ x u)) :
    LocalConnection.curvature (mapForm L Γ) x u v =
      L (LocalConnection.curvature Γ x u v) := by
  rw [LocalConnection.curvature_apply, LocalConnection.curvature_apply,
    fderiv_mapForm L Γ x hΓ]
  change L (fderiv ℝ Γ x u v) - L (fderiv ℝ Γ x v u) +
      L (Γ x u) * L (Γ x v) - L (Γ x v) * L (Γ x u) = _
  calc
    _ = L (fderiv ℝ Γ x u v - fderiv ℝ Γ x v u) +
        L (Γ x u * Γ x v - Γ x v * Γ x u) := by
      rw [map_sub, hbracket]
      abel
    _ = _ := by rw [← map_add]; congr 1; abel

theorem curvature_congr_germ (Γ θ : LocalConnection.Form (E := E) (A := A))
    (x : E) (h : Γ =ᶠ[𝓝 x] θ) :
    LocalConnection.curvature Γ x = LocalConnection.curvature θ x := by
  ext u v
  simp only [LocalConnection.curvature_apply, h.fderiv_eq, h.self_of_nhds]

theorem curvature_map_composite {C : Type*} [NormedRing C] [NormedAlgebra ℝ C]
    (L : A →L[ℝ] B) (K : B →L[ℝ] C)
    (Γ : LocalConnection.Form (E := E) (A := A)) (x u v : E)
    (hΓ : DifferentiableAt ℝ Γ x)
    (hbracket : K (L (Γ x u * Γ x v - Γ x v * Γ x u)) =
      K (L (Γ x u)) * K (L (Γ x v)) - K (L (Γ x v)) * K (L (Γ x u))) :
    LocalConnection.curvature (mapForm (K.comp L) Γ) x u v =
      K (L (LocalConnection.curvature Γ x u v)) :=
  curvature_map (K.comp L) Γ x u v hΓ hbracket

end
end QuaternionicSymmetry.LocalConnectionLieMap
