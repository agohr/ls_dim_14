import QuaternionicSymmetry.LocalConnectionGauge
import QuaternionicSymmetry.LocalConnectionForms

/-! Local projective gauge descent for genuine connection and curvature forms.

A pair of inverse matrix lifts can change by the central sign on different
components of an overlap.  The sign need only be fixed in a neighborhood of
the point under consideration.  The results below prove that the connection
and its curvature are independent of that choice, and that gauge changes
compose under a projective (rather than strict) cocycle.  They do not construct
the global quaternionic frame bundle or its projective standard bundle. -/

namespace QuaternionicSymmetry.LocalProjectiveGauge

open LocalConnection LocalConnectionGauge LocalConnectionForms
open scoped Topology

noncomputable section

variable {E A : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedRing A] [NormedAlgebra ℝ A]

/-- Two local pairs of gauge lifts agree up to the same locally fixed central
sign.  The same sign on the inverse lift is essential. -/
def SignedTransitionGerm (g₁ h₁ g₂ h₂ : E → A) (x : E) : Prop :=
  (g₁ =ᶠ[𝓝 x] g₂ ∧ h₁ =ᶠ[𝓝 x] h₂) ∨
    (g₁ =ᶠ[𝓝 x] -g₂ ∧ h₁ =ᶠ[𝓝 x] -h₂)

theorem transform_congr_germ (Γ : Form (E := E) (A := A))
    (g₁ h₁ g₂ h₂ : E → A) (x : E)
    (hg : g₁ =ᶠ[𝓝 x] g₂) (hh : h₁ =ᶠ[𝓝 x] h₂) :
    transform Γ g₁ h₁ =ᶠ[𝓝 x] transform Γ g₂ h₂ := by
  filter_upwards [hg, hh, hg.fderiv (𝕜 := ℝ)] with y hgy hhy hD
  ext v
  simp only [transform_apply, hgy, hhy, hD]

theorem transform_congr_signed_germ (Γ : Form (E := E) (A := A))
    (g₁ h₁ g₂ h₂ : E → A) (x : E)
    (h : SignedTransitionGerm g₁ h₁ g₂ h₂ x) :
    transform Γ g₁ h₁ =ᶠ[𝓝 x] transform Γ g₂ h₂ := by
  rcases h with ⟨hg, hh⟩ | ⟨hg, hh⟩
  · exact transform_congr_germ Γ g₁ h₁ g₂ h₂ x hg hh
  · simpa only [transform_neg] using
      (transform_congr_germ Γ g₁ h₁ (-g₂) (-h₂) x hg hh)

theorem adjointForm_congr_signed_germ (θ : Form (E := E) (A := A))
    (g₁ h₁ g₂ h₂ : E → A) (x : E)
    (h : SignedTransitionGerm g₁ h₁ g₂ h₂ x) :
    adjointForm θ g₁ h₁ =ᶠ[𝓝 x] adjointForm θ g₂ h₂ := by
  rcases h with ⟨hg, hh⟩ | ⟨hg, hh⟩
  · filter_upwards [hg, hh] with y hgy hhy
    ext v
    simp only [adjointForm_apply, hgy, hhy]
  · have h' : adjointForm θ g₁ h₁ =ᶠ[𝓝 x] adjointForm θ (-g₂) (-h₂) := by
      filter_upwards [hg, hh] with y hgy hhy
      ext v
      simp only [adjointForm_apply, hgy, hhy]
    simpa only [adjointForm_neg] using h'

theorem curvature_congr_of_germ (Γ₁ Γ₂ : Form (E := E) (A := A)) (x v w : E)
    (h : Γ₁ =ᶠ[𝓝 x] Γ₂) : curvature Γ₁ x v w = curvature Γ₂ x v w := by
  simp only [curvature_apply, h.eq_of_nhds, h.fderiv_eq (𝕜 := ℝ)]

theorem curvatureForm_congr_signed_germ (Γ : Form (E := E) (A := A))
    (g₁ h₁ g₂ h₂ : E → A) (x : E)
    (h : SignedTransitionGerm g₁ h₁ g₂ h₂ x) :
    curvatureForm (transform Γ g₁ h₁) x = curvatureForm (transform Γ g₂ h₂) x := by
  ext v
  simpa only [curvatureForm_apply] using
    curvature_congr_of_germ (transform Γ g₁ h₁) (transform Γ g₂ h₂) x
      (v 0) (v 1) (transform_congr_signed_germ Γ g₁ h₁ g₂ h₂ x h)

/-- The product of two gauge lifts is projectively the direct lift, on a
neighborhood of `x`.  This is the local cocycle hypothesis needed below. -/
def ProjectiveCocycleAt (gij hij gjk hjk gik hik : E → A) (x : E) : Prop :=
  SignedTransitionGerm (fun y => gij y * gjk y) (fun y => hjk y * hij y) gik hik x

theorem transform_comp_projective_germ (Γ : Form (E := E) (A := A))
    (gij hij gjk hjk gik hik : E → A) (x : E)
    (hregular : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ gij y ∧
      DifferentiableAt ℝ gjk y ∧ hij y * gij y = 1)
    (hcocycle : ProjectiveCocycleAt gij hij gjk hjk gik hik x) :
    transform (transform Γ gij hij) gjk hjk =ᶠ[𝓝 x]
      transform Γ gik hik := by
  have hcomp : transform (transform Γ gij hij) gjk hjk =ᶠ[𝓝 x]
      transform Γ (fun y => gij y * gjk y) (fun y => hjk y * hij y) := by
    filter_upwards [hregular] with y hy
    exact transform_comp Γ gij hij gjk hjk y hy.1 hy.2.1 hy.2.2
  exact hcomp.trans (transform_congr_signed_germ Γ _ _ gik hik x hcocycle)

theorem transform_congr_connection_germ (Γ₁ Γ₂ : Form (E := E) (A := A))
    (g h : E → A) (x : E) (hΓ : Γ₁ =ᶠ[𝓝 x] Γ₂) :
    transform Γ₁ g h =ᶠ[𝓝 x] transform Γ₂ g h := by
  filter_upwards [hΓ] with y hy
  ext v
  simp only [transform_apply, hy]

/-- If the connection and solder form obey their respective gauge laws,
every member of the connection path obeys the same transition law. -/
theorem path_transition (Γi Γj θi θj : Form (E := E) (A := A))
    (g h : E → A) (x : E) (t : ℝ)
    (hΓ : Γj =ᶠ[𝓝 x] transform Γi g h)
    (hθ : θj =ᶠ[𝓝 x] adjointForm θi g h) :
    Γj + t • θj =ᶠ[𝓝 x] transform (Γi + t • θi) g h := by
  filter_upwards [hΓ, hθ] with y hΓy hθy
  calc
    (Γj + t • θj) y = (transform Γi g h + t • adjointForm θi g h) y := by
      simp only [Pi.add_apply, Pi.smul_apply, hΓy, hθy]
    _ = transform (Γi + t • θi) g h y :=
      congrArg (fun Φ : Form (E := E) (A := A) => Φ y)
        (transform_path Γi θi g h t).symm

/-- Local connection forms satisfying two overlap laws also satisfy the
direct overlap law when the lifts form a projective cocycle. -/
theorem connection_transition_transitive (Γi Γj Γk : Form (E := E) (A := A))
    (gij hij gjk hjk gik hik : E → A) (x : E)
    (hpatchij : Γj =ᶠ[𝓝 x] transform Γi gij hij)
    (hpatchjk : Γk =ᶠ[𝓝 x] transform Γj gjk hjk)
    (hregular : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ gij y ∧
      DifferentiableAt ℝ gjk y ∧ hij y * gij y = 1)
    (hcocycle : ProjectiveCocycleAt gij hij gjk hjk gik hik x) :
    Γk =ᶠ[𝓝 x] transform Γi gik hik :=
  hpatchjk.trans ((transform_congr_connection_germ Γj (transform Γi gij hij)
    gjk hjk x hpatchij).trans
      (transform_comp_projective_germ Γi gij hij gjk hjk gik hik x hregular hcocycle))

/-- Curvature of locally related connection forms patches by conjugation;
this is an identity of actual alternating two-forms. -/
theorem curvatureForm_transition (Γi Γj : Form (E := E) (A := A))
    (g h : E → A) (x : E)
    (hpatch : Γj =ᶠ[𝓝 x] transform Γi g h)
    (hΓ : DifferentiableAt ℝ Γi x) (hg : ContDiffAt ℝ 2 g x)
    (hh : DifferentiableAt ℝ h x)
    (hleft : (fun y => h y * g y) =ᶠ[𝓝 x] fun _ => 1)
    (hright : g x * h x = 1) (v : Fin 2 → E) :
    curvatureForm Γj x v = h x * curvatureForm Γi x v * g x := by
  rw [curvatureForm_apply, curvature_congr_of_germ Γj (transform Γi g h)
    x (v 0) (v 1) hpatch]
  rw [curvature_transform Γi g h x hΓ hg hh hleft hright (v 0) (v 1)]
  rw [curvatureForm_apply]

theorem curvatureForm_comp_projective (Γ : Form (E := E) (A := A))
    (gij hij gjk hjk gik hik : E → A) (x : E)
    (hregular : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ gij y ∧
      DifferentiableAt ℝ gjk y ∧ hij y * gij y = 1)
    (hcocycle : ProjectiveCocycleAt gij hij gjk hjk gik hik x) :
    curvatureForm (transform (transform Γ gij hij) gjk hjk) x =
      curvatureForm (transform Γ gik hik) x := by
  ext v
  simpa only [curvatureForm_apply] using
    curvature_congr_of_germ (transform (transform Γ gij hij) gjk hjk)
      (transform Γ gik hik) x (v 0) (v 1)
      (transform_comp_projective_germ Γ gij hij gjk hjk gik hik x hregular hcocycle)

end
end QuaternionicSymmetry.LocalProjectiveGauge
