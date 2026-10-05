import QuaternionicSymmetry.LocalProjectiveGauge
import QuaternionicSymmetry.CyclicTraceConjugation

/-! Gauge invariance of ordered trace words in actual local curvature
coefficients.  The list may have any length, so this supplies the pointwise
invariant-polynomial algebra for higher trace forms.  Closure and their exterior
normalization are separate differential-form statements. -/

namespace QuaternionicSymmetry.LocalTraceWordGauge

open QuaternionicSymmetry.LocalConnection QuaternionicSymmetry.LocalConnectionGauge
  QuaternionicSymmetry.LocalConnectionForms QuaternionicSymmetry.LocalProjectiveGauge
  QuaternionicSymmetry.CyclicTraceConjugation
open scoped Topology

noncomputable section

variable {E A B : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedRing A] [NormedAlgebra ℝ A]
  [NormedAddCommGroup B] [NormedSpace ℝ B]

local instance : NormedSpace ℝ A := NormedAlgebra.toNormedSpace A

/-- Every ordered product of local curvature coefficients has the same cyclic
trace on two charts related by an honest inverse-pair gauge transformation.
The empty list is included and uses both inverse identities. -/
theorem trace_curvature_word_transition
    (T : A →L[ℝ] B) (hT : ∀ a b : A, T (a * b) = T (b * a))
    (Γi Γj : Form (E := E) (A := A)) (g h : E → A) (x : E)
    (hpatch : Γj =ᶠ[𝓝 x] transform Γi g h)
    (hΓ : DifferentiableAt ℝ Γi x) (hg : ContDiffAt ℝ 2 g x)
    (hh : DifferentiableAt ℝ h x)
    (hleft : (fun y => h y * g y) =ᶠ[𝓝 x] fun _ => 1)
    (hright : g x * h x = 1) (vs : List (Fin 2 → E)) :
    T ((vs.map (fun v => curvatureForm Γj x v)).prod) =
      T ((vs.map (fun v => curvatureForm Γi x v)).prod) := by
  have hright' : g x * h x = 1 := hright
  have hleft' : h x * g x = 1 := hleft.eq_of_nhds
  have hmap :
      vs.map (fun v => curvatureForm Γj x v) =
        vs.map (fun v => h x * curvatureForm Γi x v * g x) := by
    induction vs with
    | nil => rfl
    | cons v vs ih =>
        simp only [List.map_cons]
        rw [curvatureForm_transition Γi Γj g h x hpatch hΓ hg hh hleft hright v, ih]
  rw [hmap]
  have hmap' :
      vs.map (fun v => h x * curvatureForm Γi x v * g x) =
        (vs.map (fun v => curvatureForm Γi x v)).map
          (fun a => h x * a * g x) := by
    simp only [List.map_map, Function.comp_def]
  rw [hmap']
  exact cyclic_trace_conjugated_list_prod T hT (g x) (h x)
    hright' hleft' (vs.map (fun v => curvatureForm Γi x v))

end
end QuaternionicSymmetry.LocalTraceWordGauge
