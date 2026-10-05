import QuaternionicSymmetry.GeneralLeviCivitaReflectionEndomorphismCancellation
import QuaternionicSymmetry.GeneralSmoothZeroSectionDerivative

/-! Reflection cancellation plus the zero-section derivative principle
forces the ordinary Levi-Civita covariant derivative of any invariant
subbundle section to remain inside its fiber. -/

namespace QuaternionicSymmetry.GeneralLeviCivitaReflectedPlaneParallel

open Filter GeneralLeviCivitaReflectionEndomorphismCancellation
open GeneralSmoothZeroSectionDerivative
open scoped ContDiff Topology
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def covariantEndomorphismMap (Γ : E →L[ℝ] E →L[ℝ] E)
    (S : E → E →L[ℝ] E) (y u : E) : E →L[ℝ] E :=
  fderiv ℝ S y u + (Γ u).comp (S y) - (S y).comp (Γ u)

theorem covariantEndomorphismMap_apply
    (Γ : E →L[ℝ] E →L[ℝ] E)
    (S : E → E →L[ℝ] E) (y u v : E) :
    covariantEndomorphismMap Γ S y u v =
      covariantEndomorphismJet Γ S y u v := by
  rfl

theorem covariantEndomorphismMap_mem_of_reflected_cancellation
    (Γ : E →L[ℝ] E →L[ℝ] E)
    (S B : E → E →L[ℝ] E) (P : E → (E →L[ℝ] E) →L[ℝ] (E →L[ℝ] E))
    (K : Submodule ℝ (E →L[ℝ] E)) (y u : E)
    (hS : DifferentiableAt ℝ S y)
    (hB : DifferentiableAt ℝ B y)
    (hP : DifferentiableAt ℝ P y)
    (hcenter : S y = B y)
    (hfix : ∀ᶠ z in 𝓝 y, P z (S z - B z) = S z - B z)
    (hrange : ∀ T, P y T ∈ K)
    (hcancel : ∀ v,
      covariantEndomorphismJet Γ S y u v +
        covariantEndomorphismJet Γ B y u v = 0) :
    covariantEndomorphismMap Γ S y u ∈ K := by
  let D := fun z => S z - B z
  have hD : DifferentiableAt ℝ D y := hS.sub hB
  have hDzero : D y = 0 := by simp [D, hcenter]
  have hDmem : (fderiv ℝ D y) u ∈ K :=
    zero_section_fderiv_mem P D K y u hP hD hDzero hfix hrange
  have hDderiv : fderiv ℝ D y = fderiv ℝ S y - fderiv ℝ B y := by
    simpa only [Pi.sub_apply] using (fderiv_sub hS hB)
  let JS := covariantEndomorphismMap Γ S y u
  let JB := covariantEndomorphismMap Γ B y u
  have hsum : JS + JB = 0 := by
    ext v
    exact hcancel v
  have hBneg : JB = -JS := by
    calc
      JB = JS + JB - JS := by abel
      _ = 0 - JS := by rw [hsum]
      _ = -JS := by simp
  have hdiff : (fderiv ℝ D y) u = JS - JB := by
    rw [hDderiv]
    simp only [ContinuousLinearMap.sub_apply]
    change (fderiv ℝ S y) u - (fderiv ℝ B y) u =
      ((fderiv ℝ S y) u + (Γ u).comp (S y) - (S y).comp (Γ u)) -
        ((fderiv ℝ B y) u + (Γ u).comp (B y) - (B y).comp (Γ u))
    rw [hcenter]
    abel
  have htwomem : (2 : ℝ) • JS ∈ K := by
    simpa only [hdiff, hBneg, sub_neg_eq_add, two_smul] using hDmem
  have hhalf : JS = ((1 / 2 : ℝ) • ((2 : ℝ) • JS)) := by
    simp [smul_smul]
  change JS ∈ K
  rw [hhalf]
  exact K.smul_mem _ htwomem

end
end QuaternionicSymmetry.GeneralLeviCivitaReflectedPlaneParallel
