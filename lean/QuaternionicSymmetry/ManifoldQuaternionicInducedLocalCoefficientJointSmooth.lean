import QuaternionicSymmetry.ManifoldQuaternionicInducedLocalCoefficientSmooth
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! Operator-norm and joint smoothness of the genuine induced coefficient
map in fixed adapted charts. -/
namespace QuaternionicSymmetry.ManifoldQuaternionicInducedLocalCoefficientJointSmooth
open ManifoldPositiveQuaternionicKahlerGeometry
open ManifoldQuaternionicSubmanifoldInput
open ManifoldQuaternionicInducedLocalIntertwining
open ManifoldQuaternionicInducedLocalCoefficientSmooth
open scoped Manifold ContDiff
noncomputable section

variable {E F M N : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [FiniteDimensional ℝ F] [Nontrivial F]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℝ,F) ∞ N]
variable (P : PositiveQuaternionicKahlerGeometry (E := E) (M := M))
  (R : PositiveQuaternionicKahlerGeometry (E := F) (M := N))
  (ι : N → M)
  (hSmooth : ContMDiff 𝓘(ℝ,F) 𝓘(ℝ,E) ∞ ι)
  (hι : ∀ x, Function.Injective (mfderiv 𝓘(ℝ,F) 𝓘(ℝ,E) ι x))
  (hR : IsInducedQuaternionicGeometry P R ι)

def localCoefficientCLM (i : atlas F N) (j : atlas E M) (x : N) :
    (Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ) :=
  LinearMap.toContinuousLinearMap (localCoefficientMap P R ι hι hR i j x)

include hSmooth in
theorem localCoefficientCLM_smoothAt_center (c : N) :
    ContMDiffAt 𝓘(ℝ,F)
      𝓘(ℝ,(Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ)) ∞
      (fun x => localCoefficientCLM P R ι hι hR
        (achart F c) (achart E (ι c)) x) c := by
  let i := achart F c
  let j := achart E (ι c)
  let e := ContinuousLinearEquiv.piRing (𝕜 := ℝ)
    (E := Fin 3 → ℝ) (Fin 3)
  have hcols : ContMDiffAt 𝓘(ℝ,F)
      𝓘(ℝ,Fin 3 → Fin 3 → ℝ) ∞
      (fun x => fun t : Fin 3 =>
        localCoefficientMap P R ι hι hR i j x (Pi.single t (1 : ℝ))) c := by
    apply contMDiffAt_pi_space.mpr
    intro t
    exact localCoefficientMap_apply_smoothAt_center P R ι hSmooth hι hR c
      (Pi.single t 1)
  have heq (x : N) :
      e.symm (fun t : Fin 3 =>
        localCoefficientMap P R ι hι hR i j x (Pi.single t (1 : ℝ))) =
      localCoefficientCLM P R ι hι hR i j x := by
    apply e.injective
    rw [e.apply_symm_apply]
    ext t k
    simp [e, ContinuousLinearEquiv.piRing, LinearEquiv.piRing_apply,
      LinearEquiv.trans_apply, localCoefficientCLM]
  have h := e.symm.toContinuousLinearMap.contMDiff.contMDiffAt.comp c hcols
  change ContMDiffAt 𝓘(ℝ,F)
    𝓘(ℝ,(Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ)) ∞
    (fun x => e.symm (fun t : Fin 3 =>
      localCoefficientMap P R ι hι hR i j x (Pi.single t (1 : ℝ)))) c at h
  have heqfun : (fun x => e.symm (fun t : Fin 3 =>
      localCoefficientMap P R ι hι hR i j x (Pi.single t (1 : ℝ)))) =
      (fun x => localCoefficientCLM P R ι hι hR i j x) := by
    funext x
    exact heq x
  rw [heqfun] at h
  exact h

include hSmooth in
/-- Joint smoothness in a base point and arbitrary rank-three coefficient
vector. This is the precise local product-chart fiber formula. -/
theorem localCoefficientMap_jointSmoothAt_center
    (c : N) (a : Fin 3 → ℝ) :
    ContMDiffAt (𝓘(ℝ,F).prod 𝓘(ℝ,Fin 3 → ℝ))
      𝓘(ℝ,Fin 3 → ℝ) ∞
      (fun p : N × (Fin 3 → ℝ) =>
        localCoefficientMap P R ι hι hR
          (achart F c) (achart E (ι c)) p.1 p.2) (c,a) := by
  have hMat : ContMDiffAt (𝓘(ℝ,F).prod 𝓘(ℝ,Fin 3 → ℝ))
      𝓘(ℝ,(Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ)) ∞
      (fun p : N × (Fin 3 → ℝ) =>
        localCoefficientCLM P R ι hι hR
          (achart F c) (achart E (ι c)) p.1) (c,a) :=
    ContMDiffAt.comp (f := Prod.fst) (x := (c,a))
      (localCoefficientCLM_smoothAt_center P R ι hSmooth hι hR c)
      contMDiffAt_fst
  have hCoeff : ContMDiffAt (𝓘(ℝ,F).prod 𝓘(ℝ,Fin 3 → ℝ))
      𝓘(ℝ,Fin 3 → ℝ) ∞
      (fun p : N × (Fin 3 → ℝ) => p.2) (c,a) := contMDiffAt_snd
  exact hMat.clm_apply hCoeff

end
end QuaternionicSymmetry.ManifoldQuaternionicInducedLocalCoefficientJointSmooth
