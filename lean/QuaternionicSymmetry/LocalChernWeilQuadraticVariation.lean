import QuaternionicSymmetry.LocalChernWeilQuadratic
import QuaternionicSymmetry.LocalConnectionVariation

/-! The first variation of the normalized degree-four Chern--Weil form along
an affine path of actual local connections. This is a step toward the
quadratic transgression formula; it does not assume or assert that formula. -/

namespace QuaternionicSymmetry.LocalChernWeilQuadraticVariation

open QuaternionicSymmetry.LocalConnection QuaternionicSymmetry.LocalConnectionForms
  QuaternionicSymmetry.LocalConnectionVariation
  QuaternionicSymmetry.LocalChernWeilQuadratic
  QuaternionicSymmetry.LocalTraceSquareAlgebra
  QuaternionicSymmetry.ContinuousAlternation
  QuaternionicSymmetry.ContinuousMultilinearProduct

noncomputable section

variable {E R B : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedRing R] [NormedAlgebra ℝ R]
  [NormedAddCommGroup B] [NormedSpace ℝ B]

local instance : NormedSpace ℝ R := NormedAlgebra.toNormedSpace R
local instance : NormedAddCommGroup (E [⋀^Fin 2]→L[ℝ] R) := inferInstance
local instance : NormedSpace ℝ (E [⋀^Fin 2]→L[ℝ] R) := inferInstance
local instance : NormedAddCommGroup (E [⋀^Fin 4]→L[ℝ] B) := inferInstance
local instance : NormedSpace ℝ (E [⋀^Fin 4]→L[ℝ] B) := inferInstance
local instance : NormedAddCommGroup
    ((E [⋀^Fin 2]→L[ℝ] R) →L[ℝ] E [⋀^Fin 4]→L[ℝ] B) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ
    ((E [⋀^Fin 2]→L[ℝ] R) →L[ℝ] E [⋀^Fin 4]→L[ℝ] B) :=
  ContinuousLinearMap.toNormedSpace

private def raw22 (P : R →L[ℝ] R →L[ℝ] B)
    (α β : E [⋀^Fin 2]→L[ℝ] R) :
    ContinuousMultilinearMap ℝ (fun _ : Fin 4 => E) B :=
  (concatenate P α.toContinuousMultilinearMap β.toContinuousMultilinearMap).domDomCongr
    (finSumFinEquiv (m := 2) (n := 2))

private theorem raw22_apply (P : R →L[ℝ] R →L[ℝ] B)
    (α β : E [⋀^Fin 2]→L[ℝ] R) (v : Fin 4 → E) :
    raw22 P α β v = P (α ![v 0, v 1]) (β ![v 2, v 3]) := by
  simp [raw22, concatenate_apply, ContinuousMultilinearMap.domDomCongr_apply,
    finSumFinEquiv]
  have hleft : ((fun i : Fin 2 ⊕ Fin 2 =>
      v (Sum.elim (Fin.castAdd 2 : Fin 2 → Fin 4)
        (Fin.natAdd 2 : Fin 2 → Fin 4) i)) ∘ Sum.inl) =
      ![v 0, v 1] := by
    funext i
    fin_cases i <;> rfl
  have hright : ((fun i : Fin 2 ⊕ Fin 2 =>
      v (Sum.elim (Fin.castAdd 2 : Fin 2 → Fin 4)
        (Fin.natAdd 2 : Fin 2 → Fin 4) i)) ∘ Sum.inr) =
      ![v 2, v 3] := by
    funext i
    fin_cases i <;> rfl
  rw [hleft, hright]

private def blockSwap : Equiv.Perm (Fin 4) :=
  (Equiv.swap 0 2) * (Equiv.swap 1 3)

private theorem blockSwap_sign : Equiv.Perm.sign blockSwap = 1 := by
  decide

theorem wedge22_cyclic (P : R →L[ℝ] R →L[ℝ] B)
    (hP : ∀ a b : R, P a b = P b a)
    (α β : E [⋀^Fin 2]→L[ℝ] R) :
    wedge22 P α β = wedge22 P β α := by
  have hraw : raw22 P β α = (raw22 P α β).domDomCongr blockSwap := by
    ext v
    rw [raw22_apply, ContinuousMultilinearMap.domDomCongr_apply]
    simp only [raw22_apply]
    have h0 : blockSwap 0 = 2 := by decide
    have h1 : blockSwap 1 = 3 := by decide
    have h2 : blockSwap 2 = 0 := by decide
    have h3 : blockSwap 3 = 1 := by decide
    rw [h0, h1, h2, h3]
    simpa using (hP (α ![v 2, v 3]) (β ![v 0, v 1])).symm
  ext v
  change ((4⁻¹ : ℝ) • alternationCLM (raw22 P α β)) v =
    ((4⁻¹ : ℝ) • alternationCLM (raw22 P β α)) v
  rw [hraw, alternation_domDomCongr, blockSwap_sign, one_smul]

/-- Product rule for the normalized `2∧2` form, with the curvature variation
identified as the covariant derivative of the path direction. -/
theorem wedge22_curvature_path_hasDerivAt
    (P : R →L[ℝ] R →L[ℝ] B)
    (Γ θ : Form (E := E) (A := R)) (x : E)
    (hΓ : DifferentiableAt ℝ Γ x) (hθ : DifferentiableAt ℝ θ x) (t : ℝ) :
    HasDerivAt (fun s : ℝ => wedge22 P
      (curvatureForm (Γ + s • θ) x) (curvatureForm (Γ + s • θ) x))
      (wedge22 P (covariantDerivativeForm (Γ + t • θ) θ x)
          (curvatureForm (Γ + t • θ) x) +
       wedge22 P (curvatureForm (Γ + t • θ) x)
          (covariantDerivativeForm (Γ + t • θ) θ x)) t := by
  let f : ℝ → E [⋀^Fin 2]→L[ℝ] R :=
    fun s => curvatureForm (Γ + s • θ) x
  let dF : E [⋀^Fin 2]→L[ℝ] R :=
    covariantDerivativeForm (Γ + t • θ) θ x
  have hf : HasDerivAt f dF t :=
    curvatureForm_path_hasDerivAt Γ θ x hΓ hθ t
  have hc : HasDerivAt (fun _ : ℝ =>
      wedge22CLM (E := E) (A := R) (B := R) (C := B) P) 0 t :=
    hasDerivAt_const t (wedge22CLM (E := E) (A := R) (B := R) (C := B) P)
  have hfirst : HasDerivAt (fun s =>
      wedge22CLM (E := E) (A := R) (B := R) (C := B) P (f s))
      (wedge22CLM (E := E) (A := R) (B := R) (C := B) P dF) t := by
    simpa using (HasDerivAt.clm_apply
      (F := E [⋀^Fin 2]→L[ℝ] R)
      (G := (E [⋀^Fin 2]→L[ℝ] R) →L[ℝ] E [⋀^Fin 4]→L[ℝ] B)
      hc hf)
  have hsecond := HasDerivAt.clm_apply
    (F := E [⋀^Fin 2]→L[ℝ] R)
    (G := E [⋀^Fin 4]→L[ℝ] B) hfirst hf
  simpa only [f, dF, wedge22CLM_apply] using hsecond

/-- Actual first variation of `T(F∧F)`; the two terms keep their order in the
possibly noncommutative coefficient algebra. -/
theorem traceSquareForm_path_hasDerivAt (T : R →L[ℝ] B)
    (Γ θ : Form (E := E) (A := R)) (x : E)
    (hΓ : DifferentiableAt ℝ Γ x) (hθ : DifferentiableAt ℝ θ x) (t : ℝ) :
    HasDerivAt (fun s : ℝ => traceSquareForm T (Γ + s • θ) x)
      (wedge22 (traceProduct T) (covariantDerivativeForm (Γ + t • θ) θ x)
          (curvatureForm (Γ + t • θ) x) +
       wedge22 (traceProduct T) (curvatureForm (Γ + t • θ) x)
          (covariantDerivativeForm (Γ + t • θ) θ x)) t :=
  wedge22_curvature_path_hasDerivAt (traceProduct T) Γ θ x hΓ hθ t

theorem traceSquareForm_path_deriv (T : R →L[ℝ] B)
    (Γ θ : Form (E := E) (A := R)) (x : E)
    (hΓ : DifferentiableAt ℝ Γ x) (hθ : DifferentiableAt ℝ θ x) (t : ℝ) :
    deriv (fun s : ℝ => traceSquareForm T (Γ + s • θ) x) t =
      wedge22 (traceProduct T) (covariantDerivativeForm (Γ + t • θ) θ x)
          (curvatureForm (Γ + t • θ) x) +
      wedge22 (traceProduct T) (curvatureForm (Γ + t • θ) x)
          (covariantDerivativeForm (Γ + t • θ) θ x) :=
  (traceSquareForm_path_hasDerivAt T Γ θ x hΓ hθ t).deriv

/-- Cyclicity makes the two first-variation terms equal, giving the expected
factor `2` for the trace square. -/
theorem traceSquareForm_path_deriv_cyclic (T : R →L[ℝ] B)
    (hT : ∀ a b : R, T (a * b) = T (b * a))
    (Γ θ : Form (E := E) (A := R)) (x : E)
    (hΓ : DifferentiableAt ℝ Γ x) (hθ : DifferentiableAt ℝ θ x) (t : ℝ) :
    deriv (fun s : ℝ => traceSquareForm T (Γ + s • θ) x) t =
      (2 : ℝ) • wedge22 (traceProduct T)
        (covariantDerivativeForm (Γ + t • θ) θ x)
        (curvatureForm (Γ + t • θ) x) := by
  rw [traceSquareForm_path_deriv T Γ θ x hΓ hθ t]
  rw [wedge22_cyclic (traceProduct T)
    (fun a b => hT a b) (curvatureForm (Γ + t • θ) x)
      (covariantDerivativeForm (Γ + t • θ) θ x)]
  module

end
end QuaternionicSymmetry.LocalChernWeilQuadraticVariation
