import QuaternionicSymmetry.ContinuousMultilinearProduct
import QuaternionicSymmetry.LocalEndomorphismTrace
import QuaternionicSymmetry.LocalCovariantExterior
import QuaternionicSymmetry.LocalTraceSquareAlgebra

/-! A normalized product of continuous alternating two-forms. This uses the
actual alternation of the concatenated multilinear product, divided by
`2! 2! = 4`, so it is the usual exterior-product convention. -/

namespace QuaternionicSymmetry.LocalChernWeilQuadratic

open QuaternionicSymmetry.ContinuousAlternation
  QuaternionicSymmetry.ContinuousMultilinearProduct
  QuaternionicSymmetry.LocalConnection QuaternionicSymmetry.LocalConnectionForms
  QuaternionicSymmetry.LocalConnectionExterior
  QuaternionicSymmetry.LocalCovariantExterior
  QuaternionicSymmetry.LocalEndomorphismTrace ContinuousAlternatingMap
  QuaternionicSymmetry.LocalTraceSquareAlgebra

noncomputable section

variable {E A B C : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup B] [NormedSpace ℝ B]
  [NormedAddCommGroup C] [NormedSpace ℝ C]

local instance : NormedAddCommGroup (E [⋀^Fin 2]→L[ℝ] A) := inferInstance
local instance : NormedSpace ℝ (E [⋀^Fin 2]→L[ℝ] A) := inferInstance
local instance : NormedAddCommGroup (E [⋀^Fin 2]→L[ℝ] B) := inferInstance
local instance : NormedSpace ℝ (E [⋀^Fin 2]→L[ℝ] B) := inferInstance

/-- Exterior product with a specified continuous bilinear pairing on coefficients.
The factor `1/4` is `1/(2!2!)`, not an arbitrary rescaling. -/
def wedge22 (P : A →L[ℝ] B →L[ℝ] C)
    (α : E [⋀^Fin 2]→L[ℝ] A) (β : E [⋀^Fin 2]→L[ℝ] B) :
    E [⋀^Fin 4]→L[ℝ] C :=
  (4⁻¹ : ℝ) • alternationCLM
    ((concatenate P α.toContinuousMultilinearMap β.toContinuousMultilinearMap).domDomCongr
      (finSumFinEquiv (m := 2) (n := 2)))

theorem wedge22_add_left (P : A →L[ℝ] B →L[ℝ] C)
    (α₁ α₂ : E [⋀^Fin 2]→L[ℝ] A) (β : E [⋀^Fin 2]→L[ℝ] B) :
    wedge22 P (α₁ + α₂) β = wedge22 P α₁ β + wedge22 P α₂ β := by
  ext v
  simp [wedge22, alternationCLM_apply, concatenate_apply, Finset.sum_add_distrib,
    smul_add]

theorem wedge22_smul_left (P : A →L[ℝ] B →L[ℝ] C)
    (r : ℝ) (α : E [⋀^Fin 2]→L[ℝ] A) (β : E [⋀^Fin 2]→L[ℝ] B) :
    wedge22 P (r • α) β = r • wedge22 P α β := by
  ext v
  simp [wedge22, alternationCLM_apply, concatenate_apply, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro σ _
  rw [smul_comm (Equiv.Perm.sign σ) r]
  simp only [smul_smul]
  rw [mul_comm (4⁻¹ : ℝ) r]

theorem wedge22_add_right (P : A →L[ℝ] B →L[ℝ] C)
    (α : E [⋀^Fin 2]→L[ℝ] A) (β₁ β₂ : E [⋀^Fin 2]→L[ℝ] B) :
    wedge22 P α (β₁ + β₂) = wedge22 P α β₁ + wedge22 P α β₂ := by
  ext v
  simp [wedge22, alternationCLM_apply, concatenate_apply, Finset.sum_add_distrib,
    smul_add]

theorem wedge22_smul_right (P : A →L[ℝ] B →L[ℝ] C)
    (r : ℝ) (α : E [⋀^Fin 2]→L[ℝ] A) (β : E [⋀^Fin 2]→L[ℝ] B) :
    wedge22 P α (r • β) = r • wedge22 P α β := by
  ext v
  simp [wedge22, alternationCLM_apply, concatenate_apply, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro σ _
  rw [smul_comm (Equiv.Perm.sign σ) r]
  simp only [smul_smul]
  rw [mul_comm (4⁻¹ : ℝ) r]

def wedge22Linear (P : A →L[ℝ] B →L[ℝ] C) :
    (E [⋀^Fin 2]→L[ℝ] A) →ₗ[ℝ]
      (E [⋀^Fin 2]→L[ℝ] B) →ₗ[ℝ] (E [⋀^Fin 4]→L[ℝ] C) :=
  LinearMap.mk₂ ℝ (wedge22 P)
    (wedge22_add_left P) (wedge22_smul_left P)
    (wedge22_add_right P) (wedge22_smul_right P)

theorem norm_wedge22_le (P : A →L[ℝ] B →L[ℝ] C)
    (α : E [⋀^Fin 2]→L[ℝ] A) (β : E [⋀^Fin 2]→L[ℝ] B) :
    ‖wedge22 P α β‖ ≤ 6 * ‖P‖ * ‖α‖ * ‖β‖ := by
  let f := concatenate P α.toContinuousMultilinearMap β.toContinuousMultilinearMap
  let g := f.domDomCongr (finSumFinEquiv (m := 2) (n := 2))
  have h₁ : ‖alternationCLM g‖ ≤ 24 * ‖g‖ := by
    simpa using norm_alternation_le g
  have h₂ : ‖f‖ ≤ ‖P‖ * ‖α‖ * ‖β‖ := by
    simpa only [ContinuousAlternatingMap.norm_toContinuousMultilinearMap] using
      norm_concatenate_le P α.toContinuousMultilinearMap β.toContinuousMultilinearMap
  calc
    ‖wedge22 P α β‖ = (4⁻¹ : ℝ) * ‖alternationCLM g‖ := by
      simp [wedge22, g, f, norm_smul]
    _ ≤ (4⁻¹ : ℝ) * (24 * ‖g‖) := by gcongr
    _ = 6 * ‖f‖ := by
      rw [ContinuousMultilinearMap.norm_domDomCongr]
      ring
    _ ≤ 6 * (‖P‖ * ‖α‖ * ‖β‖) := by gcongr
    _ = 6 * ‖P‖ * ‖α‖ * ‖β‖ := by ring

def wedge22CLM (P : A →L[ℝ] B →L[ℝ] C) :
    (E [⋀^Fin 2]→L[ℝ] A) →L[ℝ]
      (E [⋀^Fin 2]→L[ℝ] B) →L[ℝ] (E [⋀^Fin 4]→L[ℝ] C) :=
  (wedge22Linear P).mkContinuous₂ (6 * ‖P‖) (fun α β => norm_wedge22_le P α β)

theorem wedge22CLM_apply (P : A →L[ℝ] B →L[ℝ] C)
    (α : E [⋀^Fin 2]→L[ℝ] A) (β : E [⋀^Fin 2]→L[ℝ] B) :
    wedge22CLM P α β = wedge22 P α β := rfl

theorem differentiableAt_wedge22 (P : A →L[ℝ] B →L[ℝ] C)
    (α : E → E [⋀^Fin 2]→L[ℝ] A) (β : E → E [⋀^Fin 2]→L[ℝ] B)
    (x : E) (hα : DifferentiableAt ℝ α x) (hβ : DifferentiableAt ℝ β x) :
    DifferentiableAt ℝ (fun y => wedge22 P (α y) (β y)) x := by
  have hconst : DifferentiableAt ℝ (fun _ : E =>
      wedge22CLM (E := E) (A := A) (B := B) (C := C) P) x :=
    differentiableAt_const _
  have hf : DifferentiableAt ℝ (fun y =>
      wedge22CLM (E := E) (A := A) (B := B) (C := C) P (α y)) x :=
    DifferentiableAt.clm_apply
      (G := E [⋀^Fin 2]→L[ℝ] A)
      (H := (E [⋀^Fin 2]→L[ℝ] B) →L[ℝ] E [⋀^Fin 4]→L[ℝ] C)
      hconst hα
  simpa only [wedge22CLM_apply] using hf.clm_apply hβ

variable {R : Type*} [NormedRing R] [NormedAlgebra ℝ R]

local instance : NormedSpace ℝ R := NormedAlgebra.toNormedSpace R

/-- The bilinear pairing `(a,b) ↦ T(ab)` used for trace powers. -/
def traceProduct (T : R →L[ℝ] B) : R →L[ℝ] R →L[ℝ] B :=
  ((ContinuousLinearMap.compL ℝ R R B) T).comp (ContinuousLinearMap.mul ℝ R)

theorem traceProduct_apply (T : R →L[ℝ] B) (a b : R) :
    traceProduct T a b = T (a * b) := rfl

/-- The degree-four local characteristic form `T(F ∧ F)`. -/
def traceSquareForm (T : R →L[ℝ] B) (Γ : Form (E := E) (A := R)) :
    E → E [⋀^Fin 4]→L[ℝ] B := fun x =>
  wedge22 (traceProduct T) (curvatureForm Γ x) (curvatureForm Γ x)

theorem differentiableAt_traceSquareForm (T : R →L[ℝ] B)
    (Γ : Form (E := E) (A := R)) (x : E) (hΓ : ContDiffAt ℝ 2 Γ x) :
    DifferentiableAt ℝ (traceSquareForm T Γ) x := by
  have h₁ : DifferentiableAt ℝ Γ x := hΓ.differentiableAt (by norm_num)
  have h₂ : DifferentiableAt ℝ (fderiv ℝ Γ) x :=
    (hΓ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  exact differentiableAt_wedge22 (traceProduct T) (curvatureForm Γ)
    (curvatureForm Γ) x (differentiableAt_curvatureForm Γ x h₁ h₂)
    (differentiableAt_curvatureForm Γ x h₁ h₂)

theorem traceSquareForm_apply (T : R →L[ℝ] B)
    (hT : ∀ a b : R, T (a * b) = T (b * a))
    (Γ : Form (E := E) (A := R)) (x a b c d : E) :
    traceSquareForm T Γ x ![a, b, c, d] =
      (2 : ℝ) • traceSquare4 T (fun v w => curvature Γ x v w) a b c d := by
  have h := rawTraceSquare_alternation_apply T (traceProduct T)
    (traceProduct_apply T) hT (curvatureForm Γ x) a b c d
  change alternationCLM
    ((concatenate (traceProduct T)
      (curvatureForm Γ x).toContinuousMultilinearMap
      (curvatureForm Γ x).toContinuousMultilinearMap).domDomCongr
        (finSumFinEquiv (m := 2) (n := 2))) ![a, b, c, d] = _ at h
  change (4⁻¹ : ℝ) • alternationCLM
    ((concatenate (traceProduct T)
      (curvatureForm Γ x).toContinuousMultilinearMap
      (curvatureForm Γ x).toContinuousMultilinearMap).domDomCongr
        (finSumFinEquiv (m := 2) (n := 2))) ![a, b, c, d] = _
  rw [h]
  simp only [smul_smul]
  norm_num [curvatureForm_apply]

theorem differentiableAt_curvature_coefficient (Γ : Form (E := E) (A := R))
    (x : E) (hΓ : ContDiffAt ℝ 2 Γ x) (v w : E) :
    DifferentiableAt ℝ (fun y => curvature Γ y v w) x := by
  have h₁ : DifferentiableAt ℝ Γ x := hΓ.differentiableAt (by norm_num)
  have h₂ : DifferentiableAt ℝ (fderiv ℝ Γ) x :=
    (hΓ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hf := (differentiableAt_curvatureForm Γ x h₁ h₂).continuousAlternatingMap_apply_const
    ![v, w]
  simpa only [curvatureForm_apply, Matrix.cons_val_zero, Matrix.cons_val_one] using hf

theorem covariantCurvatureDerivative_skew (Γ : Form (E := E) (A := R))
    (x u v w : E) :
    LocalConnectionBianchi.covariantCurvatureDerivative Γ x u w v =
      -LocalConnectionBianchi.covariantCurvatureDerivative Γ x u v w := by
  have hswap : (fun y => curvature Γ y w v) =
      (fun y => -curvature Γ y v w) := by
    funext y
    exact curvature_antisymm Γ y w v
  have hderiv : fderiv ℝ (fun y => -curvature Γ y v w) x =
      -fderiv ℝ (fun y => curvature Γ y v w) x := by
    simpa only [Pi.neg_apply] using
      (fderiv_neg (𝕜 := ℝ) (f := fun y => curvature Γ y v w) (x := x))
  simp only [LocalConnectionBianchi.covariantCurvatureDerivative]
  rw [hswap, hderiv, curvature_antisymm Γ x w v]
  simp only [ContinuousLinearMap.neg_apply, neg_mul, mul_neg]
  abel

/-- Bianchi and cyclicity close the coordinate trace-square expression. The
five derivatives here are actual Fréchet derivatives, not formal symbols. -/
theorem traceSquare4_coordinate_closed (T : R →L[ℝ] B)
    (hT : ∀ a b : R, T (a * b) = T (b * a))
    (Γ : Form (E := E) (A := R)) (x : E) (hΓ : ContDiffAt ℝ 2 Γ x)
    (a b c d e : E) :
    fderiv ℝ (fun y => traceSquare4 T (fun v w => curvature Γ y v w) b c d e) x a -
    fderiv ℝ (fun y => traceSquare4 T (fun v w => curvature Γ y v w) a c d e) x b +
    fderiv ℝ (fun y => traceSquare4 T (fun v w => curvature Γ y v w) a b d e) x c -
    fderiv ℝ (fun y => traceSquare4 T (fun v w => curvature Γ y v w) a b c e) x d +
    fderiv ℝ (fun y => traceSquare4 T (fun v w => curvature Γ y v w) a b c d) x e = 0 := by
  let F : E → E → R := fun v w => curvature Γ x v w
  let D : E → E → E → R := fun u v w =>
    LocalConnectionBianchi.covariantCurvatureDerivative Γ x u v w
  have hd : ∀ u v w, D u w v = -D u v w := by
    intro u v w
    exact covariantCurvatureDerivative_skew Γ x u v w
  have hb : ∀ u v w, cyclicDerivative D u v w = 0 := by
    intro u v w
    exact LocalConnectionBianchi.bianchi Γ x hΓ u v w
  have hzero := traceSquare4Variation_five_eq_zero T hT F D hd hb a b c d e
  have hcv (u p q r s : E) :
      traceSquare4Variation T F (D u) p q r s =
        traceSquare4Variation T F
          (fun v w => fderiv ℝ (fun y => curvature Γ y v w) x u) p q r s := by
    have hD_eq : D u = fun v w => fderiv ℝ (fun y => curvature Γ y v w) x u +
        (Γ x u * F v w - F v w * Γ x u) := by
      funext v w
      dsimp [D, F, LocalConnectionBianchi.covariantCurvatureDerivative]
      abel
    rw [hD_eq]
    exact traceSquare4Variation_covariant_eq_ordinary T hT F
      (fun v w => fderiv ℝ (fun y => curvature Γ y v w) x u)
      (Γ x u) p q r s
  rw [hcv a b c d e, hcv b a c d e, hcv c a b d e,
    hcv d a b c e, hcv e a b c d] at hzero
  have hφ : ∀ v w, DifferentiableAt ℝ (fun y => curvature Γ y v w) x :=
    differentiableAt_curvature_coefficient Γ x hΓ
  simpa only [fderiv_traceSquare4 T (fun y v w => curvature Γ y v w)
    x a b c d e hφ,
    fderiv_traceSquare4 T (fun y v w => curvature Γ y v w)
    x b a c d e hφ,
    fderiv_traceSquare4 T (fun y v w => curvature Γ y v w)
    x c a b d e hφ,
    fderiv_traceSquare4 T (fun y v w => curvature Γ y v w)
    x d a b c e hφ,
    fderiv_traceSquare4 T (fun y v w => curvature Γ y v w)
    x e a b c d hφ] using hzero

theorem extDeriv_four_apply (ω : E → E [⋀^Fin 4]→L[ℝ] B) (x : E)
    (hω : DifferentiableAt ℝ ω x) (a b c d e : E) :
    extDeriv ω x ![a, b, c, d, e] =
      fderiv ℝ (fun y => ω y ![b, c, d, e]) x a -
      fderiv ℝ (fun y => ω y ![a, c, d, e]) x b +
      fderiv ℝ (fun y => ω y ![a, b, d, e]) x c -
      fderiv ℝ (fun y => ω y ![a, b, c, e]) x d +
      fderiv ℝ (fun y => ω y ![a, b, c, d]) x e := by
  have h₁ : Fin.removeNth (1 : Fin 5) ![a, b, c, d, e] = ![a, c, d, e] := by
    ext i; fin_cases i <;> rfl
  have h₂ : Fin.removeNth (2 : Fin 5) ![a, b, c, d, e] = ![a, b, d, e] := by
    ext i; fin_cases i <;> rfl
  have h₃ : Fin.removeNth (3 : Fin 5) ![a, b, c, d, e] = ![a, b, c, e] := by
    ext i; fin_cases i <;> rfl
  have h₄ : Fin.removeNth (4 : Fin 5) ![a, b, c, d, e] = ![a, b, c, d] := by
    ext i; fin_cases i <;> rfl
  rw [extDeriv_apply hω]
  simp [Fin.sum_univ_succ, h₁, h₂, h₃, h₄, sub_eq_add_neg]
  abel

private theorem traceSquareForm_closed_of_coordinate_formula (T : R →L[ℝ] B)
    (hT : ∀ a b : R, T (a * b) = T (b * a))
    (Γ : Form (E := E) (A := R)) (x : E) (hΓ : ContDiffAt ℝ 2 Γ x)
    (happly : ∀ (y a b c d : E), traceSquareForm T Γ y ![a, b, c, d] =
      (2 : ℝ) • traceSquare4 T (fun v w => curvature Γ y v w) a b c d) :
    extDeriv (traceSquareForm T Γ) x = 0 := by
  have hcoords (a b c d : E) :
      (fun y => traceSquareForm T Γ y ![a, b, c, d]) =
      (fun y => (2 : ℝ) •
        traceSquare4 T (fun v w => curvature Γ y v w) a b c d) := by
    funext y
    exact happly y a b c d
  have hderiv (a b c d u : E) :
      fderiv ℝ (fun y => traceSquareForm T Γ y ![a, b, c, d]) x u =
      (2 : ℝ) • fderiv ℝ
        (fun y => traceSquare4 T (fun v w => curvature Γ y v w) a b c d) x u := by
    rw [hcoords]
    change fderiv ℝ ((2 : ℝ) •
      (fun y => traceSquare4 T (fun v w => curvature Γ y v w) a b c d)) x u = _
    rw [fderiv_const_smul_field]
    rfl
  ext v
  have hv : v = ![v 0, v 1, v 2, v 3, v 4] := by
    ext i
    fin_cases i <;> rfl
  rw [hv, extDeriv_four_apply (traceSquareForm T Γ) x
    (differentiableAt_traceSquareForm T Γ x hΓ),
    hderiv, hderiv, hderiv, hderiv, hderiv]
  simpa only [smul_sub, smul_add, smul_zero] using
    congrArg (fun z : B => (2 : ℝ) • z)
      (traceSquare4_coordinate_closed T hT Γ x hΓ (v 0) (v 1) (v 2) (v 3) (v 4))

/-- The normalized degree-four Chern–Weil form `T(F ∧ F)` is closed at a
twice continuously differentiable local connection when `T` is cyclic. -/
theorem traceSquareForm_closed (T : R →L[ℝ] B)
    (hT : ∀ a b : R, T (a * b) = T (b * a))
    (Γ : Form (E := E) (A := R)) (x : E) (hΓ : ContDiffAt ℝ 2 Γ x) :
    extDeriv (traceSquareForm T Γ) x = 0 :=
  traceSquareForm_closed_of_coordinate_formula T hT Γ x hΓ
    (traceSquareForm_apply T hT Γ)

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V]

local instance : NormedAddCommGroup (V →L[ℝ] V) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (V →L[ℝ] V) :=
  ContinuousLinearMap.toNormedSpace

/-- The actual endomorphism trace of the square of local curvature. -/
def traceCurvatureSquare (Γ : Form (E := E) (A := V →L[ℝ] V)) :
    E → E [⋀^Fin 4]→L[ℝ] ℝ := traceSquareForm traceCLM Γ

theorem traceCurvatureSquare_closed (Γ : Form (E := E) (A := V →L[ℝ] V))
    (x : E) (hΓ : ContDiffAt ℝ 2 Γ x) :
    extDeriv (traceCurvatureSquare Γ) x = 0 :=
  traceSquareForm_closed traceCLM traceCLM_cyclic Γ x hΓ

end
end QuaternionicSymmetry.LocalChernWeilQuadratic
