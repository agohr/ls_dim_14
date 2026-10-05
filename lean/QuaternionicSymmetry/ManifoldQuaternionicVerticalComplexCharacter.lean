import QuaternionicSymmetry.ManifoldQuaternionicTwistorIsotropyWeight
import QuaternionicSymmetry.ManifoldTwistorVerticalComplexLine
import Mathlib.LinearAlgebra.Matrix.DotProduct

/-! Complex-line form of the genuine vertical coefficient representation at
an actual fixed twistor point. The complex structure is the intrinsic
cross-product rotation in the vertical two-plane. -/
namespace QuaternionicSymmetry.ManifoldQuaternionicVerticalComplexCharacter
open ManifoldQuaternionicSpanSymmetry
open ManifoldQuaternionicTwistorIsotropyWeight
open ManifoldTwistorSphereCore ManifoldTwistorSphereBundle
open ManifoldTwistorVerticalComplex
open ManifoldTwistorCoefficientSphere
open ManifoldTwistorGlobalAlmostComplex
open ManifoldQuaternionicIsometryOrientation
open scoped Manifold ContDiff Matrix
noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
  (I := 𝓘(ℝ,E)) (M := M) (n := ∞))

def coefficientVerticalComplexSmul (a : coefficientSphere) (c : ℂ)
    (v : verticalSubmodule a) : verticalSubmodule a :=
  c.re • v + c.im • verticalComplex a v

theorem coefficientVerticalComplexSmul_real (a : coefficientSphere)
    (r : ℝ) (v : verticalSubmodule a) :
    coefficientVerticalComplexSmul a (r : ℂ) v = r • v := by
  simp [coefficientVerticalComplexSmul]

theorem coefficientVerticalComplexSmul_i (a : coefficientSphere)
    (v : verticalSubmodule a) :
    coefficientVerticalComplexSmul a Complex.I v = verticalComplex a v := by
  simp [coefficientVerticalComplexSmul]

/-- The actual vertical coefficient plane as a complex line. -/
def coefficientVerticalComplexModule (a : coefficientSphere) :
    Module ℂ (verticalSubmodule a) where
  smul := coefficientVerticalComplexSmul a
  one_smul := by
    intro v
    change coefficientVerticalComplexSmul a 1 v = v
    simp [coefficientVerticalComplexSmul]
  mul_smul := by
    intro b c v
    change coefficientVerticalComplexSmul a (b * c) v =
      coefficientVerticalComplexSmul a b
        (coefficientVerticalComplexSmul a c v)
    simp only [coefficientVerticalComplexSmul, Complex.mul_re, Complex.mul_im,
      add_smul, smul_add, mul_smul, map_add, map_smul,
      verticalComplex_sq]
    module
  smul_zero := by
    intro c
    change coefficientVerticalComplexSmul a c 0 = 0
    simp [coefficientVerticalComplexSmul]
  smul_add := by
    intro c u v
    change coefficientVerticalComplexSmul a c (u + v) =
      coefficientVerticalComplexSmul a c u +
        coefficientVerticalComplexSmul a c v
    simp only [coefficientVerticalComplexSmul, smul_add, map_add]
    abel
  add_smul := by
    intro b c v
    change coefficientVerticalComplexSmul a (b + c) v =
      coefficientVerticalComplexSmul a b v +
        coefficientVerticalComplexSmul a c v
    simp only [coefficientVerticalComplexSmul, Complex.add_re, Complex.add_im,
      add_smul]
    abel
  zero_smul := by
    intro v
    change coefficientVerticalComplexSmul a 0 v = 0
    simp [coefficientVerticalComplexSmul]

theorem coefficientVerticalComplex_finrank (z : SphereBundleTotal Q) :
    letI := coefficientVerticalComplexModule
      (coefficientSphereHomeomorph.symm z.2)
    Module.finrank ℂ
      (verticalSubmodule (coefficientSphereHomeomorph.symm z.2)) = 1 := by
  let a := coefficientSphereHomeomorph.symm z.2
  let realModule : Module ℝ (verticalSubmodule a) := inferInstance
  letI : Module ℝ (verticalSubmodule a) := realModule
  letI := coefficientVerticalComplexModule a
  letI : IsScalarTower ℝ ℂ (verticalSubmodule a) := ⟨by
    intro r c v
    change coefficientVerticalComplexSmul a (r • c) v =
      r • coefficientVerticalComplexSmul a c v
    rw [show r • c = (r : ℂ) * c by simp,
      show coefficientVerticalComplexSmul a ((r : ℂ) * c) v =
        coefficientVerticalComplexSmul a (r : ℂ)
          (coefficientVerticalComplexSmul a c v) from
        (coefficientVerticalComplexModule a).mul_smul (r : ℂ) c v,
      coefficientVerticalComplexSmul_real]⟩
  have hmodule : Module.complexToReal (verticalSubmodule a) = realModule := by
    apply Module.ext'
    intro r v
    exact coefficientVerticalComplexSmul_real a r v
  have h := finrank_real_of_complex (verticalSubmodule a)
  rw [hmodule] at h
  have hreal : Module.finrank ℝ (verticalSubmodule a) = 2 := by
    have he := (verticalTangentEquiv Q z).finrank_eq
    exact he.symm.trans (verticalTangent_finrank Q z)
  have hh : 2 = 2 * Module.finrank ℂ (verticalSubmodule a) :=
    hreal.symm.trans h
  change Module.finrank ℂ (verticalSubmodule a) = 1
  omega

/-- The actual SO(3) derivative of a twistor-point stabilizer is
complex-linear on its two-dimensional vertical coefficient plane. -/
def isotropyVerticalComplexRepresentation (z : SphereBundleTotal Q) :
    letI := coefficientVerticalComplexModule
      (coefficientSphereHomeomorph.symm z.2)
    MulAction.stabilizer (QuaternionicIsometries Q) z →*
      Module.End ℂ (verticalSubmodule (coefficientSphereHomeomorph.symm z.2)) := by
  let a := coefficientSphereHomeomorph.symm z.2
  letI := coefficientVerticalComplexModule a
  let ρ := isotropyVerticalRepresentation Q z
  exact {
    toFun := fun f => {
      toFun := ρ f
      map_add' := (ρ f).map_add
      map_smul' := by
        intro c v
        change ρ f (coefficientVerticalComplexSmul a c v) =
          coefficientVerticalComplexSmul a c (ρ f v)
        simp only [coefficientVerticalComplexSmul, map_add, map_smul]
        rw [isotropyVerticalRepresentation_complex Q z f v] }
    map_one' := by
      apply LinearMap.ext
      intro v
      change ρ 1 v = v
      rw [map_one]
      rfl
    map_mul' := by
      intro f g
      apply LinearMap.ext
      intro v
      change ρ (f*g) v = ρ f (ρ g v)
      rw [map_mul]
      rfl }

/-- The unique complex scalar by which a twistor-point stabilizer acts on
its actual vertical complex line. Its extraction uses the proven complex
finrank-one statement rather than a selected real basis. -/
def verticalScalar (z : SphereBundleTotal Q)
    (f : MulAction.stabilizer (QuaternionicIsometries Q) z) : ℂ := by
  letI := coefficientVerticalComplexModule
    (coefficientSphereHomeomorph.symm z.2)
  let e := LinearEquiv.smul_id_of_finrank_eq_one
    (coefficientVerticalComplex_finrank Q z)
  exact e.symm (isotropyVerticalComplexRepresentation Q z f)

theorem isotropyVerticalComplexRepresentation_eq_scalar
    (z : SphereBundleTotal Q)
    (f : MulAction.stabilizer (QuaternionicIsometries Q) z) :
    letI := coefficientVerticalComplexModule
      (coefficientSphereHomeomorph.symm z.2)
    isotropyVerticalComplexRepresentation Q z f =
      verticalScalar Q z f •
        (LinearMap.id : Module.End ℂ
          (verticalSubmodule (coefficientSphereHomeomorph.symm z.2))) := by
  letI := coefficientVerticalComplexModule
    (coefficientSphereHomeomorph.symm z.2)
  let e := LinearEquiv.smul_id_of_finrank_eq_one
    (coefficientVerticalComplex_finrank Q z)
  have he := e.apply_symm_apply (isotropyVerticalComplexRepresentation Q z f)
  exact he.symm

theorem verticalScalar_one (z : SphereBundleTotal Q) :
    verticalScalar Q z (1 : MulAction.stabilizer (QuaternionicIsometries Q) z) = 1 := by
  letI := coefficientVerticalComplexModule
    (coefficientSphereHomeomorph.symm z.2)
  let e := LinearEquiv.smul_id_of_finrank_eq_one
    (coefficientVerticalComplex_finrank Q z)
  apply e.injective
  calc
    e (verticalScalar Q z 1) = isotropyVerticalComplexRepresentation Q z 1 :=
      (isotropyVerticalComplexRepresentation_eq_scalar Q z 1).symm
    _ = 1 := map_one _
    _ = e 1 := by
      ext v
      simp [e, LinearEquiv.smul_id_of_finrank_eq_one]

theorem verticalScalar_mul (z : SphereBundleTotal Q)
    (f g : MulAction.stabilizer (QuaternionicIsometries Q) z) :
    verticalScalar Q z (f * g) = verticalScalar Q z f * verticalScalar Q z g := by
  letI := coefficientVerticalComplexModule
    (coefficientSphereHomeomorph.symm z.2)
  let e := LinearEquiv.smul_id_of_finrank_eq_one
    (coefficientVerticalComplex_finrank Q z)
  apply e.injective
  calc
    e (verticalScalar Q z (f*g)) =
        isotropyVerticalComplexRepresentation Q z (f*g) :=
      (isotropyVerticalComplexRepresentation_eq_scalar Q z (f*g)).symm
    _ = isotropyVerticalComplexRepresentation Q z f *
          isotropyVerticalComplexRepresentation Q z g :=
      (isotropyVerticalComplexRepresentation Q z).map_mul f g
    _ = e (verticalScalar Q z f * verticalScalar Q z g) := by
      rw [isotropyVerticalComplexRepresentation_eq_scalar,
        isotropyVerticalComplexRepresentation_eq_scalar]
      apply LinearMap.ext
      intro v
      change verticalScalar Q z f • (verticalScalar Q z g • v) =
        (verticalScalar Q z f * verticalScalar Q z g) • v
      exact (mul_smul _ _ _).symm

theorem isotropyVerticalRepresentation_eq_verticalScalar
    (z : SphereBundleTotal Q)
    (f : MulAction.stabilizer (QuaternionicIsometries Q) z)
    (v : verticalSubmodule (coefficientSphereHomeomorph.symm z.2)) :
    isotropyVerticalRepresentation Q z f v =
      coefficientVerticalComplexSmul
        (coefficientSphereHomeomorph.symm z.2) (verticalScalar Q z f) v := by
  letI := coefficientVerticalComplexModule
    (coefficientSphereHomeomorph.symm z.2)
  have h := congrArg (fun L : Module.End ℂ
      (verticalSubmodule (coefficientSphereHomeomorph.symm z.2)) => L v)
    (isotropyVerticalComplexRepresentation_eq_scalar Q z f)
  simpa only [LinearMap.smul_apply, LinearMap.id_apply] using h

theorem coefficientVerticalComplexSmul_dot_self (a : coefficientSphere)
    (c : ℂ) (v : verticalSubmodule a) :
    (coefficientVerticalComplexSmul a c v).1 ⬝ᵥ
      (coefficientVerticalComplexSmul a c v).1 =
      Complex.normSq c * (v.1 ⬝ᵥ v.1) := by
  have horth : v.1 ⬝ᵥ (a.1 ⨯₃ v.1) = 0 := dot_cross_self a.1 v.1
  have horth' : (a.1 ⨯₃ v.1) ⬝ᵥ v.1 = 0 := by
    rw [dotProduct_comm]
    exact horth
  have hcross := cross_dot_self a v.1 v.2
  change (c.re • v.1 + c.im • (a.1 ⨯₃ v.1)) ⬝ᵥ
    (c.re • v.1 + c.im • (a.1 ⨯₃ v.1)) = _
  simp only [add_dotProduct, dotProduct_add, dotProduct_smul, smul_dotProduct,
    smul_eq_mul, horth, horth', hcross, Complex.normSq_apply]
  ring

theorem verticalScalar_normSq_eq_one (z : SphereBundleTotal Q)
    (f : MulAction.stabilizer (QuaternionicIsometries Q) z) :
    Complex.normSq (verticalScalar Q z f) = 1 := by
  let a := coefficientSphereHomeomorph.symm z.2
  letI := coefficientVerticalComplexModule a
  letI : Nontrivial (verticalSubmodule a) :=
    Module.nontrivial_of_finrank_pos (by
      rw [coefficientVerticalComplex_finrank Q z]
      omega)
  obtain ⟨v, hv⟩ := exists_ne (0 : verticalSubmodule a)
  have hv' : v.1 ≠ 0 := by
    intro h
    exact hv (Subtype.ext h)
  have hdot : v.1 ⬝ᵥ v.1 ≠ 0 := by
    intro h
    exact hv' (dotProduct_self_eq_zero.mp h)
  have horth := coefficientAction_dot Q f.1 z.1 v.1 v.1
  have hval :
      (isotropyVerticalRepresentation Q z f v).1 =
        (coefficientVerticalComplexSmul a (verticalScalar Q z f) v).1 :=
    congrArg Subtype.val (isotropyVerticalRepresentation_eq_verticalScalar Q z f v)
  change (isotropyVerticalRepresentation Q z f v).1 ⬝ᵥ
    (isotropyVerticalRepresentation Q z f v).1 = v.1 ⬝ᵥ v.1 at horth
  have hnorm := coefficientVerticalComplexSmul_dot_self a (verticalScalar Q z f) v
  rw [← hval] at hnorm
  exact mul_right_cancel₀ hdot (hnorm.symm.trans (horth.trans (one_mul _).symm))

theorem verticalScalar_re_mul_dot (z : SphereBundleTotal Q)
    (f : MulAction.stabilizer (QuaternionicIsometries Q) z)
    (v : verticalSubmodule (coefficientSphereHomeomorph.symm z.2)) :
    (verticalScalar Q z f).re * (v.1 ⬝ᵥ v.1) =
      (isotropyVerticalRepresentation Q z f v).1 ⬝ᵥ v.1 := by
  let a := coefficientSphereHomeomorph.symm z.2
  have h := congrArg (fun w : verticalSubmodule a => w.1 ⬝ᵥ v.1)
    (isotropyVerticalRepresentation_eq_verticalScalar Q z f v)
  have horth : (a.1 ⨯₃ v.1) ⬝ᵥ v.1 = 0 := by
    rw [dotProduct_comm]
    exact dot_cross_self a.1 v.1
  change (isotropyVerticalRepresentation Q z f v).1 ⬝ᵥ v.1 =
    ((verticalScalar Q z f).re • v.1 +
      (verticalScalar Q z f).im • (a.1 ⨯₃ v.1)) ⬝ᵥ v.1 at h
  simp only [add_dotProduct, smul_dotProduct, smul_eq_mul, horth,
    mul_zero, add_zero] at h
  exact h.symm

theorem verticalScalar_im_mul_dot (z : SphereBundleTotal Q)
    (f : MulAction.stabilizer (QuaternionicIsometries Q) z)
    (v : verticalSubmodule (coefficientSphereHomeomorph.symm z.2)) :
    (verticalScalar Q z f).im * (v.1 ⬝ᵥ v.1) =
      (isotropyVerticalRepresentation Q z f v).1 ⬝ᵥ
        ((coefficientSphereHomeomorph.symm z.2).1 ⨯₃ v.1) := by
  let a := coefficientSphereHomeomorph.symm z.2
  have h := congrArg (fun w : verticalSubmodule a =>
    w.1 ⬝ᵥ (a.1 ⨯₃ v.1))
    (isotropyVerticalRepresentation_eq_verticalScalar Q z f v)
  have horth : v.1 ⬝ᵥ (a.1 ⨯₃ v.1) = 0 := dot_cross_self a.1 v.1
  have hcross := cross_dot_self a v.1 v.2
  change (isotropyVerticalRepresentation Q z f v).1 ⬝ᵥ
    (a.1 ⨯₃ v.1) =
    ((verticalScalar Q z f).re • v.1 +
      (verticalScalar Q z f).im • (a.1 ⨯₃ v.1)) ⬝ᵥ
        (a.1 ⨯₃ v.1) at h
  simp only [add_dotProduct, smul_dotProduct, smul_eq_mul, horth,
    hcross, mul_zero, zero_add] at h
  exact h.symm

end
end QuaternionicSymmetry.ManifoldQuaternionicVerticalComplexCharacter
