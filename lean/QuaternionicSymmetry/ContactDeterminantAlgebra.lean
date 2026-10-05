import Mathlib.LinearAlgebra.BilinearForm.Basic
import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Tactic

/-! The nondegenerate bordered alternating form associated with contact data.
Its determinant supplies the square of the contact canonical relation. -/
namespace QuaternionicSymmetry.ContactDeterminantAlgebra
open LinearMap
noncomputable section

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

def border (a : V →ₗ[K] K) (b : LinearMap.BilinForm K V) : LinearMap.BilinForm K (V × K) :=
  LinearMap.mk₂ K (fun u v => b u.1 v.1 + u.2 * a v.1 - v.2 * a u.1)
    (by intros; simp only [Prod.fst_add, Prod.snd_add, map_add, LinearMap.add_apply]; ring)
    (by intros; simp only [Prod.smul_fst, Prod.smul_snd, map_smul, smul_eq_mul,
      LinearMap.smul_apply]; ring)
    (by intros; simp only [Prod.fst_add, Prod.snd_add, map_add, LinearMap.add_apply]; ring)
    (by intros; simp only [Prod.smul_fst, Prod.smul_snd, map_smul, smul_eq_mul]; ring)

@[simp] theorem border_apply (a : V →ₗ[K] K) (b : LinearMap.BilinForm K V) (u v : V × K) :
    border a b u v = b u.1 v.1 + u.2 * a v.1 - v.2 * a u.1 := rfl

theorem border_alt (a : V →ₗ[K] K) (b : LinearMap.BilinForm K V) (hb : b.IsAlt) :
    (border a b).IsAlt := by
  intro u
  simp [hb.self_eq_zero]

/-- Nondegeneracy on the contact hyperplane makes the bordered form
nondegenerate on the tangent space plus one auxiliary scalar direction. -/
theorem border_nondegenerate (a : V →ₗ[K] K) (b : LinearMap.BilinForm K V)
    (ha : Function.Surjective a) (hb : b.IsAlt)
    (hker : ∀ u, a u = 0 → (∀ v, a v = 0 → b u v = 0) → u = 0) :
    (border a b).Nondegenerate := by
  have hleft : ∀ u, (∀ v, border a b u v = 0) → u = 0 := by
    rintro ⟨u,s⟩ hu
    have hau : a u = 0 := by simpa using hu (0,1)
    have hu0 : u = 0 := hker u hau (by
      intro v hv
      simpa [hau, hv] using hu (v,0))
    obtain ⟨v,hv⟩ := ha 1
    have hs : s = 0 := by simpa [hu0, hv] using hu (v,0)
    simp [hu0, hs]
  refine ⟨hleft, ?_⟩
  intro v hv
  apply hleft v
  intro u
  have h := (border_alt a b hb).neg_eq u v
  simpa [hv u] using h.symm

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem border_det_ne_zero (e : Module.Basis ι K (V × K))
    (a : V →ₗ[K] K) (b : LinearMap.BilinForm K V)
    (ha : Function.Surjective a) (hb : b.IsAlt)
    (hker : ∀ u, a u = 0 → (∀ v, a v = 0 → b u v = 0) → u = 0) :
    (LinearMap.BilinForm.toMatrix e (border a b)).det ≠ 0 :=
  (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero e).mp
    (border_nondegenerate a b ha hb hker)

/-- Determinants of bilinear forms transform by the square of the ordinary
determinant. -/
theorem det_comp (e : Module.Basis ι K V) (b : LinearMap.BilinForm K V) (f : V →ₗ[K] V) :
    (LinearMap.BilinForm.toMatrix e (b.comp f f)).det =
      f.det ^ 2 * (LinearMap.BilinForm.toMatrix e b).det := by
  rw [LinearMap.BilinForm.toMatrix_comp e e, Matrix.det_mul, Matrix.det_mul,
    Matrix.det_transpose, LinearMap.det_toMatrix]
  ring

/-- The triangular change of the auxiliary direction has determinant one. -/
def shear (η : V →ₗ[K] K) : V × K →ₗ[K] V × K :=
  (LinearMap.fst K V K).prod
    ((LinearMap.snd K V K) + η.comp (LinearMap.fst K V K))

@[simp] theorem shear_apply (η : V →ₗ[K] K) (u : V × K) :
    shear η u = (u.1, u.2 + η u.1) := rfl

theorem shear_det (e : Module.Basis ι K V) (η : V →ₗ[K] K) :
    (shear η).det = 1 := by
  classical
  let eK := Module.Basis.singleton Unit K
  have hm : LinearMap.toMatrix (e.prod eK) (e.prod eK) (shear η) =
      Matrix.fromBlocks (1 : Matrix ι ι K) 0 (fun _ j => η (e j))
        (1 : Matrix Unit Unit K) := by
    ext (i | i) (j | j) <;> simp [LinearMap.toMatrix, eK, shear, Matrix.one_apply, Finsupp.single_apply, eq_comm]
  rw [← LinearMap.det_toMatrix (e.prod eK), hm, Matrix.det_fromBlocks_zero₁₂]
  simp

/-- Adding a multiple of the contact form to a local primitive changes
its exterior derivative by this decomposable alternating form. -/
def wedge (η a : V →ₗ[K] K) : LinearMap.BilinForm K V :=
  LinearMap.mk₂ K (fun u v => η u * a v - η v * a u)
    (by intros; simp only [map_add]; ring)
    (by intros; simp only [map_smul, smul_eq_mul]; ring)
    (by intros; simp only [map_add]; ring)
    (by intros; simp only [map_smul, smul_eq_mul]; ring)

@[simp] theorem wedge_apply (η a : V →ₗ[K] K) (u v : V) :
    wedge η a u v = η u * a v - η v * a u := rfl

theorem border_wedge (a η : V →ₗ[K] K) (b : LinearMap.BilinForm K V) :
    border a (b + wedge η a) = (border a b).comp (shear η) (shear η) := by
  apply LinearMap.ext
  intro u
  apply LinearMap.ext
  intro v
  simp only [border_apply, LinearMap.BilinForm.comp_apply, shear_apply,
    LinearMap.add_apply, wedge_apply]
  ring

theorem border_det_wedge (e : Module.Basis ι K V)
    (a η : V →ₗ[K] K) (b : LinearMap.BilinForm K V) :
    (LinearMap.BilinForm.toMatrix (e.prod (Module.Basis.singleton Unit K))
      (border a (b + wedge η a))).det =
    (LinearMap.BilinForm.toMatrix (e.prod (Module.Basis.singleton Unit K))
      (border a b)).det := by
  rw [border_wedge, det_comp, shear_det e]
  simp

@[simp] theorem border_smul (a : V →ₗ[K] K) (b : LinearMap.BilinForm K V) (c : K) :
    border (c • a) (c • b) = c • border a b := by
  apply LinearMap.ext
  intro u
  apply LinearMap.ext
  intro v
  simp only [border_apply, LinearMap.smul_apply, smul_eq_mul]
  ring

theorem border_comp (a : V →ₗ[K] K) (b : LinearMap.BilinForm K V)
    (f : V →ₗ[K] V) :
    (border a b).comp (f.prodMap (LinearMap.id : K →ₗ[K] K))
      (f.prodMap (LinearMap.id : K →ₗ[K] K)) = border (a.comp f) (b.comp f f) := by
  apply LinearMap.ext
  intro u
  apply LinearMap.ext
  intro v
  rfl

theorem border_det_scale_wedge (e : Module.Basis ι K V)
    (a η : V →ₗ[K] K) (b : LinearMap.BilinForm K V) (c : K) (hc : c ≠ 0) :
    (LinearMap.BilinForm.toMatrix (e.prod (Module.Basis.singleton Unit K))
      (border (c • a) (c • b + wedge η a))).det =
      c ^ (Fintype.card ι + 1) *
        (LinearMap.BilinForm.toMatrix (e.prod (Module.Basis.singleton Unit K))
          (border a b)).det := by
  have hw : c • b + wedge η a = c • (b + wedge (c⁻¹ • η) a) := by
    apply LinearMap.ext
    intro u
    apply LinearMap.ext
    intro v
    simp only [LinearMap.add_apply, LinearMap.smul_apply, wedge_apply, smul_eq_mul]
    field_simp
    <;> ring
  rw [hw, border_smul, map_smul, Matrix.det_smul, border_det_wedge]
  simp

theorem border_det_covariance [FiniteDimensional K V]
    (e : Module.Basis ι K V) (a a' η : V →ₗ[K] K)
    (b b' : LinearMap.BilinForm K V) (f : V →ₗ[K] V)
    (c : K) (hc : c ≠ 0)
    (ha : a'.comp f = c • a)
    (hb : b'.comp f f = c • b + wedge η a) :
    f.det ^ 2 *
      (LinearMap.BilinForm.toMatrix (e.prod (Module.Basis.singleton Unit K))
        (border a' b')).det =
    c ^ (Fintype.card ι + 1) *
      (LinearMap.BilinForm.toMatrix (e.prod (Module.Basis.singleton Unit K))
        (border a b)).det := by
  have h := det_comp (e.prod (Module.Basis.singleton Unit K)) (border a' b')
    (f.prodMap (LinearMap.id : K →ₗ[K] K))
  rw [border_comp, ha, hb, LinearMap.det_prodMap, LinearMap.det_id, mul_one] at h
  exact h.symm.trans (border_det_scale_wedge e a η b c hc)

end
end QuaternionicSymmetry.ContactDeterminantAlgebra
