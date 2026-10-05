import QuaternionicSymmetry.ContactDeterminantAlgebra

/-! The local contact Hamiltonian is the unique solution of the bordered
Levi system. This construction is linear in the value and first derivative
of a section and is covariant under contact-form gauge changes. -/
namespace QuaternionicSymmetry.ContactHamiltonianAlgebra
open ContactDeterminantAlgebra
noncomputable section
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable (a : V →ₗ[K] K) (b : LinearMap.BilinForm K V)
  (h : (border a b).Nondegenerate)

def datum (s : K) (d : V →ₗ[K] K) : V × K →ₗ[K] K :=
  -(d.comp (LinearMap.fst K V K)) - s • LinearMap.snd K V K

@[simp] theorem datum_apply (s : K) (d : V →ₗ[K] K) (u : V × K) :
    datum s d u = -d u.1 - s * u.2 := rfl

def solution (s : K) (d : V →ₗ[K] K) : V × K := (border a b).toDual h |>.symm (datum s d)

theorem solution_equation (s : K) (d : V →ₗ[K] K) (v : V × K) :
    border a b (solution a b h s d) v = datum s d v :=
  LinearMap.BilinForm.apply_toDual_symm_apply _ _

theorem solution_value (s : K) (d : V →ₗ[K] K) : a (solution a b h s d).1 = s := by
  have he := solution_equation a b h s d (0,1)
  simpa using he

theorem solution_levi (s : K) (d : V →ₗ[K] K) (v : V) :
    b (solution a b h s d).1 v + (solution a b h s d).2 * a v = -d v := by
  simpa using solution_equation a b h s d (v,0)

theorem solution_unique (s : K) (d : V →ₗ[K] K) (u : V) (c : K)
    (hs : a u = s) (hd : ∀ v, b u v + c * a v = -d v) :
    (u,c) = solution a b h s d := by
  apply (border a b).toDual h |>.injective
  apply LinearMap.ext
  intro v
  change border a b (u,c) v = border a b (solution a b h s d) v
  rw [solution_equation]
  simp only [border_apply,datum_apply,hs,hd]
  ring

theorem solution_add (s t : K) (d e : V →ₗ[K] K) :
    solution a b h (s+t) (d+e) = solution a b h s d + solution a b h t e := by
  apply (border a b).toDual h |>.injective
  unfold solution
  rw [map_add,LinearEquiv.apply_symm_apply,LinearEquiv.apply_symm_apply,LinearEquiv.apply_symm_apply]
  change datum (s+t) (d+e) = datum s d + datum t e
  apply LinearMap.ext
  intro v
  simp only [datum_apply,LinearMap.add_apply,LinearMap.smul_apply,smul_eq_mul]
  ring

theorem solution_smul (r s : K) (d : V →ₗ[K] K) :
    solution a b h (r*s) (r • d) = r • solution a b h s d := by
  apply (border a b).toDual h |>.injective
  unfold solution
  rw [map_smul,LinearEquiv.apply_symm_apply,LinearEquiv.apply_symm_apply]
  change datum (r*s) (r • d) = r • datum s d
  apply LinearMap.ext
  intro v
  simp only [datum_apply,LinearMap.add_apply,LinearMap.smul_apply,smul_eq_mul]
  ring

/-- The vector component transforms intrinsically; only the auxiliary
scalar changes with the local line gauge. -/
theorem solution_covariance
    (a' : V →ₗ[K] K) (b' : LinearMap.BilinForm K V) (h' : (border a' b').Nondegenerate)
    (T : V ≃ₗ[K] V) (g : K) (dg : V →ₗ[K] K) (s s' : K) (d d' : V →ₗ[K] K)
    (hform : ∀ v, a' (T v) = g * a v)
    (hlevi : ∀ u v, b' (T u) (T v) = g * b u v + dg u * a v - dg v * a u)
    (hvalue : s' = g*s) (hderiv : ∀ v, d' (T v) = dg v * s + g * d v)
    (hg : g ≠ 0) :
    (solution a' b' h' s' d').1 = T (solution a b h s d).1 := by
  let u := (solution a b h s d).1
  let c := (solution a b h s d).2
  have hs : a u = s := solution_value a b h s d
  have hd (v : V) : b u v + c * a v = -d v := solution_levi a b h s d v
  have he := solution_unique a' b' h' s' d' (T u) (c - dg u / g)
    (by rw [hform,hs,hvalue]) (by
      intro w
      obtain ⟨v,rfl⟩ := T.surjective w
      rw [hlevi,hform,hderiv,hs]
      have he := hd v
      field_simp
      linear_combination g * he)
  exact (congrArg Prod.fst he).symm

end
end QuaternionicSymmetry.ContactHamiltonianAlgebra
