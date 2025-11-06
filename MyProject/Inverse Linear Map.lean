import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Module.LinearMap.Defs

variable {K V W : Type*} [Field K]
  [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]

def idLinear : V →ₗ[K] V :=
{ toFun := id,
  map_add' := by simp,
  map_smul' := by simp }

open Function

noncomputable section

-- Inverse of a linear isomorphism is linear.
def inverse_map (f : V →ₗ[K] V) (h : Bijective f) : V →ₗ[K] V :=
{
  toFun := invFun f.toFun,
  map_add' := by
    intro w₁ w₂
    let p := f.toFun
    let q := invFun f.toFun
    let v₁ := q w₁
    let v₂ := q w₂
    have h₁ : v₁ + v₂ = q (w₁ + w₂) := by
      have h₃ : p (v₁ + v₂) = p (v₁) + p (v₂) := by
        exact f.map_add' v₁ v₂
      rw [ ] at h₃
    sorry
    ,
  map_smul' := sorry
}
