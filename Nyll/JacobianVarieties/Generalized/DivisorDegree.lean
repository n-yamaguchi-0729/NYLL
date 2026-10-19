/-
Copyright (c) 2026 Naganori Yamaguchi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
Repository: https://github.com/n-yamaguchi-0729
-/

import Nyll.JacobianVarieties.Generalized.DivisorClasses

/-!
# Degree and the degree-zero modulus class group

The quotient of degree-zero divisors is identified with the kernel of degree
on the full modulus class group. The only geometric input is the existing
degree-zero theorem for principal divisors.
-/

noncomputable section

namespace AlgebraicCurve.Modulus

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

/-- Degree on the full divisor class group with modulus. -/
def classDegree [HasPrincipalDivisors K F] (D : Modulus K F) : D.ClassGroup →+ ℤ :=
  QuotientAddGroup.lift _ (Divisor.degree.comp D.divAway.subtype) (by
    intro E hE
    exact D.principal_le_degZero hE)

@[simp]
theorem classDegree_mk [HasPrincipalDivisors K F] (D : Modulus K F) (E : D.divAway) :
    D.classDegree (QuotientAddGroup.mk E) = Divisor.degree (E : Divisor K F) := rfl

/-- Forget only the degree-zero constraint on a modulus divisor class. -/
def includeZero (D : Modulus K F) : D.ClassGroupZero →+ D.ClassGroup :=
  QuotientAddGroup.map _ _ (AddSubgroup.inclusion inf_le_left) (by
    intro E hE
    exact hE)

/-- The degree-zero modulus class group embeds in the full one. -/
theorem includeZero_injective (D : Modulus K F) : Function.Injective D.includeZero := by
  apply (injective_iff_map_eq_zero D.includeZero).mpr
  intro x hx
  obtain ⟨E, rfl⟩ := QuotientAddGroup.mk_surjective x
  apply (QuotientAddGroup.eq_zero_iff E).mpr
  exact (QuotientAddGroup.eq_zero_iff (AddSubgroup.inclusion inf_le_left E)).mp hx

/-- Every included degree-zero class has degree zero. -/
@[simp]
theorem classDegree_includeZero [HasPrincipalDivisors K F] (D : Modulus K F)
    (x : D.ClassGroupZero) :
    D.classDegree (D.includeZero x) = 0 := by
  obtain ⟨E, rfl⟩ := QuotientAddGroup.mk_surjective x
  exact E.2.2

/-- The image of degree-zero classes is exactly the kernel of degree. -/
theorem range_includeZero [HasPrincipalDivisors K F] (D : Modulus K F) :
    D.includeZero.range = D.classDegree.ker := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact classDegree_includeZero D y
  · intro hx
    obtain ⟨E, rfl⟩ := QuotientAddGroup.mk_surjective x
    exact ⟨D.mkZero ⟨E.1, E.2, hx⟩, rfl⟩

/-- The canonical map into the degree kernel. -/
def toDegreeKernel [HasPrincipalDivisors K F] (D : Modulus K F) :
    D.ClassGroupZero →+ D.classDegree.ker :=
  D.includeZero.codRestrict _ (classDegree_includeZero D)

/-- The two definitions of degree-zero modulus classes agree. -/
def degreeKernelEquiv [HasPrincipalDivisors K F] (D : Modulus K F) :
    D.ClassGroupZero ≃+ D.classDegree.ker :=
  AddEquiv.ofBijective D.toDegreeKernel ⟨(by
    intro x y h
    exact D.includeZero_injective (congrArg Subtype.val h)), (by
    intro x
    have hx : x.1 ∈ D.includeZero.range := by
      rw [range_includeZero]
      exact x.2
    obtain ⟨y, hy⟩ := hx
    exact ⟨y, Subtype.ext hy⟩)⟩

end AlgebraicCurve.Modulus
