/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.Inertia.NormalizationArithmeticInertiaKernel

/-!
# The arithmetic kernel in the original normalization decomposition image

The canonical constant-residue map identifies the algebraic constant
closure with the residue field at the same original normalization prime.
Consequently an element of its decomposition group is inertial exactly
when its restriction to constants is trivial. The original field-source
map then identifies the geometric intersection of its decomposition image
with its full inertia image, also after any quotient over the arithmetic
projection. All wild inertia is retained.
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory AlgebraicGeometry.FiniteEtale SchemeTheory
open scoped Pointwise

namespace EtaleFundamentalGroups.Inertia

universe u v

attribute [local instance] normalizationCommAlgGaloisAction

section Native

variable (k A F κ Ω : Type u)
  [Field k] [CommRing A] [IsLocalRing A] [Field F] [Field κ] [Field Ω]
  [Algebra k A] [Algebra k F] [Algebra k κ] [Algebra k Ω]
  [Algebra A F] [IsFractionRing A F]
  [Algebra F Ω] [Algebra A Ω] [Algebra κ Ω]
  [IsScalarTower A F Ω] [IsScalarTower k A Ω]
  [IsScalarTower k F Ω] [IsScalarTower k κ Ω]
  [IsGalois F Ω] [IsAlgClosed κ] [IsAlgClosure k κ]
  (Q : Ideal (normalizationCommAlgCat A Ω)) [Q.IsMaximal]
  (r : A →ₐ[k] k) (hr : RingHom.ker r.toRingHom = IsLocalRing.maximalIdeal A)

include r hr in
/-- In the original decomposition group, trivial arithmetic restriction is
exactly the full native ideal-inertia condition. -/
theorem normalLocal_mem_inertia_iff_restrict_constants_eq_one
    (d : normalizationDecompositionGroup A F Ω Q) :
    d.val ∈ Q.inertia Gal(Ω/F) ↔ (d.val.restrictScalars k).restrictNormal κ = 1 :=
  normalization_mem_inertia_iff_restrict_constants_eq_one_of_residue_bijective
    k A F κ Ω Q (arithmeticConstantResidueMap_bijective k A κ Ω Q r hr) d

end Native

section Images

variable (k A F κ Ω : Type u)
  [Field k] [CommRing A] [IsLocalRing A] [Field F] [Field κ] [Field Ω]
  [Algebra k A] [Algebra k F] [Algebra k κ] [Algebra k Ω]
  [Algebra A F] [IsFractionRing A F]
  [Algebra F Ω] [Algebra A Ω] [Algebra κ Ω]
  [IsScalarTower A F Ω] [IsScalarTower k A Ω]
  [IsScalarTower k F Ω] [IsScalarTower k κ Ω]
  [IsGalois F Ω] [IsAlgClosed κ] [IsAlgClosure k κ]
  [IsSepClosure k κ] [IsSepClosure F Ω] [IsSepClosed Ω]
  (Q : Ideal (normalizationCommAlgCat A Ω)) [Q.IsMaximal]
  (r : A →ₐ[k] k) (hr : RingHom.ker r.toRingHom = IsLocalRing.maximalIdeal A)
  {X : Scheme.{u}} [IsIntegral X]
  (c : X ⟶ Spec (.of k)) (j : Spec (.of F) ⟶ X)
  (hbase : (ξ F Ω ≫ j) ≫ c = ξ k Ω)

include r hr hbase in
/-- The same original decomposition image meets the original arithmetic
kernel in precisely the original full inertia image. -/
theorem normalLocal_arithmetic_decomposition_inf_ker_eq_inertia :
    let q := fieldSourceAbsoluteGaloisHom F Ω j
    let π := arithmeticFundamentalGroupHom k κ c (ξ F Ω ≫ j)
    (q.toMonoidHom.comp (normalizationDecompositionInclusion A F Ω Q)).range ⊓
        π.toMonoidHom.ker =
      (Q.inertia Gal(Ω/F)).map q.toMonoidHom := by
  intro q π
  obtain ⟨α, hα⟩ := exists_fieldSource_arithmetic_restriction_label k F κ Ω c j hbase
  ext x
  constructor
  · rintro ⟨⟨d, rfl⟩, hd⟩
    refine ⟨d.val, (normalLocal_mem_inertia_iff_restrict_constants_eq_one
      k A F κ Ω Q r hr d).mpr ?_, rfl⟩
    have hconj : α * (d.val.restrictScalars k).restrictNormal κ * α⁻¹ = 1 :=
      (hα d.val).symm.trans hd
    have h := congrArg (fun z => α⁻¹ * z * α) hconj
    simpa only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one, one_mul] using h
  · rintro ⟨γ, hγ, rfl⟩
    let d : normalizationDecompositionGroup A F Ω Q := ⟨γ, Q.inertia_le_stabilizer hγ⟩
    refine ⟨⟨d, rfl⟩, ?_⟩
    change arithmeticFundamentalGroupHom k κ c (ξ F Ω ≫ j) (q γ) = 1
    rw [hα γ, (normalLocal_mem_inertia_iff_restrict_constants_eq_one
      k A F κ Ω Q r hr d).mp hγ]
    simp only [mul_one, mul_inv_cancel]

variable {P : Type v} [Group P]

include r hr hbase in
/-- Any quotient over the original arithmetic projection retains the
exact inertia intersection, without a kernel-containment assumption. -/
theorem normalLocal_arithmetic_quotient_decomposition_inf_ker_eq_inertia
    (ρ : π₁ᵉᵗ(ξ F Ω ≫ j) →* P) (π : P →* Gal(κ/k))
    (hπ : π.comp ρ = (arithmeticFundamentalGroupHom k κ c (ξ F Ω ≫ j)).toMonoidHom) :
    let q := ρ.comp (fieldSourceAbsoluteGaloisHom F Ω j).toMonoidHom
    (q.comp (normalizationDecompositionInclusion A F Ω Q)).range ⊓ π.ker =
      (Q.inertia Gal(Ω/F)).map q := by
  intro q
  let q₀ := (fieldSourceAbsoluteGaloisHom F Ω j).toMonoidHom
  let D := (q₀.comp (normalizationDecompositionInclusion A F Ω Q)).range
  let π₀ := (arithmeticFundamentalGroupHom k κ c (ξ F Ω ≫ j)).toMonoidHom
  have hnative : D ⊓ π₀.ker = (Q.inertia Gal(Ω/F)).map q₀ :=
    normalLocal_arithmetic_decomposition_inf_ker_eq_inertia k A F κ Ω Q r hr c j hbase
  ext x
  constructor
  · rintro ⟨⟨d, rfl⟩, hd⟩
    have hgeom : q₀ d.val ∈ π₀.ker := by
      change π₀ (q₀ d.val) = 1
      exact (DFunLike.congr_fun hπ (q₀ d.val)).symm.trans hd
    have hi : q₀ d.val ∈ (Q.inertia Gal(Ω/F)).map q₀ :=
      hnative ▸ (show q₀ d.val ∈ D ⊓ π₀.ker from ⟨⟨d, rfl⟩, hgeom⟩)
    obtain ⟨γ, hγ, hγd⟩ := hi
    exact ⟨γ, hγ, congrArg ρ hγd⟩
  · rintro ⟨γ, hγ, rfl⟩
    have hi : q₀ γ ∈ D ⊓ π₀.ker :=
      hnative.symm ▸ (show q₀ γ ∈ (Q.inertia Gal(Ω/F)).map q₀ from ⟨γ, hγ, rfl⟩)
    obtain ⟨d, hd⟩ := hi.1
    exact ⟨⟨d, congrArg ρ hd⟩,
      (DFunLike.congr_fun hπ (q₀ γ)).trans hi.2⟩

end Images

end EtaleFundamentalGroups.Inertia
