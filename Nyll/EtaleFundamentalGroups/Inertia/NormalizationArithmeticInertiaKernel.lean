/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.Inertia.NormalLocalArithmeticDecomposition
public import Nyll.EtaleFundamentalGroups.Inertia.ConstantResidueRationality

/-!
# Full inertia at arbitrary closed affine points

For a maximal normalization prime over a finite-type algebra, the actual
constant-residue map is bijective even when the closed point is not
rational. The same residue calculation identifies full inertia with the
kernel of restriction to constants inside the original decomposition
group. Its images in the original fundamental group and every marked
quotient retain this exact intersection.
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
  [Field k] [CommRing A] [Field F] [Field κ] [Field Ω]
  [Algebra k A] [Algebra k F] [Algebra k κ] [Algebra k Ω]
  [Algebra A F] [IsFractionRing A F]
  [Algebra F Ω] [Algebra A Ω] [Algebra κ Ω]
  [IsScalarTower A F Ω] [IsScalarTower k A Ω]
  [IsScalarTower k F Ω] [IsScalarTower k κ Ω]
  [IsGalois F Ω] [IsAlgClosed κ] [IsAlgClosure k κ]
  (Q : Ideal (normalizationCommAlgCat A Ω)) [Q.IsMaximal]

omit [IsAlgClosed κ] [Q.IsMaximal] in
/-- In the original decomposition group, trivial arithmetic restriction is
exactly the full native ideal-inertia condition. -/
theorem normalization_mem_inertia_iff_restrict_constants_eq_one_of_residue_bijective
    (hf : Function.Bijective (arithmeticConstantResidueMap k A κ Ω Q))
    (d : normalizationDecompositionGroup A F Ω Q) :
    d.val ∈ Q.inertia Gal(Ω/F) ↔ (d.val.restrictScalars k).restrictNormal κ = 1 := by
  let B := normalizationCommAlgCat A Ω
  let c : κ →+* B := arithmeticConstantNormalizationMap k A κ Ω
  let δ := (d.val.restrictScalars k).restrictNormal κ
  have hc (x : κ) : c (δ x) = d.val • c x := by
    apply Subtype.ext
    have haction := congrArg (fun z : B →+* Ω => z (c x))
      (normalizationCommAlg_action_comp_inclusion A F Ω d.val)
    change d.val (algebraMap κ Ω x) =
      (show integralClosure A Ω from d.val • c x).val at haction
    exact ((d.val.restrictScalars k).restrictNormal_commutes κ x).trans haction
  constructor
  · intro hd
    apply AlgEquiv.ext
    intro x
    apply hf.injective
    change Ideal.Quotient.mk Q (c (δ x)) = Ideal.Quotient.mk Q (c x)
    rw [hc]
    have hzero := (Ideal.Quotient.eq_zero_iff_mem).mpr (hd (c x))
    simpa only [map_sub, sub_eq_zero] using hzero
  · intro hδ b
    obtain ⟨x, hx⟩ := hf.surjective (Ideal.Quotient.mk Q b)
    have hbc : b - c x ∈ Q := Ideal.Quotient.eq.mp hx.symm
    have hdb : d.val • (b - c x) ∈ Q := by
      have h := Ideal.smul_mem_pointwise_smul d.val (b - c x) Q hbc
      have hQ : d.val • Q = Q := d.property
      rwa [hQ] at h
    have hfix : d.val • c x = c x := by
      rw [← hc]
      exact congrArg c (DFunLike.congr_fun hδ x)
    rw [smul_sub, hfix] at hdb
    have hsub := Q.sub_mem hdb hbc
    have he : d.val • b - b = (d.val • b - c x) - (b - c x) := by abel
    exact he.symm ▸ hsub

/-- At an arbitrary closed point of a finite-type affine scheme, the
original inertia subgroup is exactly the kernel on algebraic constants. -/
theorem normalization_mem_inertia_iff_restrict_constants_eq_one_of_finiteType
    [Algebra.FiniteType k A] (d : normalizationDecompositionGroup A F Ω Q) :
    d.val ∈ Q.inertia Gal(Ω/F) ↔ (d.val.restrictScalars k).restrictNormal κ = 1 :=
  normalization_mem_inertia_iff_restrict_constants_eq_one_of_residue_bijective
    k A F κ Ω Q (arithmeticConstantResidueMap_bijective_of_finiteType k A κ Ω Q) d

end Native

section Images

variable (k A F κ Ω : Type u)
  [Field k] [CommRing A] [Field F] [Field κ] [Field Ω]
  [Algebra k A] [Algebra.FiniteType k A] [Algebra k F] [Algebra k κ] [Algebra k Ω]
  [Algebra A F] [IsFractionRing A F]
  [Algebra F Ω] [Algebra A Ω] [Algebra κ Ω]
  [IsScalarTower A F Ω] [IsScalarTower k A Ω]
  [IsScalarTower k F Ω] [IsScalarTower k κ Ω]
  [IsGalois F Ω] [IsAlgClosed κ] [IsAlgClosure k κ]
  [IsSepClosure k κ] [IsSepClosure F Ω] [IsSepClosed Ω]
  (Q : Ideal (normalizationCommAlgCat A Ω)) [Q.IsMaximal]
  {X : Scheme.{u}} [IsIntegral X]
  (c : X ⟶ Spec (.of k)) (j : Spec (.of F) ⟶ X)
  (hbase : (ξ F Ω ≫ j) ≫ c = ξ k Ω)

include hbase in
/-- The same original decomposition image meets the original arithmetic
kernel in precisely the original full inertia image. -/
theorem normalization_arithmetic_decomposition_inf_ker_eq_inertia_of_finiteType :
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
    refine ⟨d.val, (normalization_mem_inertia_iff_restrict_constants_eq_one_of_finiteType
      k A F κ Ω Q d).mpr ?_, rfl⟩
    have hconj : α * (d.val.restrictScalars k).restrictNormal κ * α⁻¹ = 1 :=
      (hα d.val).symm.trans hd
    have h := congrArg (fun z => α⁻¹ * z * α) hconj
    simpa only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one, one_mul] using h
  · rintro ⟨γ, hγ, rfl⟩
    let d : normalizationDecompositionGroup A F Ω Q := ⟨γ, Q.inertia_le_stabilizer hγ⟩
    refine ⟨⟨d, rfl⟩, ?_⟩
    change arithmeticFundamentalGroupHom k κ c (ξ F Ω ≫ j) (q γ) = 1
    rw [hα γ, (normalization_mem_inertia_iff_restrict_constants_eq_one_of_finiteType
      k A F κ Ω Q d).mp hγ]
    simp only [mul_one, mul_inv_cancel]

variable {P : Type v} [Group P]

include hbase in
/-- Any quotient over the original arithmetic projection retains the
exact inertia intersection, without a kernel-containment assumption. -/
theorem normalization_arithmetic_quotient_decomposition_inf_ker_eq_inertia_of_finiteType
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
    normalization_arithmetic_decomposition_inf_ker_eq_inertia_of_finiteType k A F κ Ω Q c j hbase
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
