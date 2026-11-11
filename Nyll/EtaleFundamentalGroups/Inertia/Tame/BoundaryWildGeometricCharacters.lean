/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.Inertia.Tame.BoundaryWildCharacters
public import Nyll.ProCGroups.Topologies.ContinuousMulEquiv

/-!
# Geometric character comparison for the boundary-wild quotient

The original quotient induces a surjection between the original arithmetic
kernels. Pullback along this literal map is a bijection on continuous pro-ell
characters whenever ell differs from the base characteristic.
-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.FiniteEtale
open CategoryTheory.PreGaloisCategory TopologicalSpace SchemeTheory
open ProCGroups ProCGroups.ProC

namespace EtaleFundamentalGroups.Tame

universe u v w

/-- A character of a compact group descends continuously along a surjective
continuous homomorphism exactly when its kernel contains the projection kernel. -/
theorem exists_continuous_factor_of_surjective
    {G : Type u} {B : Type v} {H : Type w} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [Group B] [TopologicalSpace B] [T2Space B]
    [Group H] [TopologicalSpace H]
    (q : G →ₜ* B) (hq : Function.Surjective q) (χ : G →ₜ* H)
    (hχ : q.toMonoidHom.ker ≤ χ.toMonoidHom.ker) :
    ∃ ψ : B →ₜ* H, ψ.comp q = χ := by
  let N := q.toMonoidHom.ker
  let f : G ⧸ N →ₜ* B := QuotientGroup.liftₜ N q le_rfl
  have hf : Function.Bijective f := by
    constructor
    · exact QuotientGroup.kerLift_injective q.toMonoidHom
    · intro b
      obtain ⟨g, rfl⟩ := hq b
      exact ⟨QuotientGroup.mk' N g, rfl⟩
  let e := ContinuousMulEquiv.ofBijectiveCompactToT2 f.toMonoidHom f.continuous_toFun hf
  let χq := QuotientGroup.liftₜ N χ hχ
  refine ⟨χq.comp (ContinuousMonoidHom.toContinuousMonoidHom e.symm), ?_⟩
  apply ContinuousMonoidHom.ext
  intro g
  change χq (e.symm (q g)) = χ g
  have he : e (QuotientGroup.mk' N g) = q g := rfl
  rw [← he, e.symm_apply_apply]
  rfl

variable (k F Ω : Type u) [Field k] [Field F] [Field Ω]
  [Algebra F Ω] [IsSepClosure F Ω] [IsSepClosed Ω]
  {X U : Scheme.{u}} [IsIntegral X] [IsIntegral U]
  (c : X ⟶ Spec (.of k)) [SmoothOfRelativeDimension 1 c]
  (j : U ⟶ X) [IsOpenImmersion j]
  (p : Spec (.of F) ⟶ U) [IsDominant p] [IsPreimmersion p]
  (κ : Type u) [Field κ] [Algebra k F] [Algebra k κ] [Algebra k Ω]
  [Algebra κ Ω] [IsScalarTower k F Ω] [IsScalarTower k κ Ω]
  [IsAlgClosure k κ] [IsSepClosure k κ]
  (hp : (p ≫ j) ≫ c = Spec.map (CommRingCat.ofHom (algebraMap k F)))

local notation "π" => arithmeticFundamentalGroupHom k κ (j ≫ c) (ξ F Ω ≫ p)
local notation "πt" => boundaryWildArithmeticProjection k F Ω c j p κ hp

/-- The quotient map restricted to the actual kernels of the original and
descended arithmetic projections. -/
def boundaryWildGeometricProjection : (π).toMonoidHom.ker →ₜ* (πt).toMonoidHom.ker :=
  { toMonoidHom :=
      { toFun := fun d => ⟨boundaryWildProjection k F Ω c j p d.val, d.property⟩
        map_one' := Subtype.ext (map_one (boundaryWildProjection k F Ω c j p))
        map_mul' := fun d e => Subtype.ext
          (map_mul (boundaryWildProjection k F Ω c j p) d.val e.val) }
    continuous_toFun := ((boundaryWildProjection k F Ω c j p).continuous_toFun.comp
      continuous_subtype_val).subtype_mk _ }

/-- The geometric map keeps the original quotient representative. -/
@[simp] theorem boundaryWildGeometricProjection_apply (d : (π).toMonoidHom.ker) :
    (boundaryWildGeometricProjection k F Ω c j p κ hp d).val =
      boundaryWildProjection k F Ω c j p d.val := rfl

/-- Every element of the tame arithmetic kernel lifts to the original
arithmetic kernel, using the original arithmetic square. -/
theorem boundaryWildGeometricProjection_surjective :
    Function.Surjective (boundaryWildGeometricProjection k F Ω c j p κ hp) := by
  intro d
  obtain ⟨g, hg⟩ := boundaryWildProjection_surjective k F Ω c j p d.val
  have hgeo : g ∈ (π).toMonoidHom.ker := by
    change π g = 1
    exact (congrArg πt hg).trans d.property
  exact ⟨⟨g, hgeo⟩, Subtype.ext hg⟩

/-- The kernel is the original boundary-wild subgroup inside the original
geometric group. -/
theorem mem_boundaryWildGeometricProjection_ker (d : (π).toMonoidHom.ker) :
    d ∈ (boundaryWildGeometricProjection k F Ω c j p κ hp).toMonoidHom.ker ↔
      d.val ∈ boundaryWildKernel k F Ω c j p := by
  constructor
  · intro hd
    exact (QuotientGroup.eq_one_iff d.val).mp (congrArg Subtype.val hd)
  · intro hd
    exact Subtype.ext ((QuotientGroup.eq_one_iff d.val).mpr hd)

variable (r ℓ : ℕ) [Fact r.Prime] [Fact ℓ.Prime] [CharP k r] (hrℓ : r ≠ ℓ)

include hrℓ in
/-- Pullback along the original geometric quotient is bijective on continuous
pro-ell characters. In particular it gives the character comparison used for
prime-to-characteristic geometric H¹, with its original source map. -/
theorem boundaryWild_geometric_character_pullback_bijective
    {H : Type v} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H]
    (hH : HasOpenNormalBasisInClass (FiniteGroupClass.pGroup ℓ) H) :
    Function.Bijective (fun χ : (πt).toMonoidHom.ker →ₜ* H =>
      χ.comp (boundaryWildGeometricProjection k F Ω c j p κ hp)) := by
  let q := boundaryWildGeometricProjection k F Ω c j p κ hp
  have hq := boundaryWildGeometricProjection_surjective k F Ω c j p κ hp
  constructor
  · intro χ ψ h
    apply ContinuousMonoidHom.ext
    intro d
    obtain ⟨g, rfl⟩ := hq d
    exact DFunLike.congr_fun h g
  · intro χ
    have : CompactSpace (π).toMonoidHom.ker := isCompact_iff_compactSpace.mp
      (ContinuousMonoidHom.isClosed_ker π).isCompact
    apply exists_continuous_factor_of_surjective q hq χ
    intro d hd
    exact boundaryWild_geometric_character_eq_one k F Ω c j p κ hp r ℓ hrℓ hH χ d
      ((mem_boundaryWildGeometricProjection_ker k F Ω c j p κ hp d).mp hd)

end EtaleFundamentalGroups.Tame
