/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.GeometricFiber.AbelianMultiplicationMonodromyGroup
public import Nyll.EtaleFundamentalGroups.GeometricFiber.AbelianMultiplicationTranslations
public import Nyll.EtaleFundamentalGroups.GeometricFiber.AbelianUnitMultiplicationAlgebraicPoints
public import Nyll.EtaleFundamentalGroups.GeometricFiber.FundamentalGroup
public import Nyll.EtaleFundamentalGroups.GeometricFiber.FieldMonodromyLift
public import Nyll.EtaleFundamentalGroups.GaloisCategories.Functoriality
public import Nyll.SchemeTheory.CategoryTheory.SchemeHomOver

/-!
# Actual multiplication-cover action at an arbitrary geometric point

Transport through a path to the unit identifies actual monodromy with
translation by the same torsion point on every geometric fibre. Naturality
against the deck translation proves the comparison; it is not an input.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.PreGaloisCategory AlgebraicGeometry NeronModelInfra

open AlgebraicCurves.Geometry.AbelianSchemes.Theorems.Proofs
open RelativeGroupLaw_schemeNsmul_comp_eq_comp_schemeNsmul_of_hom.S17Glue

namespace GoodReductionJacobian.RelativeGroupLaw

variable {K : Type} [Field K] [IsAlgClosed K] [CharZero K]
  {A : Scheme} {f : A ⟶ Spec (.of K)} [IsProper f] [Smooth f]
  (G : RelativeGroupLaw K f) (hc : G.IsCommutative)
  {Ω : Type} [Field Ω] [IsSepClosed Ω]

omit [IsSepClosed Ω] in
/-- At any geometric point, actual monodromy is the deck translation whose
torsion parameter is obtained by transport to the unit. -/
theorem multiplicationFiber_smul_eq_translation
    (ξ : Spec (.of Ω) ⟶ A) (n : ℕ+)
    (τ : FiniteEtale.fiber ξ ≅ FiniteEtale.fiber (G.one (𝟙 (Spec (.of K)))).1)
    (g : π₁ᵉᵗ(ξ))
    (z : (FiniteEtale.fiber ξ).obj (G.multiplicationCover hc n)) :
    g • z = (FiniteEtale.fiber ξ).map
      (G.torsionDeckTranslation hc n
        (G.multiplicationMonodromy hc n (continuousConjAut τ g))).asIso.hom z := by
  have hn : IsUnit ((n : ℕ) : K) :=
    isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr n.ne_zero)
  exact UnitMultiplication.fiber_smul_eq_translation G hc ξ ⟨n, hn⟩ τ g z

/-- The transported monodromy acts on the actual point of the group scheme
by its actual group law, at the chosen geometric point. -/
theorem multiplicationFiberPoint_smul
    (ξ : Spec (.of Ω) ⟶ A) (n : ℕ+)
    (τ : FiniteEtale.fiber ξ ≅ FiniteEtale.fiber (G.one (𝟙 (Spec (.of K)))).1)
    (g : π₁ᵉᵗ(ξ))
    (z : (FiniteEtale.fiber ξ).obj (G.multiplicationCover hc n)) :
    G.multiplicationFiberPoint hc ξ n (g • z) =
      G.mul (ξ ≫ f) (G.multiplicationFiberPoint hc ξ n z)
        (GoodReductionJacobian.schemeHomOverComp (ξ ≫ f) (Category.comp_id (ξ ≫ f))
          (G.torsionPointSection hc n
            (G.multiplicationMonodromy hc n (continuousConjAut τ g)))) := by
  rw [G.multiplicationFiber_smul_eq_translation hc ξ n τ g z]
  exact G.multiplicationFiberPoint_map_translation hc ξ n
    (G.torsionPointSection hc n (G.multiplicationMonodromy hc n (continuousConjAut τ g)))
    (G.torsionPointSection_isTorsion hc n
      (G.multiplicationMonodromy hc n (continuousConjAut τ g))) z

omit [IsAlgClosed K] in
/-- Every point of the actual multiplication-cover fibre is an actual
division point of the chosen geometric point. -/
theorem multiplicationFiberPoint_nsmul
    (ξ : Spec (.of Ω) ⟶ A) (n : ℕ+)
    (z : (FiniteEtale.fiber ξ).obj (G.multiplicationCover hc n)) :
    G.nsmul (ξ ≫ f) (n : ℕ) (G.multiplicationFiberPoint hc ξ n z) =
      (⟨ξ, rfl⟩ : SchemeHomOver (ξ ≫ f) f) := by
  apply Subtype.ext
  rw [nsmul_coe_eq_comp_schemeNsmul]
  exact Over.w (FiniteEtale.fiberObjEquivHom ξ (G.multiplicationCover hc n) z)

/-- At a field-valued point, the actual Galois displacement of a division
point is the torsion point obtained from actual multiplication monodromy. -/
theorem multiplicationFiberPoint_field_action
    {L : Type} [Field L] [Algebra L Ω] [IsSepClosure L Ω]
    (j : Spec (.of L) ⟶ A) (n : ℕ+)
    (τ : FiniteEtale.fiber
        (Spec.map (CommRingCat.ofHom (algebraMap L Ω)) ≫ j) ≅
      FiniteEtale.fiber (G.one (𝟙 (Spec (.of K)))).1)
    (σ : Ω ≃ₐ[L] Ω)
    (z : (FiniteEtale.fiber
      (Spec.map (CommRingCat.ofHom (algebraMap L Ω)) ≫ j)).obj
        (G.multiplicationCover hc n)) :
    let xi := Spec.map (CommRingCat.ofHom (algebraMap L Ω))
    let g := FiniteEtale.fundamentalGroupHom j xi
      (toAut (FiniteEtale.fiber xi) (Ω ≃ₐ[L] Ω) σ)
    Spec.map (CommRingCat.ofHom σ.toRingHom) ≫
      (G.multiplicationFiberPoint hc (xi ≫ j) n z).1 =
      (G.mul ((xi ≫ j) ≫ f) (G.multiplicationFiberPoint hc (xi ≫ j) n z)
        (GoodReductionJacobian.schemeHomOverComp ((xi ≫ j) ≫ f)
          (Category.comp_id ((xi ≫ j) ≫ f))
          (G.torsionPointSection hc n
            (G.multiplicationMonodromy hc n (continuousConjAut τ g))))).1 := by
  intro xi g
  have hfield := FiniteEtale.fundamentalGroupHom_field_fiberLift j
    (G.multiplicationCover hc n) σ z
  change (G.multiplicationFiberPoint hc (xi ≫ j) n (g • z)).1 =
    Spec.map (CommRingCat.ofHom σ.toRingHom) ≫
      (G.multiplicationFiberPoint hc (xi ≫ j) n z).1 at hfield
  exact hfield.symm.trans (congrArg Subtype.val
    (G.multiplicationFiberPoint_smul hc (xi ≫ j) n τ g z))

end GoodReductionJacobian.RelativeGroupLaw
