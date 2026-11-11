/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.FiniteEtale.AdicClosedProjectiveHomFaithfulness
public import Nyll.EtaleFundamentalGroups.FiniteEtale.AdicCoverLevelUnit
public import Nyll.EtaleFundamentalGroups.FiniteEtale.AdicLevelPullbackModules
public import Nyll.SchemeTheory.ProjectiveSpace.Basic
public import Nyll.EtaleFundamentalGroups.FiniteEtale.AdicClosedProjectiveHomCompletion
public import Nyll.EtaleFundamentalGroups.FiniteEtale.AdicCoverAlgebraizedLocallyFree
public import Nyll.EtaleFundamentalGroups.FiniteEtale.AdicCoverAlgebraObjects
public import Nyll.EtaleFundamentalGroups.FiniteEtale.AdicCoverClosedProjectiveModuleAlgebraization
public import Nyll.EtaleFundamentalGroups.FiniteEtale.AdicCoverLevelUnitTransition
public import Nyll.SchemeTheory.Modules.FiniteType.FiniteTypeOfFiniteSections
public import Nyll.SchemeTheory.Modules.Quasicoherent.DirectImageAlgebraQuasicoherent
public import Nyll.SchemeTheory.Modules.Tensor.QuasicoherentTensor
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.CategoryTheory.Preadditive.Basic

/-!
# Algebra operations on the reconstructed original module

For the original compatible maps from an algebraized finite locally free
module to the actual cover modules, the established coherent Hom theorem
lifts their units and products. The original quotient comparisons carry
the compatible families into the literal quotients required by that
theorem. Faithfulness of all original closed reductions reflects the
stage algebra laws and makes those same maps monoid morphisms.

The coherent module, its local freeness, and its original comparison maps
are intermediate inputs supplied by the module algebraization and
flatness steps. No Hom reconstruction, lift, or algebra-law hypothesis is
an input to this construction.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Limits MonoidalCategory
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.FiniteEtale.AdicCoverTower

open Scheme.Modules ProjSpace

attribute [local instance] MvPolynomial.gradedAlgebra

variable (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
  [IsAdicComplete (IsLocalRing.maximalIdeal R) R] (n : ℕ)
  {Y : Scheme.{u}}
  (j : Y ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R))
  [IsClosedImmersion j]
  (V : MorphismProperty.Over
    ((@IsFinite : MorphismProperty Scheme.{u}) ⊓ @Etale) ⊤
      (level (j ≫ π R n) (IsLocalRing.maximalIdeal R) 0))
  (F : Y.Modules) [F.IsQuasicoherent] [F.IsFiniteType]
  (s : ∀ k : ℕ, F ⟶ moduleSheaf (j ≫ π R n) (IsLocalRing.maximalIdeal R) V k)
  [∀ k : ℕ, IsIso
    ((Scheme.Modules.pullback
      (Limits.pullback.fst (j ≫ π R n) (baseInclusion (IsLocalRing.maximalIdeal R) k))).map
        (s k))]
  (hs : ∀ k : ℕ, s (k + 1) ≫
    moduleTransition (j ≫ π R n) (IsLocalRing.maximalIdeal R) V k = s k)

omit [IsAdicComplete (IsLocalRing.maximalIdeal R) R] in
private theorem hom_ext_of_coverMaps (P : Y.Modules)
    [P.IsQuasicoherent] [P.IsFiniteType] (a b : P ⟶ F)
    (hab : ∀ k : ℕ, a ≫ s k = b ≫ s k) : a = b := by
  apply sub_eq_zero.mp
  apply hom_eq_zero_of_forall_levelPullbackUnit_comp_eq_zero R n j P F (a - b)
  intro k
  let e := moduleSheafLevelQuotientIso
    (j ≫ π R n) (IsLocalRing.maximalIdeal R) V F k (s k)
  apply (cancel_mono e.hom).mp
  rw [Category.assoc, levelUnit_moduleSheafLevelQuotientIso_hom,
    Preadditive.sub_comp, hab k, sub_self, zero_comp]

include hs

private theorem existsUnique_hom_to_coverMaps
    (hF : finiteFreeLocus F = ⊤)
    (P : Y.Modules) [P.IsQuasicoherent] [P.IsFiniteType]
    (β : ∀ k : ℕ, P ⟶
      moduleSheaf (j ≫ π R n) (IsLocalRing.maximalIdeal R) V k)
    (hβ : ∀ k : ℕ, β (k + 1) ≫
      moduleTransition (j ≫ π R n) (IsLocalRing.maximalIdeal R) V k = β k) :
    ∃! a : P ⟶ F, ∀ k : ℕ, a ≫ s k = β k := by
  let e (k : ℕ) := moduleSheafLevelQuotientIso
    (j ≫ π R n) (IsLocalRing.maximalIdeal R) V F k (s k)
  let γ (k : ℕ) : P ⟶
      levelPullbackModule (j ≫ π R n) (IsLocalRing.maximalIdeal R) F k :=
    β k ≫ (e k).inv
  have hγ : ∀ k : ℕ, γ (k + 1) ≫
      levelPullbackTransition (j ≫ π R n) (IsLocalRing.maximalIdeal R) F k = γ k := by
    intro k
    change (β (k + 1) ≫ (e (k + 1)).inv) ≫
        levelPullbackTransition (j ≫ π R n) (IsLocalRing.maximalIdeal R) F k =
          β k ≫ (e k).inv
    rw [Category.assoc, moduleSheafLevelQuotientIso_inv_transition
      (j ≫ π R n) (IsLocalRing.maximalIdeal R) V F s hs k,
      ← Category.assoc, hβ k]
  obtain ⟨a, ha, _⟩ :=
    existsUnique_hom_of_compatible_levelMaps_to_locallyFree R n j P F hF γ hγ
  have ha' : ∀ k : ℕ, a ≫ s k = β k := by
    intro k
    have he :
        levelPullbackUnit (j ≫ π R n) (IsLocalRing.maximalIdeal R) F k ≫ (e k).hom =
          s k :=
      levelUnit_moduleSheafLevelQuotientIso_hom
        (j ≫ π R n) (IsLocalRing.maximalIdeal R) V F k (s k)
    calc
      a ≫ s k = a ≫
          (levelPullbackUnit (j ≫ π R n) (IsLocalRing.maximalIdeal R) F k ≫
            (e k).hom) := congrArg (fun b => a ≫ b) he.symm
      _ = (a ≫ levelPullbackUnit (j ≫ π R n) (IsLocalRing.maximalIdeal R) F k) ≫
          (e k).hom := (Category.assoc _ _ _).symm
      _ = (β k ≫ (e k).inv) ≫ (e k).hom :=
        congrArg (fun b => b ≫ (e k).hom) (ha k)
      _ = β k := by rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  refine ⟨a, ha', ?_⟩
  intro b hb
  exact hom_ext_of_coverMaps R n j V F s P b a
    (fun k => (hb k).trans (ha' k).symm)

/-- The original compatible cover comparisons lift the actual stage
units and products to a commutative monoid object on the reconstructed
finite locally free module. Every original comparison is a monoid map. -/
theorem exists_commMonObj_of_compatible_coverMaps
    (hF : finiteFreeLocus F = ⊤) :
    ∃ m : MonObj F, let _ : MonObj F := m
      IsCommMonObj F ∧ ∀ k : ℕ, IsMonHom (s k) := by
  let B (k : ℕ) := moduleSheaf (j ≫ π R n) (IsLocalRing.maximalIdeal R) V k
  let t (k : ℕ) := moduleTransition (j ≫ π R n) (IsLocalRing.maximalIdeal R) V k
  let U : Y.Modules := 𝟙_ Y.Modules
  have : U.IsQuasicoherent := isQuasicoherent_unit Y
  have : U.IsFiniteType := by
    apply isFiniteType_of_finite_affine_sections U
    intro W _hW
    exact inferInstanceAs (Module.Finite Γ(Y, W) Γ(Y, W))
  have : (F ⊗ F).IsQuasicoherent := isQuasicoherent_tensor F F
  have : (F ⊗ F).IsFiniteType := isFiniteType_tensor F F
  have : (U ⊗ F).IsQuasicoherent := isQuasicoherent_tensor U F
  have : (U ⊗ F).IsFiniteType := isFiniteType_tensor U F
  have : (F ⊗ U).IsQuasicoherent := isQuasicoherent_tensor F U
  have : (F ⊗ U).IsFiniteType := isFiniteType_tensor F U
  have : ((F ⊗ F) ⊗ F).IsQuasicoherent := isQuasicoherent_tensor (F ⊗ F) F
  have : ((F ⊗ F) ⊗ F).IsFiniteType := isFiniteType_tensor (F ⊗ F) F
  obtain ⟨u, hu, _⟩ :=
    existsUnique_hom_to_coverMaps R n j V F s hs hF U
      (fun k => η[B k]) (fun k => IsMonHom.one_hom (t k))
  let β (k : ℕ) : F ⊗ F ⟶ B k := (s k ⊗ₘ s k) ≫ μ[B k]
  have hβ : ∀ k : ℕ, β (k + 1) ≫ t k = β k := by
    intro k
    change ((s (k + 1) ⊗ₘ s (k + 1)) ≫ μ[B (k + 1)]) ≫ t k =
      (s k ⊗ₘ s k) ≫ μ[B k]
    rw [Category.assoc, IsMonHom.mul_hom, ← Category.assoc,
      tensorHom_comp_tensorHom, hs k]
  obtain ⟨m, hm, _⟩ :=
    existsUnique_hom_to_coverMaps R n j V F s hs hF (F ⊗ F) β hβ
  let algebra : MonObj F :=
    { one := u
      mul := m
      one_mul := by
        apply hom_ext_of_coverMaps R n j V F s (U ⊗ F)
        intro k
        change ((u ▷ F) ≫ m) ≫ s k = (λ_ F).hom ≫ s k
        rw [Category.assoc, hm k, ← Category.assoc, ← tensorHom_id,
          tensorHom_comp_tensorHom, Category.id_comp, hu k, MonObj.one_mul_hom]
      mul_one := by
        apply hom_ext_of_coverMaps R n j V F s (F ⊗ U)
        intro k
        change ((F ◁ u) ≫ m) ≫ s k = (ρ_ F).hom ≫ s k
        rw [Category.assoc, hm k, ← Category.assoc, ← id_tensorHom,
          tensorHom_comp_tensorHom, Category.id_comp, hu k, MonObj.mul_one_hom]
      mul_assoc := by
        apply hom_ext_of_coverMaps R n j V F s ((F ⊗ F) ⊗ F)
        intro k
        have hleft : (m ▷ F) ≫ (s k ⊗ₘ s k) =
            ((s k ⊗ₘ s k) ⊗ₘ s k) ≫ (μ[B k] ▷ B k) := by
          calc
            (m ▷ F) ≫ (s k ⊗ₘ s k) = (m ≫ s k) ⊗ₘ s k := by
              rw [← tensorHom_id, tensorHom_comp_tensorHom, Category.id_comp]
            _ = β k ⊗ₘ s k := congrArg (fun a => a ⊗ₘ s k) (hm k)
            _ = ((s k ⊗ₘ s k) ⊗ₘ s k) ≫ (μ[B k] ▷ B k) := by
              change (((s k ⊗ₘ s k) ≫ μ[B k]) ⊗ₘ s k) = _
              rw [← tensorHom_id, tensorHom_comp_tensorHom, Category.comp_id]
        have hright : (F ◁ m) ≫ (s k ⊗ₘ s k) =
            (s k ⊗ₘ (s k ⊗ₘ s k)) ≫ (B k ◁ μ[B k]) := by
          calc
            (F ◁ m) ≫ (s k ⊗ₘ s k) = s k ⊗ₘ (m ≫ s k) := by
              rw [← id_tensorHom, tensorHom_comp_tensorHom, Category.id_comp]
            _ = s k ⊗ₘ β k := congrArg (fun a => s k ⊗ₘ a) (hm k)
            _ = (s k ⊗ₘ (s k ⊗ₘ s k)) ≫ (B k ◁ μ[B k]) := by
              change (s k ⊗ₘ ((s k ⊗ₘ s k) ≫ μ[B k])) = _
              rw [← id_tensorHom, tensorHom_comp_tensorHom, Category.comp_id]
        have hnat := congrArg (fun a => a ≫ (B k ◁ μ[B k]) ≫ μ[B k])
          (associator_naturality (s k) (s k) (s k))
        calc
          ((m ▷ F) ≫ m) ≫ s k =
              ((s k ⊗ₘ s k) ⊗ₘ s k) ≫ ((μ[B k] ▷ B k) ≫ μ[B k]) := by
            rw [Category.assoc, hm k, ← Category.assoc, hleft, Category.assoc]
          _ = ((s k ⊗ₘ s k) ⊗ₘ s k) ≫
              ((α_ (B k) (B k) (B k)).hom ≫ (B k ◁ μ[B k]) ≫ μ[B k]) :=
            congrArg (fun a => ((s k ⊗ₘ s k) ⊗ₘ s k) ≫ a) (MonObj.mul_assoc (B k))
          _ = (α_ F F F).hom ≫
              ((s k ⊗ₘ (s k ⊗ₘ s k)) ≫ (B k ◁ μ[B k]) ≫ μ[B k]) := by
            simpa only [Category.assoc] using hnat
          _ = ((α_ F F F).hom ≫ (F ◁ m) ≫ m) ≫ s k := by
            rw [Category.assoc, Category.assoc, hm k, ← Category.assoc (F ◁ m),
              hright, Category.assoc]
    }
  let : MonObj F := algebra
  refine ⟨algebra, ?_, ?_⟩
  · refine ⟨?_⟩
    apply hom_ext_of_coverMaps R n j V F s (F ⊗ F)
    intro k
    change ((β_ F F).hom ≫ m) ≫ s k = m ≫ s k
    rw [Category.assoc, hm k, ← Category.assoc, ← BraidedCategory.braiding_naturality,
      Category.assoc, IsCommMonObj.mul_comm]
  · intro k
    exact ⟨hu k, hm k⟩

end AlgebraicGeometry.FiniteEtale.AdicCoverTower

namespace AlgebraicGeometry.FiniteEtale.AdicCoverTower

open Scheme.Modules ProjSpace

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The original closed-fiber finite étale cover over a complete
Noetherian local projective family has an actual finite locally free
commutative module-algebra algebraization. Its original comparison maps
recover every closed level, commute with the original transitions, and
preserve the units and multiplications. -/
theorem exists_closedProjective_commMonObj_algebraization
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R] (n : ℕ)
    {Y : Scheme.{u}}
    (j : Y ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R))
    [IsClosedImmersion j]
    (V : MorphismProperty.Over
      ((@IsFinite : MorphismProperty Scheme.{u}) ⊓ @Etale) ⊤
        (level (j ≫ π R n) (IsLocalRing.maximalIdeal R) 0)) :
    ∃ F : Y.Modules, F.IsQuasicoherent ∧ F.IsFiniteType ∧
      finiteFreeLocus F = ⊤ ∧
      ∃ m : MonObj F, let _ : MonObj F := m
        IsCommMonObj F ∧ ∃ s : ∀ k : ℕ, F ⟶
            moduleSheaf (j ≫ π R n) (IsLocalRing.maximalIdeal R) V k,
          (∀ k : ℕ, IsIso
            ((Scheme.Modules.pullback
              (Limits.pullback.fst (j ≫ π R n)
                (baseInclusion (IsLocalRing.maximalIdeal R) k))).map (s k))) ∧
          (∀ k : ℕ, s (k + 1) ≫
            moduleTransition (j ≫ π R n) (IsLocalRing.maximalIdeal R) V k = s k) ∧
          (∀ k : ℕ, IsMonHom (s k)) := by
  obtain ⟨F, hFqc, hFft, s, hsIso, hs⟩ :=
    exists_closedProjective_module_algebraization R n j V
  have : F.IsQuasicoherent := hFqc
  have : F.IsFiniteType := hFft
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (j ≫ π R n)
  have hF : finiteFreeLocus F = ⊤ :=
    finiteFreeLocus_eq_top_of_adicCoverPullback_isIso (j ≫ π R n) V F s hsIso
  have (k : ℕ) : IsIso
      ((Scheme.Modules.pullback
        (Limits.pullback.fst (j ≫ π R n)
          (baseInclusion (IsLocalRing.maximalIdeal R) k))).map (s k)) := hsIso k
  obtain ⟨m, hm⟩ := exists_commMonObj_of_compatible_coverMaps R n j V F s hs hF
  let : MonObj F := m
  exact ⟨F, hFqc, hFft, hF, m, hm.1, s, hsIso, hs, hm.2⟩

end AlgebraicGeometry.FiniteEtale.AdicCoverTower
