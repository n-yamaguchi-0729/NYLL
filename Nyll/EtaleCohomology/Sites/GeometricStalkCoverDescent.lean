/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleCohomology.Sites.GeometricStalkSchemeLimit
import Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalkFlat
import Nyll.SchemeTheory.Descent.AffineTransitionCover
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction

/-!
# Spreading an affine étale covering from the actual strict-local base

An affine open in the strict-local pullback of an affine étale object,
covering the original strict-local source, comes from a covering affine
open over a pointed affine étale neighborhood. The recovery map is the
actual geometric-stalk germ and all pullbacks are native scheme pullbacks.

Only quasi-compactness of the original source over the affine base is
needed. No continuity assertion about arbitrary coefficient sheaves is
assumed in this geometric covering step.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Limits Opposite
open EtaleFundamentalGroups.StrictHenselian

namespace EtaleCohomology

universe u

/-- Every actual coefficient spectrum admits a pointed affine étale
refinement through which its geometric-stalk germ factors literally. -/
theorem geometricStalk_exists_affine_coefficientFactor
    {R Ω : Type u} [CommRing R] [Field Ω] [IsSepClosed Ω]
    (φ : R →+* Ω) (i : (GeometricStalkAlgebraIndex φ)ᵒᵖ) :
    ∃ (V : (Spec (CommRingCat.of R)).Etale)
      (v : (Scheme.pointSmallEtale (Spec.map (CommRingCat.ofHom φ))).fiber.obj V)
      (_ : IsAffine V.left)
      (ρ : Spec (geometricStalk (Spec.map (CommRingCat.ofHom φ))) ⟶ V.left)
      (_ : ρ ≫ V.hom = Spec.map (CommRingCat.ofHom (geometricStalkStructureMap φ)))
      (b : V.left ⟶ ((geometricStalkSpecDiagram φ).obj i).left),
      ρ = Spec.map (geometricStalkGerm (Spec.map (CommRingCat.ofHom φ)) V v) ≫
          V.left.isoSpec.inv ∧
      b ≫ ((geometricStalkSpecDiagram φ).obj i).hom = V.hom ∧
      ρ ≫ b = ((geometricStalkSpecCone φ).π.app i).left := by
  let D := geometricStalkSpecDiagram φ
  let c := geometricStalkSpecCone φ
  let j := (FinallySmall.fromFilteredFinalModel
    (Scheme.pointSmallEtale (Spec.map (CommRingCat.ofHom φ))).fiber.Elementsᵒᵖ).obj i.unop
  let Z : (Spec (CommRingCat.of R)).Etale := j.unop.obj
  let z : (Scheme.pointSmallEtale (Spec.map (CommRingCat.ofHom φ))).fiber.obj Z := j.unop.val
  obtain ⟨V, v, a, hV, hav⟩ := geometricStalk_exists_affine_refinement
    (Spec.map (CommRingCat.ofHom φ)) Z z
  have : IsAffine V.left := hV
  change (Scheme.pointSmallEtale (Spec.map (CommRingCat.ofHom φ))).fiber.obj V at v
  change (Scheme.pointSmallEtale (Spec.map (CommRingCat.ofHom φ))).fiber.map a v = z at hav
  let a₀ : V.left ⟶ Z.left := a.left
  let vhom : V.left ⟶ Spec (CommRingCat.of R) := V.hom
  let zhom : Z.left ⟶ Spec (CommRingCat.of R) := Z.hom
  let b : V.left ⟶ (D.obj i).left := a₀ ≫ Z.left.toSpecΓ
  have hb : b ≫ (D.obj i).hom = V.hom := by
    change (a₀ ≫ Z.left.toSpecΓ) ≫ Spec.map
      ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ zhom.appTop) = vhom
    rw [Spec.map_comp, Category.assoc, ← Category.assoc Z.left.toSpecΓ,
      ← Scheme.toSpecΓ_naturality zhom, Category.assoc zhom, toSpecΓ_SpecMap_ΓSpecIso_inv,
      Category.comp_id]
    exact a.w
  let γV := geometricStalkGerm (Spec.map (CommRingCat.ofHom φ)) V v
  let γZ := geometricStalkGerm (Spec.map (CommRingCat.ofHom φ)) Z z
  have hγ : a.left.appTop ≫ γV = γZ := by
    have h := (Scheme.pointSmallEtale (Spec.map (CommRingCat.ofHom φ))).toPresheafFiber_w
      a v (etaleSections (Spec (CommRingCat.of R)))
    rw [hav] at h
    exact h
  have hbase : ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ vhom.appTop) ≫ γV =
      CommRingCat.ofHom (geometricStalkStructureMap φ) := by
    apply CommRingCat.hom_ext
    exact geometricStalkGerm_comp_structure φ V v
  let ρ : c.pt.left ⟶ V.left := Spec.map γV ≫ V.left.isoSpec.inv
  have hρ : ρ ≫ V.hom = c.pt.hom := by
    change (Spec.map γV ≫ V.left.isoSpec.inv) ≫ vhom = c.pt.hom
    rw [Category.assoc, ← Scheme.isoSpec_inv_naturality vhom,
      Scheme.isoSpec_Spec_inv, ← Spec.map_comp_assoc, ← Spec.map_comp]
    exact congrArg Spec.map hbase
  have hρb : ρ ≫ b = (c.π.app i).left := by
    change (Spec.map γV ≫ V.left.isoSpec.inv) ≫ (a.left ≫ Z.left.toSpecΓ) = Spec.map γZ
    rw [Scheme.toSpecΓ_naturality, Category.assoc, ← Category.assoc V.left.isoSpec.inv,
      Scheme.isoSpec_inv_toSpecΓ, Category.id_comp, ← Spec.map_comp, hγ]
  exact ⟨V, v, hV, ρ, hρ, b, rfl, hb, hρb⟩

/-- A covering affine open in an affine étale model over the strict-local
base spreads to a covering affine open over a pointed affine étale stage. -/
theorem geometricStalk_exists_affine_coverOpen_stage
    {R Ω : Type u} [CommRing R] [Field Ω] [IsSepClosed Ω]
    (φ : R →+* Ω) {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) [QuasiCompact f]
    {Y : Scheme.{u}} (g : Y ⟶ X) [Etale g] [IsAffine Y]
    (W : (pullback (Spec.map (CommRingCat.ofHom (geometricStalkStructureMap φ)))
      (g ≫ f)).Opens) (hW : IsAffineOpen W)
    [Surjective (W.ι ≫ AffineTransitionHom.modelMap
      (Spec.map (CommRingCat.ofHom (geometricStalkStructureMap φ))) f g)] :
    ∃ (V : (Spec (CommRingCat.of R)).Etale)
      (v : (Scheme.pointSmallEtale (Spec.map (CommRingCat.ofHom φ))).fiber.obj V)
      (_ : IsAffine V.left)
      (ρ : Spec (geometricStalk (Spec.map (CommRingCat.ofHom φ))) ⟶ V.left)
      (hρ : ρ ≫ V.hom = Spec.map (CommRingCat.ofHom (geometricStalkStructureMap φ)))
      (O : (pullback V.hom (g ≫ f)).Opens),
      ρ = Spec.map (geometricStalkGerm (Spec.map (CommRingCat.ofHom φ)) V v) ≫
          V.left.isoSpec.inv ∧
      IsAffineOpen O ∧ Surjective (O.ι ≫ AffineTransitionHom.modelMap V.hom f g) ∧
      ((Over.pullback (g ≫ f)).map
        (Over.homMk ρ hρ : Over.mk
          (Spec.map (CommRingCat.ofHom (geometricStalkStructureMap φ))) ⟶
            Over.mk V.hom)).left ⁻¹ᵁ O = W := by
  let D := geometricStalkSpecDiagram φ
  let c := geometricStalkSpecCone φ
  let F := geometricStalkSmallAlgebraDiagram φ
  have : ∀ {i j : (GeometricStalkAlgebraIndex φ)ᵒᵖ} (a : i ⟶ j),
      IsAffineHom (D.map a).left :=
    fun a => inferInstanceAs (IsAffineHom (Spec.map (F.map a.unop).right))
  have : ∀ i : (GeometricStalkAlgebraIndex φ)ᵒᵖ, CompactSpace (D.obj i).left :=
    fun i => inferInstanceAs (CompactSpace (Spec (F.obj i.unop).right))
  have : ∀ i : (GeometricStalkAlgebraIndex φ)ᵒᵖ,
      QuasiSeparatedSpace (D.obj i).left :=
    fun i => inferInstanceAs (QuasiSeparatedSpace (Spec (F.obj i.unop).right))
  have hWsurj : Surjective (W.ι ≫ AffineTransitionHom.modelMap c.pt.hom f g) :=
    inferInstanceAs (Surjective (W.ι ≫ AffineTransitionHom.modelMap
      (Spec.map (CommRingCat.ofHom (geometricStalkStructureMap φ))) f g))
  obtain ⟨i, O, hO, hrec, hsurj⟩ := AffineTransitionHom.exists_affineOpen_cover_stage
    D c (geometricStalkSpecConeIsLimit φ) f g W hW (hWsurj := hWsurj)
  obtain ⟨V, v, hV, ρ, hρ, b, hρgerm, hb, hρb⟩ :=
    geometricStalk_exists_affine_coefficientFactor φ i
  have : IsAffine V.left := hV
  have : IsAffine (D.obj i).left :=
    inferInstanceAs (IsAffine (Spec (F.obj i.unop).right))
  let B : Over (Spec (CommRingCat.of R)) := Over.mk V.hom
  let β : B ⟶ D.obj i := Over.homMk b hb
  let r : c.pt ⟶ B := Over.homMk ρ hρ
  have hrβ : r ≫ β = c.π.app i := Over.OverMorphism.ext hρb
  have : IsAffineHom β.left := inferInstanceAs (IsAffineHom b)
  have : IsAffineHom ((Over.pullback (g ≫ f)).map β).left :=
    MorphismProperty.overPullbackMap
      (P := show MorphismProperty Scheme.{u} from @IsAffineHom)
      (g ≫ f) β inferInstance
  let OV : (pullback V.hom (g ≫ f)).Opens :=
    ((Over.pullback (g ≫ f)).map β).left ⁻¹ᵁ O
  have hCover : Surjective (OV.ι ≫ AffineTransitionHom.modelMap V.hom f g) := by
    refine ⟨Set.range_eq_univ.mp ?_⟩
    have : Surjective (O.ι ≫ AffineTransitionHom.modelMap (D.obj i).hom f g) := hsurj
    exact (AffineTransitionHom.modelMap_range_preimage β f g O).trans
      ((congrArg (fun T => ((Over.pullback f).map β).left ⁻¹' T)
        (Set.range_eq_univ.mpr
          (O.ι ≫ AffineTransitionHom.modelMap (D.obj i).hom f g).surjective)).trans
        (Set.preimage_univ))
  have hRecover : ((Over.pullback (g ≫ f)).map r).left ⁻¹ᵁ OV = W := by
    change ((Over.pullback (g ≫ f)).map r).left ⁻¹ᵁ
      (((Over.pullback (g ≫ f)).map β).left ⁻¹ᵁ O) = W
    rw [← Scheme.Hom.comp_preimage]
    have hcomp : ((Over.pullback (g ≫ f)).map r).left ≫
        ((Over.pullback (g ≫ f)).map β).left =
          ((Over.pullback (g ≫ f)).map (c.π.app i)).left := by
      exact (congrArg (fun t => t.left) ((Over.pullback (g ≫ f)).map_comp r β)).symm.trans
        (congrArg (fun t => ((Over.pullback (g ≫ f)).map t).left) hrβ)
    rw [hcomp]
    exact hrec
  exact ⟨V, v, hV, ρ, hρ, OV, hρgerm, hO.preimage _, hCover, hRecover⟩

end EtaleCohomology
