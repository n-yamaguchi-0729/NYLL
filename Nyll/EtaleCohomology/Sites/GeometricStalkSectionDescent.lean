/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalkAlgebraColimit
import Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalkFlat
import Nyll.EtaleCohomology.Sites.GeometricStalkSchemeLimit
import Nyll.SchemeTheory.Descent.AffineTransitionHom
import Mathlib.AlgebraicGeometry.AffineTransitionLimit
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
import Mathlib.CategoryTheory.Comma.Over.Pullback
import Mathlib.CategoryTheory.Limits.Opposites

/-!
# Spreading scheme sections from the actual geometric stalk

For a qcqs scheme over an affine base, a morphism from its actual
strict-local base change to a locally finitely presented relative target
descends to a pointed affine étale neighborhood. The recovered morphism
is the original one, along the literal germ map and native pullbacks.

Only the relative target needs finite presentation. The original scheme
may be proper without being finitely presented over the base. Applying
`Spec` to the existing algebra colimit gives the actual inverse limit used
in the geometric finite-data step of Stacks Project, Theorem 59.53.1.
This file does not assume a continuity theorem for arbitrary étale sheaves.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open EtaleFundamentalGroups.StrictHenselian

namespace EtaleCohomology

universe u

/-- A section over the actual strict-local base spreads to a pointed affine
étale neighborhood, with exact recovery along the actual germ map. -/
theorem geometricStalk_exists_affine_section_stage
    {R Ω : Type u} [CommRing R] [Field Ω] [IsSepClosed Ω]
    (φ : R →+* Ω) {X Y : Scheme.{u}}
    (f : X ⟶ Spec (.of R)) [QuasiCompact f] [QuasiSeparated f]
    (g : Y ⟶ X) [LocallyOfFinitePresentation g]
    (s : pullback (Spec.map (CommRingCat.ofHom (geometricStalkStructureMap φ))) f ⟶ Y)
    (hs : s ≫ g =
      pullback.snd (Spec.map (CommRingCat.ofHom (geometricStalkStructureMap φ))) f) :
    ∃ (V : (Spec (.of R)).Etale)
      (v : (Scheme.pointSmallEtale (Spec.map (CommRingCat.ofHom φ))).fiber.obj V)
      (_ : IsAffine V.left)
      (b : pullback V.hom f ⟶ Y)
      (m : pullback (Spec.map (CommRingCat.ofHom (geometricStalkStructureMap φ))) f ⟶
        pullback V.hom f),
      b ≫ g = pullback.snd V.hom f ∧ m ≫ b = s ∧
      m ≫ pullback.snd V.hom f =
        pullback.snd (Spec.map (CommRingCat.ofHom (geometricStalkStructureMap φ))) f ∧
      m ≫ pullback.fst V.hom f =
        pullback.fst (Spec.map (CommRingCat.ofHom (geometricStalkStructureMap φ))) f ≫
          Spec.map (geometricStalkGerm (Spec.map (CommRingCat.ofHom φ)) V v) ≫
            V.left.isoSpec.inv := by
  let F := geometricStalkSmallAlgebraDiagram φ
  let D₀ := geometricStalkSpecDiagram φ
  let c₀ : Cone D₀ := geometricStalkSpecCone φ
  have hc₀ : IsLimit c₀ := geometricStalkSpecConeIsLimit φ
  let D := D₀ ⋙ Over.pullback f
  let c : Cone D := (Over.pullback f).mapCone c₀
  have hc : IsLimit c := isLimitOfPreserves (Over.pullback f) hc₀
  let D' := D ⋙ Over.forget X
  let c' : Cone D' := (Over.forget X).mapCone c
  have hc' : IsLimit c' := isLimitOfPreserves (Over.forget X) hc
  let p : D' ⟶ (Functor.const _).obj X := ((Over.forgetCocone X).whisker D).ι
  have hcompat : c'.π ≫ p = (Functor.const _).map (s ≫ g) := by
    apply NatTrans.ext
    funext i
    exact (Over.w (c.π.app i)).trans hs.symm
  have : ∀ {i j} (a : i ⟶ j), IsAffineHom (D₀.map a).left :=
    fun a => inferInstanceAs (IsAffineHom (Spec.map (F.map a.unop).right))
  have : ∀ i, CompactSpace (D₀.obj i).left :=
    fun i => inferInstanceAs (CompactSpace (Spec (F.obj i.unop).right))
  have : ∀ i, QuasiSeparatedSpace (D₀.obj i).left :=
    fun i => inferInstanceAs (QuasiSeparatedSpace (Spec (F.obj i.unop).right))
  have : ∀ {i j} (a : i ⟶ j), IsAffineHom (D'.map a) :=
    fun a => AffineTransitionHom.diagram_map_isAffineHom D₀ f a
  have : ∀ i, CompactSpace (D'.obj i) :=
    AffineTransitionHom.diagram_obj_compactSpace D₀ f
  have : ∀ i, QuasiSeparatedSpace (D'.obj i) :=
    AffineTransitionHom.diagram_obj_quasiSeparatedSpace D₀ f
  obtain ⟨k, bk, hrec, hbk⟩ :=
    Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation D' p g c' hc' s hcompat
  let j := (FinallySmall.fromFilteredFinalModel
    (Scheme.pointSmallEtale (Spec.map (CommRingCat.ofHom φ))).fiber.Elementsᵒᵖ).obj k.unop
  let W : (Spec (.of R)).Etale := j.unop.obj
  let w : (Scheme.pointSmallEtale (Spec.map (CommRingCat.ofHom φ))).fiber.obj W := j.unop.val
  let β : CommRingCat.of R ⟶ Γ(W.left, ⊤) := (Scheme.ΓSpecIso (.of R)).inv ≫ W.hom.appTop
  let qW : Spec Γ(W.left, ⊤) ⟶ Spec (.of R) := Spec.map β
  let bW : pullback qW f ⟶ Y := bk
  have hbW : bW ≫ g = pullback.snd qW f := hbk
  let qH : Spec (geometricStalk (Spec.map (CommRingCat.ofHom φ))) ⟶ Spec (.of R) :=
    Spec.map (CommRingCat.ofHom (geometricStalkStructureMap φ))
  let ck : pullback qH f ⟶ pullback qW f := c'.π.app k
  have hck : ck ≫ bW = s := hrec
  have hck_snd : ck ≫ pullback.snd qW f = pullback.snd qH f :=
    Over.w (c.π.app k)
  have hck_fst : ck ≫ pullback.fst qW f = pullback.fst qH f ≫
      Spec.map (geometricStalkGerm (Spec.map (CommRingCat.ofHom φ)) W w) :=
    pullback.lift_fst _ _ _
  obtain ⟨V, v, a, hV, hav⟩ :=
    geometricStalk_exists_affine_refinement (Spec.map (CommRingCat.ofHom φ)) W w
  have : IsAffine V.left := hV
  let a₀ : V.left ⟶ W.left := a.left
  let vhom : V.left ⟶ Spec (.of R) := V.hom
  let whom : W.left ⟶ Spec (.of R) := W.hom
  have ha₀ : a₀ ≫ whom = vhom := a.w
  let jV : V.left ⟶ Spec Γ(W.left, ⊤) := a₀ ≫ W.left.toSpecΓ
  have hjV : jV ≫ qW = vhom := by
    change (a₀ ≫ W.left.toSpecΓ) ≫ Spec.map
      ((Scheme.ΓSpecIso (.of R)).inv ≫ whom.appTop) = vhom
    rw [Spec.map_comp, Category.assoc, ← Category.assoc W.left.toSpecΓ,
      ← Scheme.toSpecΓ_naturality, Category.assoc whom, toSpecΓ_SpecMap_ΓSpecIso_inv,
      Category.comp_id]
    exact ha₀
  let n : pullback vhom f ⟶ pullback qW f :=
    pullback.lift (pullback.fst vhom f ≫ jV) (pullback.snd vhom f) (by
      rw [Category.assoc, hjV, pullback.condition])
  let γV := geometricStalkGerm (Spec.map (CommRingCat.ofHom φ)) V v
  let γW := geometricStalkGerm (Spec.map (CommRingCat.ofHom φ)) W w
  have hγ : a₀.appTop ≫ γV = γW := by
    have h := (Scheme.pointSmallEtale (Spec.map (CommRingCat.ofHom φ))).toPresheafFiber_w
      a v (etaleSections (Spec (.of R)))
    change (Scheme.pointSmallEtale (Spec.map (CommRingCat.ofHom φ))).fiber.map a v = w at hav
    rw [hav] at h
    exact h
  have hbase : ((Scheme.ΓSpecIso (.of R)).inv ≫ vhom.appTop) ≫ γV =
      CommRingCat.ofHom (geometricStalkStructureMap φ) := by
    apply CommRingCat.hom_ext
    exact geometricStalkGerm_comp_structure φ V v
  let ρ : Spec (geometricStalk (Spec.map (CommRingCat.ofHom φ))) ⟶ V.left :=
    Spec.map γV ≫ V.left.isoSpec.inv
  have hρ : ρ ≫ vhom = qH := by
    change (Spec.map γV ≫ V.left.isoSpec.inv) ≫ vhom = qH
    rw [Category.assoc, ← Scheme.isoSpec_inv_naturality,
      Scheme.isoSpec_Spec_inv, ← Spec.map_comp_assoc, ← Spec.map_comp]
    exact congrArg Spec.map hbase
  have hρj : ρ ≫ jV = Spec.map γW := by
    change (Spec.map γV ≫ V.left.isoSpec.inv) ≫ (a₀ ≫ W.left.toSpecΓ) = Spec.map γW
    rw [Scheme.toSpecΓ_naturality, Category.assoc, ← Category.assoc V.left.isoSpec.inv,
      Scheme.isoSpec_inv_toSpecΓ, Category.id_comp, ← Spec.map_comp, hγ]
  let m : pullback qH f ⟶ pullback vhom f :=
    pullback.lift (pullback.fst qH f ≫ ρ) (pullback.snd qH f) (by
      rw [Category.assoc, hρ, pullback.condition])
  have hmn : m ≫ n = ck := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, ← Category.assoc,
        pullback.lift_fst, Category.assoc, hρj, hck_fst]
    · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, hck_snd]
  refine ⟨V, v, hV, n ≫ bW, m, ?_, ?_, pullback.lift_snd _ _ _, ?_⟩
  · rw [Category.assoc, hbW]
    exact pullback.lift_snd _ _ _
  · exact (Category.assoc m n bW).symm.trans
      ((congrArg (fun h => h ≫ bW) hmn).trans hck)
  · exact pullback.lift_fst _ _ _

end EtaleCohomology
