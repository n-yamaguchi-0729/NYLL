/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.Purity.FiniteBoundaryExtension
public import Nyll.EtaleFundamentalGroups.Purity.Local.BoundaryExtensionDepth
public import Mathlib.AlgebraicGeometry.Stalk
public import Nyll.SchemeTheory.RingTheory.Localization.LocalAlgebra

/-!
# Boundary depth of the global canonical finite extension

An original affine algebra chart is identified with the global sections
of the actual pulled-back cover. The comparison is the open immersion's
section map, and its coefficient triangle is the original cartesian
square on sections. Affine boundary depth therefore transfers to every
stalk of the original relative spectrum above the boundary.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Limits Opposite TopologicalSpace
open AlgebraicCurves.Foundations.Algebra.Proofs.Module_depth_quotSMulTop_succ_eq
open Ws14Port.IsLocalRing.IsCohenMacaulayOfDim

namespace EtaleFundamentalGroups.FiniteBoundaryExtension

open AlgebraicGeometry Scheme.Modules

variable (X : Scheme.{u}) [IsLocallyNoetherian X]
  (U : X.Opens) {V : Scheme.{u}} (π : V ⟶ U.toScheme) [IsFinite π] [Etale π]
  (hdepth : ∀ x : X, x ∉ U →
    (2 : ℕ∞) ≤ Module.depth (X.presheaf.stalk x) (X.presheaf.stalk x))

include hdepth in
private theorem two_le_depth_affineAlgebra_stalk (W : X.Opens) (hW : IsAffineOpen W)
    (z : Spec Γ(V, (π ≫ U.ι) ⁻¹ᵁ W))
    (hz : hW.fromSpec ((Spec.map ((π ≫ U.ι).app W)) z) ∉ U) :
    (2 : ℕ∞) ≤ Module.depth
      ((Spec Γ(V, (π ≫ U.ι) ⁻¹ᵁ W)).presheaf.stalk z)
      ((Spec Γ(V, (π ≫ U.ι) ⁻¹ᵁ W)).presheaf.stalk z) := by
  let R : CommRingCat.{u} := Γ(X, W)
  have : IsNoetherianRing R := IsLocallyNoetherian.component_noetherian ⟨W, hW⟩
  let j : Spec R ⟶ X := hW.fromSpec
  have : IsOpenImmersion j := hW.isOpenImmersion_fromSpec
  let T : (Spec R).Opens := j ⁻¹ᵁ U
  let q := pullback.snd π (j ∣_ U)
  let a := pullback.fst π (j ∣_ U)
  let g := π ≫ U.ι
  let b := q ≫ T.ι
  have H : IsPullback a b g j :=
    (IsPullback.of_hasPullback π (j ∣_ U)).paste_vert
      (isPullback_morphismRestrict j U)
  have : IsOpenImmersion a := inferInstance
  have ha : a.opensRange = g ⁻¹ᵁ W := by
    have h := IsOpenImmersion.image_preimage_eq_preimage_image_of_isPullback H.flip ⊤
    simpa only [Scheme.Hom.preimage_top, Scheme.Hom.image_top_eq_opensRange,
      j, hW.opensRange_fromSpec] using h
  have haTop : a ⁻¹ᵁ (g ⁻¹ᵁ W) = ⊤ := by
    rw [← ha, Scheme.Hom.preimage_opensRange]
  let hla : ⊤ ≤ a ⁻¹ᵁ (g ⁻¹ᵁ W) := haTop.ge
  let hlj : ⊤ ≤ j ⁻¹ᵁ W := hW.fromSpec_preimage_self.ge
  let A : CommRingCat.{u} := Γ(V, g ⁻¹ᵁ W)
  let B : CommRingCat.{u} := Γ(pullback π (j ∣_ U), ⊤)
  let d : R ⟶ A := g.app W
  let k : A ⟶ B := a.appLE (g ⁻¹ᵁ W) ⊤ hla
  have : IsIso (a.app (g ⁻¹ᵁ W)) := a.isIso_app _ ha.symm.le
  have : IsIso (homOfLE hla) := by
    have he : homOfLE hla = eqToHom haTop.symm := Subsingleton.elim _ _
    exact he.symm ▸ inferInstanceAs (IsIso (eqToHom haTop.symm))
  have : IsIso k := by
    change IsIso (a.app (g ⁻¹ᵁ W) ≫
      (pullback π (j ∣_ U)).presheaf.map (homOfLE hla).op)
    infer_instance
  let e : A ≅ B := asIso k
  have hj : j.appLE W ⊤ hlj = (Scheme.ΓSpecIso R).inv := by
    change hW.fromSpec.app W ≫ (Spec R).presheaf.map (homOfLE hlj).op = _
    rw [hW.fromSpec_app_self, Category.assoc, ← Functor.map_comp]
    have he : (eqToHom hW.fromSpec_preimage_self).op ≫ (homOfLE hlj).op =
        𝟙 (op (⊤ : (Spec R).Opens)) := Subsingleton.elim _ _
    rw [he, CategoryTheory.Functor.map_id, Category.comp_id]
  let c : R ⟶ B := (Scheme.ΓSpecIso R).inv ≫ b.appTop
  have hc : d ≫ e.hom = c := by
    let h₁ : ⊤ ≤ (a ≫ g) ⁻¹ᵁ W := hla
    let h₂ : ⊤ ≤ (b ≫ j) ⁻¹ᵁ W :=
      (show ⊤ ≤ b ⁻¹ᵁ ⊤ from le_rfl).trans (b.preimage_mono hlj)
    have he :
        (⟨a ≫ g, h₁⟩ : { f : pullback π (j ∣_ U) ⟶ X // ⊤ ≤ f ⁻¹ᵁ W }) =
          ⟨b ≫ j, h₂⟩ := Subtype.ext H.w
    have he' := congrArg
      (fun f : { f : pullback π (j ∣_ U) ⟶ X // ⊤ ≤ f ⁻¹ᵁ W } =>
        f.1.appLE W ⊤ f.2) he
    calc
      d ≫ e.hom = g.appLE W (g ⁻¹ᵁ W) le_rfl ≫
          a.appLE (g ⁻¹ᵁ W) ⊤ hla :=
        congrArg (fun l : R ⟶ A => l ≫ k) g.app_eq_appLE
      _ = (a ≫ g).appLE W ⊤ h₁ :=
        Scheme.Hom.appLE_comp_appLE a g W (g ⁻¹ᵁ W) ⊤ le_rfl hla
      _ = (b ≫ j).appLE W ⊤ h₂ := he'
      _ = j.appLE W ⊤ hlj ≫ b.appLE ⊤ ⊤ le_rfl :=
        (Scheme.Hom.appLE_comp_appLE b j W ⊤ ⊤ hlj le_rfl).symm
      _ = c := by
        rw [hj]
        exact congrArg (fun k : Γ(Spec R, ⊤) ⟶ B => (Scheme.ΓSpecIso R).inv ≫ k)
          (b.app_eq_appLE (U := ⊤)).symm
  have hT : ∀ p : Spec R, p ∉ T →
      (2 : ℕ∞) ≤ Module.depth ((Spec R).presheaf.stalk p)
        ((Spec R).presheaf.stalk p) := by
    intro p hp
    exact (hdepth (j p) hp).trans
      (Module.depth_le_depth_of_ringEquiv
        (asIso (j.stalkMap p)).commRingCatIsoToRingEquiv)
  let zB : Spec B := Spec.map e.inv z
  have hez : Spec.map e.hom zB = z := by
    change (Spec.map e.inv ≫ Spec.map e.hom) z = z
    rw [← Spec.map_comp, e.hom_inv_id, Spec.map_id]
    rfl
  have hzB : Spec.map c zB ∉ T := by
    change j (Spec.map c zB) ∉ U
    have hcSpec : Spec.map c = Spec.map e.hom ≫ Spec.map d :=
      (congrArg (fun f : R ⟶ B => Spec.map f) hc.symm).trans (Spec.map_comp _ _)
    rw [hcSpec, Scheme.Hom.comp_apply, hez]
    exact hz
  have hB := AffineReflexiveExtension.two_le_depth_sectionAlgebra_atPrime
    R T q hT zB hzB
  have hBstalk : (2 : ℕ∞) ≤ Module.depth
      ((Spec B).presheaf.stalk zB) ((Spec B).presheaf.stalk zB) :=
    hB.trans (Module.depth_le_depth_of_ringEquiv
      (Spec.stalkIso B zB).symm.commRingCatIsoToRingEquiv)
  exact hBstalk.trans (Module.depth_le_depth_of_ringEquiv
    (asIso ((Spec.map e.inv).stalkMap z)).commRingCatIsoToRingEquiv)

include hdepth in
/-- Every actual local ring of the canonical finite extension over the
missing boundary has depth at least two. -/
theorem two_le_depth_relativeSpec_boundary :
    let : (Scheme.RelativeSpec.underlyingModule
      (Scheme.DirectImageAlgebra.structureMap (π ≫ U.ι))).IsQuasicoherent :=
        isQuasicoherent_underlyingModule X U π
    ∀ z : Scheme.RelativeSpec.scheme (Scheme.DirectImageAlgebra.structureMap (π ≫ U.ι)),
      Scheme.RelativeSpec.toBase (Scheme.DirectImageAlgebra.structureMap (π ≫ U.ι)) z ∉ U →
      (2 : ℕ∞) ≤ Module.depth
        ((Scheme.RelativeSpec.scheme
          (Scheme.DirectImageAlgebra.structureMap (π ≫ U.ι))).presheaf.stalk z)
        ((Scheme.RelativeSpec.scheme
          (Scheme.DirectImageAlgebra.structureMap (π ≫ U.ι))).presheaf.stalk z) := by
  intro inst z hz
  let α := Scheme.DirectImageAlgebra.structureMap (π ≫ U.ι)
  let C := Scheme.RelativeSpec.openCover α
  obtain ⟨W, t, rfl⟩ := C.exists_eq z
  have : IsOpenImmersion (C.f W) := C.map_prop W
  have ht : W.2.fromSpec (Spec.map ((π ≫ U.ι).app W.1) t) ∉ U := by
    intro h
    apply hz
    have he := congrArg (fun k => k t) (Scheme.RelativeSpec.openCover_toBase α W)
    exact he.symm ▸ h
  have hlocal : (2 : ℕ∞) ≤ Module.depth ((C.X W).presheaf.stalk t)
      ((C.X W).presheaf.stalk t) :=
    two_le_depth_affineAlgebra_stalk X U π hdepth W.1 W.2 t ht
  exact hlocal.trans (Module.depth_le_depth_of_ringEquiv
    (asIso ((C.f W).stalkMap t)).symm.commRingCatIsoToRingEquiv)

end EtaleFundamentalGroups.FiniteBoundaryExtension
