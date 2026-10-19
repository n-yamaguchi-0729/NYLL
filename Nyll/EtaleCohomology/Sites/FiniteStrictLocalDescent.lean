/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Etale.FiniteStrictLocalSection
import Nyll.SchemeTheory.Affine.SpecBaseChangeSectionsMap
import Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalkAlgebraColimit
import Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalkFlat
import Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalkHenselian
import Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalkResidue
import Mathlib.Algebra.Category.Ring.FinitePresentation
import Mathlib.Algebra.Category.Ring.Under.Basic
import Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
import Mathlib.RingTheory.RingHom.Etale
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Spreading sections of covers of finite schemes

An affine surjective étale cover of a finite affine scheme splits after
pullback to an actual pointed affine étale neighborhood of any geometric
point of the base. First split the cover over the constructed geometric
stalk, which is strictly Henselian. Then descend the resulting algebra map
using finite presentation over the finite algebra, rather than over the
original base. In particular, the finite algebra itself need not be
finitely presented over the base.

This supplies the finite-data descent step in the finite direct-image
argument of Stacks Project, Section 59.55.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open EtaleFundamentalGroups.StrictHenselian
open scoped TensorProduct

namespace EtaleCohomology

universe u

private theorem exists_tensor_lift_over_strictlyHenselian
    {A B C H : Type u} [CommRing A] [CommRing B] [CommRing C]
    [CommRing H] [Algebra A B] [Algebra B C] [Algebra A H]
    [Module.Finite A B] [Algebra.Etale B C]
    [HenselianLocalRing H] [IsSepClosed (IsLocalRing.ResidueField H)]
    [Surjective (Spec.map (CommRingCat.ofHom (algebraMap B C)))] :
    Nonempty (C →ₐ[B] (B ⊗[A] H)) := by
  let D : Type u := H ⊗[A] B
  let p : Spec (.of C) ⟶ Spec (.of B) :=
    Spec.map (CommRingCat.ofHom (algebraMap B C))
  have : Etale p :=
    (HasRingHomProperty.Spec_iff (P := @Etale)).mpr
      (RingHom.etale_algebraMap.mpr inferInstance)
  let q : Spec (.of D) ⟶ Spec (.of B) :=
    Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight : B →ₐ[A] D).toRingHom)
  obtain ⟨σ, hσ⟩ := Etale.exists_section_of_finite_over_strictlyHenselian
    H D (pullback.snd p q)
  have hlift : (σ ≫ pullback.fst p q) ≫ p = q := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, hσ, Category.id_comp]
  obtain ⟨τ, hτ⟩ := Spec.map_surjective (σ ≫ pullback.fst p q)
  have hcomp : CommRingCat.ofHom (algebraMap B C) ≫ τ =
      CommRingCat.ofHom (Algebra.TensorProduct.includeRight : B →ₐ[A] D).toRingHom := by
    apply Spec.map_injective
    rw [Spec.map_comp, hτ]
    exact hlift
  refine ⟨{ __ := (Algebra.TensorProduct.comm A H B).toRingHom.comp τ.hom
            commutes' := ?_ }⟩
  intro b
  change (Algebra.TensorProduct.comm A H B) (τ.hom (algebraMap B C b)) =
    algebraMap B (B ⊗[A] H) b
  have hb : τ.hom (algebraMap B C b) =
      (Algebra.TensorProduct.includeRight : B →ₐ[A] D) b :=
    congrArg (fun f : CommRingCat.of B ⟶ CommRingCat.of D => f.hom b) hcomp
  rw [hb]
  exact Algebra.TensorProduct.comm_tmul A (1 : H) b

/-- An affine surjective étale cover of a finite affine scheme admits an
actual lift after base change to a pointed affine étale neighborhood of any
geometric point of the base. The finite algebra has no finite-presentation
hypothesis. The displayed equality is the literal equation over its spectrum. -/
theorem exists_affine_pointed_etale_lift_of_finite
    {A B C Ω : Type u} [CommRing A] [CommRing B] [CommRing C]
    [Field Ω] [IsSepClosed Ω] [Algebra A B] [Algebra B C]
    [Module.Finite A B] [Algebra.Etale B C]
    [Surjective (Spec.map (CommRingCat.ofHom (algebraMap B C)))]
    (φ : A →+* Ω) :
    ∃ (V : (Spec (.of A)).Etale)
      (_ : (Scheme.pointSmallEtale (Spec.map (CommRingCat.ofHom φ))).fiber.obj V),
      IsAffine V.left ∧
      let _ : Algebra A Γ(V.left, ⊤) :=
        (((Scheme.ΓSpecIso (.of A)).inv ≫ V.hom.appTop).hom).toAlgebra
      ∃ s : Spec (.of (B ⊗[A] Γ(V.left, ⊤))) ⟶ Spec (.of C),
        s ≫ Spec.map (CommRingCat.ofHom (algebraMap B C)) =
          Spec.map (CommRingCat.ofHom (algebraMap B (B ⊗[A] Γ(V.left, ⊤)))) := by
  let H : Type u := geometricStalk (Spec.map (CommRingCat.ofHom φ))
  let : Algebra A H := (geometricStalkStructureMap φ).toAlgebra
  obtain ⟨g⟩ := exists_tensor_lift_over_strictlyHenselian (A := A) (B := B)
    (C := C) (H := H)
  let F := geometricStalkSmallAlgebraDiagram φ
  let c := geometricStalkSmallAlgebraCocone φ
  let T : Under (CommRingCat.of A) ⥤ Under (CommRingCat.of B) :=
    CommRingCat.tensorProd (CommRingCat.of A) (CommRingCat.of B)
  let cB : Cocone (F ⋙ T) := T.mapCocone c
  let : PreservesColimit F T :=
    preservesColimit_of_natIso F
      (CommRingCat.tensorProdIsoPushout (CommRingCat.of A) (CommRingCat.of B)).symm
  have hcB : IsColimit cB :=
    isColimitOfPreserves T (geometricStalkSmallAlgebraCoconeIsColimit φ)
  let C₀ : Under (CommRingCat.of B) := CommRingCat.mkUnder (CommRingCat.of B) C
  have hCfp : C₀.hom.hom.FinitePresentation := by
    change (algebraMap B C).FinitePresentation
    exact RingHom.finitePresentation_algebraMap.mpr inferInstance
  let : IsFinitelyPresentable.{u} C₀ :=
    CommRingCat.isFinitelyPresentable_under (CommRingCat.of B) C₀ hCfp
  obtain ⟨k, gk, _⟩ := IsFinitelyPresentable.exists_hom_of_isColimit hcB g.toUnder
  let j := (FinallySmall.fromFilteredFinalModel
    (Scheme.pointSmallEtale (Spec.map (CommRingCat.ofHom φ))).fiber.Elementsᵒᵖ).obj k
  let W : (Spec (.of A)).Etale := j.unop.obj
  let t : (Scheme.pointSmallEtale (Spec.map (CommRingCat.ofHom φ))).fiber.obj W := j.unop.val
  let : Algebra A Γ(W.left, ⊤) :=
    (((Scheme.ΓSpecIso (.of A)).inv ≫ W.hom.appTop).hom).toAlgebra
  let gW : C →ₐ[B] (B ⊗[A] Γ(W.left, ⊤)) :=
    { __ := gk.right.hom
      commutes' := fun b => congrArg
        (fun h : CommRingCat.of B ⟶ CommRingCat.of (B ⊗[A] Γ(W.left, ⊤)) => h.hom b)
        (Under.w gk) }
  obtain ⟨V, v, f, hV, _⟩ :=
    geometricStalk_exists_affine_refinement (Spec.map (CommRingCat.ofHom φ)) W t
  refine ⟨V, v, hV, ?_⟩
  intro av
  have hbase : f.left.appTop.hom.comp
      (((Scheme.ΓSpecIso (.of A)).inv ≫ W.hom.appTop).hom) =
      (((Scheme.ΓSpecIso (.of A)).inv ≫ V.hom.appTop).hom) := by
    change ((((Scheme.ΓSpecIso (.of A)).inv ≫ W.hom.appTop) ≫ f.left.appTop).hom) = _
    apply congrArg CommRingCat.Hom.hom
    rw [Category.assoc, ← Scheme.Hom.comp_appTop]
    have hf : f.left ≫ (show W.left ⟶ Spec (.of A) from W.hom) =
        (show V.left ⟶ Spec (.of A) from V.hom) := f.w
    exact congrArg (fun h => (Scheme.ΓSpecIso (.of A)).inv ≫ h.appTop) hf
  let ρ : Γ(W.left, ⊤) →ₐ[A] Γ(V.left, ⊤) :=
    { __ := f.left.appTop.hom
      commutes' := fun a => RingHom.congr_fun hbase a }
  let gV : C →ₐ[B] (B ⊗[A] Γ(V.left, ⊤)) :=
    (Algebra.TensorProduct.map (AlgHom.id B B) ρ).comp gW
  refine ⟨Spec.map (CommRingCat.ofHom gV.toRingHom), ?_⟩
  rw [← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  exact gV.comp_algebraMap

private theorem exists_affine_pointed_etale_pullback_lift_of_finite
    {A B C Ω : Type u} [CommRing A] [CommRing B] [CommRing C]
    [Field Ω] [IsSepClosed Ω] [Algebra A B] [Algebra B C]
    [Module.Finite A B] [Algebra.Etale B C]
    [Surjective (Spec.map (CommRingCat.ofHom (algebraMap B C)))]
    (φ : A →+* Ω) :
    ∃ (V : (Spec (.of A)).Etale)
      (_ : (Scheme.pointSmallEtale (Spec.map (CommRingCat.ofHom φ))).fiber.obj V),
      IsAffine V.left ∧
      ∃ s : pullback V.hom (Spec.map (CommRingCat.ofHom (algebraMap A B))) ⟶ Spec (.of C),
        s ≫ Spec.map (CommRingCat.ofHom (algebraMap B C)) =
          pullback.snd V.hom (Spec.map (CommRingCat.ofHom (algebraMap A B))) := by
  obtain ⟨V, v, hV, h⟩ := exists_affine_pointed_etale_lift_of_finite (B := B) (C := C) φ
  let : Algebra A Γ(V.left, ⊤) :=
    (((Scheme.ΓSpecIso (.of A)).inv ≫ V.hom.appTop).hom).toAlgebra
  obtain ⟨s, hs⟩ := h
  let q := Spec.map (CommRingCat.ofHom (algebraMap A B))
  let Q := pullback V.hom q
  let p : Q ⟶ Spec (.of B) := pullback.snd V.hom q
  let l : Q ⟶ Spec (.of (B ⊗[A] Γ(V.left, ⊤))) :=
    Q.toSpecΓ ≫ Spec.map (specPullbackSectionsTensorMap (A := B) V.hom)
  have htensor : CommRingCat.ofHom (algebraMap B (B ⊗[A] Γ(V.left, ⊤))) ≫
      specPullbackSectionsTensorMap (A := B) V.hom =
      (Scheme.ΓSpecIso (.of B)).inv ≫ p.appTop :=
    specPullbackSectionsTensorMap_left (A := B) V.hom
  have hl : l ≫ Spec.map (CommRingCat.ofHom (algebraMap B (B ⊗[A] Γ(V.left, ⊤)))) = p := by
    dsimp only [l]
    rw [Category.assoc, ← Spec.map_comp, htensor, Spec.map_comp, ← Category.assoc,
      ← Scheme.toSpecΓ_naturality, Category.assoc, toSpecΓ_SpecMap_ΓSpecIso_inv,
      Category.comp_id]
  refine ⟨V, v, hV, l ≫ s, ?_⟩
  rw [Category.assoc, hs]
  exact hl

/-- A surjective affine étale cover of a finite scheme over an affine base
splits after pullback to an actual pointed affine étale neighborhood of any
geometric point of the base. The section is a morphism from the literal
scheme pullback, with its composite equal to the literal second projection. -/
theorem exists_affine_pointed_etale_cover_lift_of_isFinite
    {X Y W : Scheme.{u}} [IsAffine X] [IsAffine W]
    (q : Y ⟶ X) [IsFinite q] (p : W ⟶ Y) [Etale p] [Surjective p]
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (t : Spec (.of Ω) ⟶ X) :
    ∃ (V : X.Etale) (_ : (Scheme.pointSmallEtale t).fiber.obj V),
      IsAffine V.left ∧ ∃ s : pullback V.hom q ⟶ W,
        s ≫ p = pullback.snd V.hom q := by
  have : IsAffine Y := isAffine_of_isAffineHom q
  let A : CommRingCat.{u} := Γ(X, ⊤)
  let B : CommRingCat.{u} := Γ(Y, ⊤)
  let C : CommRingCat.{u} := Γ(W, ⊤)
  let : Algebra A B := q.appTop.hom.toAlgebra
  let : Algebra B C := p.appTop.hom.toAlgebra
  have : Module.Finite A B := q.finite_appTop
  have : Algebra.Etale B C :=
    (HasRingHomProperty.iff_of_isAffine (P := @Etale) (f := p)).mp inferInstance
  let q₀ : Spec B ⟶ Spec A := Spec.map q.appTop
  let p₀ : Spec C ⟶ Spec B := Spec.map p.appTop
  have hp₀ : p₀ = W.isoSpec.inv ≫ p ≫ Y.isoSpec.hom := by
    rw [← Scheme.isoSpec_hom_naturality, Iso.inv_hom_id_assoc]
  have : Surjective (Spec.map (CommRingCat.ofHom (algebraMap B C))) := by
    change Surjective p₀
    rw [hp₀]
    infer_instance
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (t ≫ X.isoSpec.hom)
  obtain ⟨V₀, v₀, hV, s₀, hs₀⟩ :=
    exists_affine_pointed_etale_pullback_lift_of_finite (B := B) (C := C) φ.hom
  change (Over.mk (Spec.map φ) ⟶ Over.mk V₀.hom) at v₀
  let U : (Spec A).Etale := V₀
  let u : U.left ⟶ Spec A := U.hom
  let w : Spec (.of Ω) ⟶ U.left := v₀.left
  have hw : w ≫ u = Spec.map φ := v₀.w
  let s : pullback u q₀ ⟶ Spec C := s₀
  have hs : s ≫ p₀ = pullback.snd u q₀ := hs₀
  let f : U.left ⟶ X := u ≫ X.isoSpec.inv
  let V : X.Etale := Scheme.Etale.mk f
  let v : (Scheme.pointSmallEtale t).fiber.obj V := Over.homMk w (by
    change w ≫ f = t
    calc
      w ≫ f = (w ≫ u) ≫ X.isoSpec.inv := (Category.assoc _ _ _).symm
      _ = Spec.map φ ≫ X.isoSpec.inv := congrArg (fun h => h ≫ X.isoSpec.inv) hw
      _ = (t ≫ X.isoSpec.hom) ≫ X.isoSpec.inv :=
        congrArg (fun h => h ≫ X.isoSpec.inv) hφ
      _ = t := by rw [Category.assoc, Iso.hom_inv_id, Category.comp_id])
  let m : pullback f q ⟶ pullback u q₀ :=
    pullback.map f q u q₀ (𝟙 U.left) Y.isoSpec.hom X.isoSpec.hom
      (by
        change (u ≫ X.isoSpec.inv) ≫ X.isoSpec.hom = (𝟙 U.left) ≫ u
        rw [Category.id_comp, Category.assoc, Iso.inv_hom_id, Category.comp_id])
      (Scheme.isoSpec_hom_naturality q).symm
  have hm : m ≫ pullback.snd u q₀ = pullback.snd f q ≫ Y.isoSpec.hom :=
    pullback.lift_snd _ _ _
  have hsp : (s ≫ W.isoSpec.inv) ≫ p = pullback.snd u q₀ ≫ Y.isoSpec.inv := by
    calc
      (s ≫ W.isoSpec.inv) ≫ p = s ≫ (W.isoSpec.inv ≫ p) := Category.assoc _ _ _
      _ = s ≫ (p₀ ≫ Y.isoSpec.inv) :=
        congrArg (fun h => s ≫ h) (Scheme.isoSpec_inv_naturality p).symm
      _ = (s ≫ p₀) ≫ Y.isoSpec.inv := (Category.assoc _ _ _).symm
      _ = pullback.snd u q₀ ≫ Y.isoSpec.inv :=
        congrArg (fun h => h ≫ Y.isoSpec.inv) hs
  refine ⟨V, v, hV, m ≫ s ≫ W.isoSpec.inv, ?_⟩
  change (m ≫ s ≫ W.isoSpec.inv) ≫ p = pullback.snd f q
  calc
    (m ≫ s ≫ W.isoSpec.inv) ≫ p = m ≫ ((s ≫ W.isoSpec.inv) ≫ p) :=
      Category.assoc _ _ _
    _ = m ≫ (pullback.snd u q₀ ≫ Y.isoSpec.inv) := congrArg (fun h => m ≫ h) hsp
    _ = (m ≫ pullback.snd u q₀) ≫ Y.isoSpec.inv := (Category.assoc _ _ _).symm
    _ = (pullback.snd f q ≫ Y.isoSpec.hom) ≫ Y.isoSpec.inv :=
      congrArg (fun h => h ≫ Y.isoSpec.inv) hm
    _ = pullback.snd f q := by rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]

end EtaleCohomology
