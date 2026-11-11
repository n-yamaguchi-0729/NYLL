/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleCohomology.Descent.FiniteLocallyConstantStrictLocalSections
import Nyll.EtaleCohomology.Descent.RepresentedSectionEvaluationNaturality

/-!
# Original coefficient maps on represented geometric-fiber sections

The original geometric-fiber section comparison is natural for morphisms
of representers. The existing strict-local naturality and literal
evaluation supply the square, whose lower map is actual postcomposition
into the original representer.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Limits
open EtaleFundamentalGroups.StrictHenselian

universe u

namespace EtaleCohomology

variable {R Ω : Type u} [CommRing R] [Field Ω]
  (φ : R →+* Ω) {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))

/-- Literal evaluation commutes with actual postcomposition into the
original represented étale scheme. -/
theorem geometricStalkEvaluationRepresentedSectionsMap_naturality
    {V W : X.Etale} (k : V ⟶ W) :
    TypeCat.ofHom (fun a : Over.mk
        (pullback.snd (Spec.map (CommRingCat.ofHom (geometricStalkStructureMap φ))) f) ⟶
          (Scheme.Etale.forget X).obj V =>
        a ≫ (Scheme.Etale.forget X).map k) ≫
      geometricStalkEvaluationRepresentedSectionsMap φ f W =
    geometricStalkEvaluationRepresentedSectionsMap φ f V ≫
      TypeCat.ofHom (fun a : Over.mk
        (pullback.snd (Spec.map (CommRingCat.ofHom φ)) f) ⟶
          (Scheme.Etale.forget X).obj V =>
        a ≫ (Scheme.Etale.forget X).map k) := by
  apply ConcreteCategory.hom_ext
  intro a
  apply Over.OverMorphism.ext
  change geometricStalkEvaluationBaseChangeMap φ f ≫ (a.left ≫ k.left) =
    (geometricStalkEvaluationBaseChangeMap φ f ≫ a.left) ≫ k.left
  exact (Category.assoc _ _ _).symm

variable [IsSepClosed Ω]

/-- The original direct-image stalk coefficient map becomes literal
postcomposition on the original geometric-fiber represented sections.
In particular this applies to the original represented overlap map. -/
theorem etaleSetPushforwardRepresentableGeometricFiberSections_naturality
    {V W : X.Etale} (k : V ⟶ W) :
    (Scheme.pointSmallEtale (Spec.map (CommRingCat.ofHom φ))).sheafFiber.map
        ((etaleSetPushforward f).map (X.smallEtaleTopology.yoneda.map k)) ≫
      etaleSetPushforwardRepresentableGeometricFiberSections φ f W =
    etaleSetPushforwardRepresentableGeometricFiberSections φ f V ≫
      TypeCat.ofHom (fun a : Over.mk
        (pullback.snd (Spec.map (CommRingCat.ofHom φ)) f) ⟶
          (Scheme.Etale.forget X).obj V =>
        a ≫ (Scheme.Etale.forget X).map k) := by
  let Φ := Scheme.pointSmallEtale (Spec.map (CommRingCat.ofHom φ))
  let m := Φ.sheafFiber.map
    ((etaleSetPushforward f).map (X.smallEtaleTopology.yoneda.map k))
  let cV := etaleSetPushforwardRepresentableGeometricStalkSections φ f V
  let cW := etaleSetPushforwardRepresentableGeometricStalkSections φ f W
  let eV := geometricStalkEvaluationRepresentedSectionsMap φ f V
  let eW := geometricStalkEvaluationRepresentedSectionsMap φ f W
  let kH := TypeCat.ofHom (fun a : Over.mk
    (pullback.snd (Spec.map (CommRingCat.ofHom (geometricStalkStructureMap φ))) f) ⟶
      (Scheme.Etale.forget X).obj V => a ≫ (Scheme.Etale.forget X).map k)
  let kΩ := TypeCat.ofHom (fun a : Over.mk
    (pullback.snd (Spec.map (CommRingCat.ofHom φ)) f) ⟶
      (Scheme.Etale.forget X).obj V => a ≫ (Scheme.Etale.forget X).map k)
  have hn : m ≫ cW = cV ≫ kH :=
    etaleSetPushforwardRepresentableGeometricStalkSections_naturality φ f k
  have he : kH ≫ eW = eV ≫ kΩ :=
    geometricStalkEvaluationRepresentedSectionsMap_naturality φ f k
  change m ≫ (cW ≫ eW) = (cV ≫ eV) ≫ kΩ
  exact (Category.assoc m cW eW).symm.trans
    ((congrArg (fun h => h ≫ eW) hn).trans
      ((Category.assoc cV kH eW).trans
        ((congrArg (fun h => cV ≫ h) he).trans (Category.assoc cV eV kΩ).symm)))

end EtaleCohomology
