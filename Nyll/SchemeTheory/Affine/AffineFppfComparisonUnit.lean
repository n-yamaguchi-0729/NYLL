/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Affine.AffineFppfComparison
import Mathlib.CategoryTheory.Adjunction.Unique

/-!
# The dense affine comparison retains the original sections

The actual isomorphism constructed by affine sheafification sends an affine
raw section to the sheafification of its original affine comparison. This
compatibility allows concrete local representatives to be transported across
the comparison, rather than only identifying the abstract sheaves.
-/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Opposite

namespace SchemeTheory.Affine

variable (R : CommRingCat.{u})

private theorem affineSheafificationCompatibility_unit
    (P : (Over (Spec R))ᵒᵖ ⥤ Type (u + 1)) :
    Functor.whiskerLeft (affineForget R).op
        (toSheafify (Scheme.fppfTopology.over (Spec R)) P) =
      toSheafify ((affineForget R).restrictedTopology
          (Scheme.fppfTopology.over (Spec R))) ((affineForget R).op ⋙ P) ≫
        ((Functor.IsDenseSubsite.sheafEquivSheafificationCompatibility
          ((affineForget R).restrictedTopology (Scheme.fppfTopology.over (Spec R)))
          (Scheme.fppfTopology.over (Spec R)) (affineForget R) (Type (u + 1))).app P).hom.hom := by
  let K := Scheme.fppfTopology.over (Spec R)
  let J := (affineForget R).restrictedTopology K
  let H := (affineForget R).sheafPushforwardContinuous (Type (u + 1)) J K
  let adj₁ := Functor.IsDenseSubsite.sheafifyAdjunctionOfIsEquivalence
    J K (affineForget R) (Type (u + 1))
  let adj₂ := sheafificationAdjunction K (Type (u + 1))
  let a := adj₁.leftAdjointUniq adj₂
  have hu : adj₁.homEquiv _ _ (a.hom.app P) = toSheafify K P :=
    adj₁.homEquiv_leftAdjointUniq_hom_app adj₂ P
  rw [← hu]
  dsimp only [adj₁, Functor.IsDenseSubsite.sheafifyAdjunctionOfIsEquivalence]
  rw [Adjunction.mkOfHomEquiv_homEquiv]
  change (Functor.IsCoverDense.restrictHomEquivHom (G := affineForget R)).symm
      ((Functor.IsCoverDense.restrictHomEquivHom (G := affineForget R))
        ((sheafificationAdjunction J (Type (u + 1))).homEquiv _ _
          (H.asEquivalence.symm.toAdjunction.homEquiv _ _ (a.hom.app P)))) = _
  exact Equiv.symm_apply_apply
    (Functor.IsCoverDense.restrictHomEquivHom (G := affineForget R)) _

variable {F G : (Over (Spec R))ᵒᵖ ⥤ Type (u + 1)}

/-- The actual dense affine isomorphism agrees with the given raw affine map
after sheafification. -/
theorem fppfSheafificationIsoOfAffineRestriction_toSheafify
    (e : (affineForget R).op ⋙ F ≅ (affineForget R).op ⋙ G) :
    Functor.whiskerLeft (affineForget R).op
        (toSheafify (Scheme.fppfTopology.over (Spec R)) F ≫
          (fppfSheafificationIsoOfAffineRestriction R e).hom.hom) =
      e.hom ≫ Functor.whiskerLeft (affineForget R).op
        (toSheafify (Scheme.fppfTopology.over (Spec R)) G) := by
  let K := Scheme.fppfTopology.over (Spec R)
  let J := (affineForget R).restrictedTopology K
  let E := Functor.IsDenseSubsite.sheafEquiv J K (affineForget R) (Type (u + 1))
  let c := Functor.IsDenseSubsite.sheafEquivSheafificationCompatibility
    J K (affineForget R) (Type (u + 1))
  have hm : E.inverse.map (fppfSheafificationIsoOfAffineRestriction R e).hom =
      (c.app F).inv ≫ (presheafToSheaf J (Type (u + 1))).map e.hom ≫ (c.app G).hom := by
    exact E.symm.fullyFaithfulFunctor.map_preimage _
  rw [Functor.whiskerLeft_comp, affineSheafificationCompatibility_unit,
    affineSheafificationCompatibility_unit]
  change (toSheafify J ((affineForget R).op ⋙ F) ≫ (c.app F).hom.hom) ≫
      (E.inverse.map (fppfSheafificationIsoOfAffineRestriction R e).hom).hom = _
  rw [hm]
  have hcF : (c.app F).hom.hom ≫ (c.app F).inv.hom = 𝟙 _ :=
    congrArg (fun f => f.hom) (c.app F).hom_inv_id
  change (toSheafify J ((affineForget R).op ⋙ F) ≫ (c.app F).hom.hom) ≫
      ((c.app F).inv.hom ≫ sheafifyMap J e.hom ≫ (c.app G).hom.hom) =
    e.hom ≫ toSheafify J ((affineForget R).op ⋙ G) ≫ (c.app G).hom.hom
  rw [Category.assoc, ← Category.assoc (c.app F).hom.hom (c.app F).inv.hom,
    hcF, Category.id_comp, ← Category.assoc, ← toSheafify_naturality, Category.assoc]

/-- Zariski existence of raw representatives transfers through the proved
affine comparison. The refinement uses the actual affine open cover. -/
theorem toSheafify_isLocallySurjective_zariski_of_affineIso
    (e : (affineForget R).op ⋙ F ≅ (affineForget R).op ⋙ G)
    [Presheaf.IsLocallySurjective (Scheme.zariskiTopology.over (Spec R))
      (toSheafify (Scheme.fppfTopology.over (Spec R)) F)] :
    Presheaf.IsLocallySurjective (Scheme.zariskiTopology.over (Spec R))
      (toSheafify (Scheme.fppfTopology.over (Spec R)) G) := by
  let J := Scheme.zariskiTopology.over (Spec R)
  let K := Scheme.fppfTopology.over (Spec R)
  let ηF := toSheafify K F
  let ηG := toSheafify K G
  let H := fppfSheafificationIsoOfAffineRestriction R e
  let α := ηF ≫ H.hom.hom
  have : Presheaf.IsLocallySurjective J α := inferInstance
  have hc : Functor.whiskerLeft (affineForget R).op α =
      e.hom ≫ Functor.whiskerLeft (affineForget R).op ηG :=
    fppfSheafificationIsoOfAffineRestriction_toSheafify R e
  constructor
  intro T s
  apply J.transitive (Presheaf.imageSieve_mem J α s) _
  intro Y f hf
  obtain ⟨a, ha⟩ := hf
  apply J.superset_covering ?_ ((affineForget R).is_cover_of_isCoverDense J Y)
  rintro Z _ ⟨⟨A₀, j, k, rfl⟩⟩
  apply ((Presheaf.imageSieve ηG s).pullback f).downward_closed ?_ j
  refine ⟨e.hom.app (op A₀) (F.map k.op a), ?_⟩
  have he := ConcreteCategory.congr_hom
    (congrArg (fun θ => θ.app (op A₀)) hc) (F.map k.op a)
  change α.app (op ((affineForget R).obj A₀)) (F.map k.op a) =
    ηG.app (op ((affineForget R).obj A₀)) (e.hom.app (op A₀) (F.map k.op a)) at he
  change ηG.app (op ((affineForget R).obj A₀))
    (e.hom.app (op A₀) (F.map k.op a)) = (sheafify K G).map (k ≫ f).op s
  rw [← he]
  have hn := ConcreteCategory.congr_hom (α.naturality k.op) a
  change α.app (op ((affineForget R).obj A₀)) (F.map k.op a) =
    (sheafify K G).map k.op (α.app (op Y) a) at hn
  rw [hn, ha, op_comp, Functor.map_comp]
  rfl

end SchemeTheory.Affine
