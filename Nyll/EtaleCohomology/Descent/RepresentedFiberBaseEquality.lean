/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Descent.RepresentedSectionEvaluationNaturality
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

/-!
# Original base-equality transport on represented fiber sections

The equality between the two composites from an overlap to its base
transports the actual direct image by its original equality isomorphism.
On represented geometric-fiber sections this is precisely precomposition
by the inverse of the existing pullback congruence isomorphism.
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits

universe u

namespace EtaleCohomology

variable {S Z T : Scheme.{u}} (t : T ⟶ S) (f g : Z ⟶ S) (hfg : f = g)

/-- The actual equality of base maps acts on original represented
sections by the canonical congruence map of their fiber products. -/
def representedSectionsBaseEquality (W : Z.Etale) :
    (Over.mk (pullback.snd t f) ⟶ (Scheme.Etale.forget Z).obj W) ⟶
      (Over.mk (pullback.snd t g) ⟶ (Scheme.Etale.forget Z).obj W) :=
  TypeCat.ofHom (fun a => Over.homMk
    ((pullback.congrHom (rfl : t = t) hfg).inv ≫ a.left)
    ((Category.assoc _ _ _).trans
      ((congrArg (fun k => (pullback.congrHom (rfl : t = t) hfg).inv ≫ k) a.w).trans
        (by
          change (pullback.congrHom (rfl : t = t) hfg).inv ≫ pullback.snd t f =
            pullback.snd t g
          simp only [pullback.congrHom_inv, pullback.lift_snd, Category.comp_id]))))

/-- Reflexive equality gives the identity on the actual section set. -/
lemma representedSectionsBaseEquality_refl (W : Z.Etale) :
    representedSectionsBaseEquality t f f rfl W = 𝟙 _ := by
  apply ConcreteCategory.hom_ext
  intro a
  apply Over.OverMorphism.ext
  change (pullback.congrHom (rfl : t = t) (rfl : f = f)).inv ≫ a.left = a.left
  rw [pullback.congrHom_inv, pullback.map_id, Category.id_comp]

variable {R Ω : Type u} [CommRing R] [Field Ω] [IsSepClosed Ω]
  (φ : R →+* Ω) {X : Scheme.{u}}

/-- The original direct-image equality isomorphism becomes the actual
pullback-congruence precomposition on represented geometric-fiber
sections. This applies to the original double-overlap equality. -/
theorem etaleSetPushforwardRepresentableGeometricFiberSections_baseEquality
    (f g : X ⟶ Spec (CommRingCat.of R)) (hfg : f = g) (W : X.Etale) :
    (Scheme.pointSmallEtale (Spec.map (CommRingCat.ofHom φ))).sheafFiber.map
        ((eqToIso (congrArg (fun r => etaleSetPushforward r) hfg)).hom.app
          (X.smallEtaleTopology.yoneda.obj W)) ≫
      etaleSetPushforwardRepresentableGeometricFiberSections φ g W =
    etaleSetPushforwardRepresentableGeometricFiberSections φ f W ≫
      representedSectionsBaseEquality (Spec.map (CommRingCat.ofHom φ)) f g hfg W := by
  subst g
  let Φ := Scheme.pointSmallEtale (Spec.map (CommRingCat.ofHom φ))
  let c := etaleSetPushforwardRepresentableGeometricFiberSections φ f W
  have hm :
      Φ.sheafFiber.map
          ((eqToIso (congrArg (fun r => etaleSetPushforward r) (rfl : f = f))).hom.app
            (X.smallEtaleTopology.yoneda.obj W)) = 𝟙 _ :=
    Φ.sheafFiber.map_id _
  have hr := representedSectionsBaseEquality_refl
    (Spec.map (CommRingCat.ofHom φ)) f W
  exact (congrArg (fun k => k ≫ c) hm).trans
    ((Category.id_comp c).trans
      ((Category.comp_id c).symm.trans (congrArg (fun k => c ≫ k) hr.symm)))

end EtaleCohomology
