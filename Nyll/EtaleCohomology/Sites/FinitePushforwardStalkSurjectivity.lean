/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleCohomology.Constructible.SigmaRepresenter
import Nyll.EtaleCohomology.Sites.FiniteMarkedNeighborhood
import Nyll.EtaleCohomology.Sites.FinitePushforwardStalks
import Mathlib.CategoryTheory.ConcreteCategory.EpiMono
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.CategoryTheory.Sites.Point.Basic
import Mathlib.CategoryTheory.Sites.Whiskering

/-!
# The finite direct-image geometric stalk formula

Represent each component of a tuple of germs on an actual pointed étale
neighborhood. Their disjoint union carries the glued section. The marked
finite neighborhood theorem gives a single ambient pointed neighborhood
whose finite inverse image maps to that union with all prescribed geometric
values. Its section therefore represents the entire tuple simultaneously.

Together with the existing injectivity theorem this proves that the actual
canonical comparison is an isomorphism, Stacks Project 59.55.2(1). The proof
applies to sets, abelian groups and modules via their usual forgetful functors.
-/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits Opposite

namespace EtaleCohomology

variable {A : Type (u + 1)} [Category.{u} A]
  {FA : A → A → Type u} {CA : A → Type u}
  [∀ M N, FunLike (FA M N) (CA M) (CA N)] [ConcreteCategory.{u} A FA]
  [HasColimitsOfSize.{u, u} A]
  [PreservesFilteredColimitsOfSize.{u, u} (forget A)]

/-- Every tuple of geometric germs over a finite fiber comes from one actual
direct-image germ. The prescribed field-valued lifts are retained. -/
theorem etalePushforwardStalkComponents_jointly_surjective
    {X Y : Scheme.{u}} (q : Y ⟶ X) [IsFinite q]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ X)
    [Y.smallEtaleTopology.HasSheafCompose (forget A)]
    (F : Sheaf Y.smallEtaleTopology A)
    (a : ∀ s : {s : Spec (.of Ω) ⟶ Y // s ≫ q = t},
      ToType ((Scheme.pointSmallEtale s.val).sheafFiber.obj F)) :
    ∃ b : ToType ((Scheme.pointSmallEtale t).sheafFiber.obj
      (((etaleBaseChange q).sheafPushforwardContinuous A
        X.smallEtaleTopology Y.smallEtaleTopology).obj F)),
      ∀ s, etalePushforwardStalkComponent q t s F b = a s := by
  classical
  let I := {s : Spec (.of Ω) ⟶ Y // s ≫ q = t}
  have hrepr (s : I) := (Scheme.pointSmallEtale s.val).toPresheafFiber_jointly_surjective
    (P := F.obj) (a s)
  choose U u z hz using hrepr
  let W : Y.Etale := etaleSigma U
  let w (s : I) : Spec (.of Ω) ⟶ W.left := (u s).left ≫ (etaleSigmaInj U s).left
  have hw (s : I) : w s ≫ W.hom = s.val := by
    let j : (U s).left ⟶ W.left := (etaleSigmaInj U s).left
    have hj : j ≫ W.hom = (U s).hom := (etaleSigmaInj U s).w
    exact (Category.assoc _ _ _).trans
      ((congrArg (fun r => (u s).left ≫ r) hj).trans (u s).w)
  obtain ⟨V, v, _, bV, hbV, hbmarked⟩ :=
    exists_pointed_etale_lift_prescribed_of_isFinite q t W.hom w hw
  let B : Y.Etale := (etaleBaseChange q).obj V
  let k : B ⟶ W := MorphismProperty.Over.homMk
    (P := show MorphismProperty Scheme.{u} from @Etale) (Q := ⊤) bV hbV
  let G : Sheaf Y.smallEtaleTopology (Type u) :=
    (sheafCompose Y.smallEtaleTopology (forget A)).obj F
  let zW : ToType (F.obj.obj (op W)) := etaleSigmaSection U G z
  have hzW (s : I) : F.obj.map (etaleSigmaInj U s).op zW = z s :=
    etaleSigmaSection_restrict U G z s
  let P : X.Etaleᵒᵖ ⥤ A :=
    (((etaleBaseChange q).sheafPushforwardContinuous A
      X.smallEtaleTopology Y.smallEtaleTopology).obj F).obj
  let zV : ToType (P.obj (op V)) := F.obj.map k.op zW
  refine ⟨(Scheme.pointSmallEtale t).toPresheafFiber V v P zV, ?_⟩
  intro s
  let vB := etalePushforwardGeometricLift q t s V v
  have hvB : (Scheme.pointSmallEtale s.val).fiber.map k vB =
      (Scheme.pointSmallEtale s.val).fiber.map (etaleSigmaInj U s) (u s) := by
    apply Over.OverMorphism.ext
    exact hbmarked s
  let Φ := Scheme.pointSmallEtale t
  let Ψ := Scheme.pointSmallEtale s.val
  let γ : P.obj (op V) ⟶ Φ.presheafFiber.obj P := Φ.toPresheafFiber V v P
  let c : Φ.presheafFiber.obj P ⟶ Ψ.presheafFiber.obj F.obj :=
    etalePushforwardStalkComponent q t s F
  let δ : P.obj (op V) ⟶ Ψ.presheafFiber.obj F.obj :=
    Ψ.toPresheafFiber B vB F.obj
  have hraw : γ ≫ c = δ :=
    toPresheafFiber_etalePushforwardStalkComponent q t s F V v
  have hcomp : c (γ zV) = δ zV :=
    (ConcreteCategory.comp_apply γ c zV).symm.trans (ConcreteCategory.congr_hom hraw zV)
  have hk : δ zV = Ψ.toPresheafFiber W (Ψ.fiber.map k vB) F.obj zW :=
    Ψ.toPresheafFiber_w_apply k vB F.obj zW
  have hm : Ψ.toPresheafFiber W (Ψ.fiber.map k vB) F.obj zW =
      Ψ.toPresheafFiber W (Ψ.fiber.map (etaleSigmaInj U s) (u s)) F.obj zW :=
    congrArg (fun r => Ψ.toPresheafFiber W r F.obj zW) hvB
  have hj : Ψ.toPresheafFiber W (Ψ.fiber.map (etaleSigmaInj U s) (u s)) F.obj zW =
      Ψ.toPresheafFiber (U s) (u s) F.obj (F.obj.map (etaleSigmaInj U s).op zW) :=
    (Ψ.toPresheafFiber_w_apply (etaleSigmaInj U s) (u s) F.obj zW).symm
  have hz' : Ψ.toPresheafFiber (U s) (u s) F.obj
      (F.obj.map (etaleSigmaInj U s).op zW) =
      Ψ.toPresheafFiber (U s) (u s) F.obj (z s) :=
    congrArg (Ψ.toPresheafFiber (U s) (u s) F.obj) (hzW s)
  exact hcomp.trans (hk.trans (hm.trans (hj.trans (hz'.trans (hz s)))))

variable [HasProducts.{u} A] [PreservesLimitsOfSize.{u, u} (forget A)]

/-- The canonical finite direct-image product comparison is surjective on
underlying elements. -/
theorem etalePushforwardStalkComparison_surjective
    {X Y : Scheme.{u}} (q : Y ⟶ X) [IsFinite q]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ X)
    [Y.smallEtaleTopology.HasSheafCompose (forget A)]
    (F : Sheaf Y.smallEtaleTopology A) :
    Function.Surjective (etalePushforwardStalkComparison q t F) := by
  intro a
  let S := fun s : {s : Spec (.of Ω) ⟶ Y // s ≫ q = t} =>
    (Scheme.pointSmallEtale s.val).sheafFiber.obj F
  obtain ⟨b, hb⟩ := etalePushforwardStalkComponents_jointly_surjective q t F
    (fun s => Pi.π S s a)
  refine ⟨b, ?_⟩
  apply Concrete.limit_ext (Discrete.functor S)
  intro ⟨s⟩
  have h := ConcreteCategory.congr_hom (etalePushforwardStalkComparison_π q t s F) b
  simp only [ConcreteCategory.comp_apply] at h
  exact h.trans (hb s)

variable [(forget A).ReflectsIsomorphisms]

/-- Stacks Project 59.55.2(1): the actual geometric stalk of finite direct
image is canonically the product of the actual stalks over its finite fiber. -/
theorem etalePushforwardStalkComparison_isIso
    {X Y : Scheme.{u}} (q : Y ⟶ X) [IsFinite q]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ X)
    [Y.smallEtaleTopology.HasSheafCompose (forget A)]
    (F : Sheaf Y.smallEtaleTopology A) :
    IsIso (etalePushforwardStalkComparison q t F) := by
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  refine ⟨?_, etalePushforwardStalkComparison_surjective q t F⟩
  intro a b hab
  apply etalePushforwardStalkComponents_jointly_injective q t F
  intro s
  have h := congrArg
    (Pi.π (fun s : {s : Spec (.of Ω) ⟶ Y // s ≫ q = t} =>
      (Scheme.pointSmallEtale s.val).sheafFiber.obj F) s) hab
  have ha := ConcreteCategory.congr_hom (etalePushforwardStalkComparison_π q t s F) a
  have hb := ConcreteCategory.congr_hom (etalePushforwardStalkComparison_π q t s F) b
  simp only [ConcreteCategory.comp_apply] at ha hb
  exact ha.symm.trans (h.trans hb)

end EtaleCohomology
