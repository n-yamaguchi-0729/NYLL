/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleCohomology.Sites.FiniteStrictLocalMarkedDescent
import Nyll.EtaleCohomology.Sites.PushforwardStalkComparison
import Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalkFlat
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Sites.EtalePoint

/-!
# Simultaneous marked neighborhoods for finite morphisms

An affine pointed neighborhood of an arbitrary base reduces the simultaneous
lifting problem to the affine case. The descended neighborhood and section
are then transported through the literal scheme pullbacks. Pullback
uniqueness preserves all prescribed field-valued lifts.

This supplies the geometric neighborhood construction for the product
description of finite direct-image stalks in Stacks Project 59.55.2(1).
-/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits
open EtaleFundamentalGroups.StrictHenselian

namespace EtaleCohomology

/-- After an actual affine pointed étale refinement of an arbitrary base,
an étale lift of a finite scheme realizes every prescribed geometric lift
simultaneously. No affineness condition is imposed on the étale target. -/
theorem exists_pointed_etale_lift_prescribed_of_isFinite
    {X Y W : Scheme.{u}} (q : Y ⟶ X) [IsFinite q]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ X)
    (p : W ⟶ Y) [Etale p]
    (w : {s : Spec (.of Ω) ⟶ Y // s ≫ q = t} → (Spec (.of Ω) ⟶ W))
    (hw : ∀ s, w s ≫ p = s.val) :
    ∃ (V : X.Etale) (v : (Scheme.pointSmallEtale t).fiber.obj V),
      IsAffine V.left ∧ ∃ b : pullback V.hom q ⟶ W,
        b ≫ p = pullback.snd V.hom q ∧
        ∀ s, (etalePushforwardGeometricLift q t s V v).left ≫ b = w s := by
  let T : X.Etale := Scheme.Etale.mk (𝟙 X)
  let tT : (Scheme.pointSmallEtale t).fiber.obj T :=
    Over.homMk t (Category.comp_id _)
  obtain ⟨U, u, _, hU, _⟩ := geometricStalk_exists_affine_refinement t T tT
  have : IsAffine U.left := hU
  have hu : u.left ≫ U.hom = t := u.w
  let B := pullback U.hom q
  let r : B ⟶ U.left := pullback.fst U.hom q
  let a : B ⟶ Y := pullback.snd U.hom q
  have : IsFinite r := inferInstanceAs (IsFinite (pullback.fst U.hom q))
  let pB : pullback p a ⟶ B := pullback.snd p a
  let I := {s : Spec (.of Ω) ⟶ Y // s ≫ q = t}
  let J := {z : Spec (.of Ω) ⟶ B // z ≫ r = u.left}
  let f : J → I := fun z => ⟨z.val ≫ a, by
    calc
      (z.val ≫ a) ≫ q = z.val ≫ (a ≫ q) := Category.assoc _ _ _
      _ = z.val ≫ (r ≫ U.hom) :=
        congrArg (fun h => z.val ≫ h) pullback.condition.symm
      _ = (z.val ≫ r) ≫ U.hom := (Category.assoc _ _ _).symm
      _ = u.left ≫ U.hom := congrArg (fun h => h ≫ U.hom) z.property
      _ = t := hu⟩
  let wB (z : J) : Spec (.of Ω) ⟶ pullback p a :=
    pullback.lift (w (f z)) z.val (hw (f z))
  obtain ⟨V₀, v₀, hV, b₀, hb₀, hmarked⟩ :=
    exists_pointed_etale_lift_prescribed_of_isFinite_of_isAffine r u.left pB wB
      (fun _ => pullback.lift_snd _ _ _)
  have hv₀ : v₀.left ≫ V₀.hom = u.left := v₀.w
  let V : X.Etale := Scheme.Etale.mk (V₀.hom ≫ U.hom)
  let v : (Scheme.pointSmallEtale t).fiber.obj V := Over.homMk v₀.left (by
    exact (Category.assoc v₀.left V₀.hom U.hom).symm.trans
      ((congrArg (fun h => h ≫ U.hom) hv₀).trans hu))
  let m : pullback V.hom q ⟶ B :=
    pullback.lift (pullback.fst V.hom q ≫ V₀.hom) (pullback.snd V.hom q) (by
      change (pullback.fst V.hom q ≫ V₀.hom) ≫ U.hom = pullback.snd V.hom q ≫ q
      exact (Category.assoc _ _ _).trans pullback.condition)
  have hmR : m ≫ r = pullback.fst V.hom q ≫ V₀.hom := pullback.lift_fst _ _ _
  have hmY : m ≫ a = pullback.snd V.hom q := pullback.lift_snd _ _ _
  let l : pullback V.hom q ⟶ pullback V₀.hom r :=
    pullback.lift (pullback.fst V.hom q) m hmR.symm
  have hlV : l ≫ pullback.fst V₀.hom r = pullback.fst V.hom q :=
    pullback.lift_fst _ _ _
  have hlR : l ≫ pullback.snd V₀.hom r = m := pullback.lift_snd _ _ _
  refine ⟨V, v, hV, l ≫ b₀ ≫ pullback.fst p a, ?_, ?_⟩
  · calc
      (l ≫ b₀ ≫ pullback.fst p a) ≫ p =
          l ≫ b₀ ≫ (pullback.fst p a ≫ p) := by
        rw [Category.assoc, Category.assoc]
      _ = l ≫ b₀ ≫ (pB ≫ a) :=
        congrArg (fun h => l ≫ b₀ ≫ h) pullback.condition
      _ = (l ≫ (b₀ ≫ pB)) ≫ a := by
        rw [Category.assoc, Category.assoc]
      _ = (l ≫ pullback.snd V₀.hom r) ≫ a :=
        congrArg (fun h => (l ≫ h) ≫ a) hb₀
      _ = m ≫ a := congrArg (fun h => h ≫ a) hlR
      _ = pullback.snd V.hom q := hmY
  · intro s
    let z : J := ⟨pullback.lift u.left s.val (hu.trans s.property.symm),
      pullback.lift_fst _ _ _⟩
    have hf : f z = s := Subtype.ext (pullback.lift_snd _ _ _)
    let n : Spec (.of Ω) ⟶ pullback V.hom q :=
      (etalePushforwardGeometricLift q t s V v).left
    let n₀ : Spec (.of Ω) ⟶ pullback V₀.hom r :=
      (etalePushforwardGeometricLift r u.left z V₀ v₀).left
    have hnV : n ≫ pullback.fst V.hom q = v₀.left := pullback.lift_fst _ _ _
    have hnm : n ≫ m = z.val := by
      apply pullback.hom_ext
      · exact (Category.assoc n m r).trans
          ((congrArg (fun k => n ≫ k) hmR).trans
            ((Category.assoc n (pullback.fst V.hom q) V₀.hom).symm.trans
              ((congrArg (fun k => k ≫ V₀.hom) hnV).trans
                (hv₀.trans z.property.symm))))
      · rw [Category.assoc, hmY]
        exact (pullback.lift_snd _ _ _).trans (pullback.lift_snd _ _ _).symm
    have hnl : n ≫ l = n₀ := by
      apply pullback.hom_ext
      · rw [Category.assoc, hlV]
        exact (pullback.lift_fst _ _ _).trans (pullback.lift_fst _ _ _).symm
      · rw [Category.assoc, hlR, hnm]
        exact (pullback.lift_snd _ _ _).symm
    calc
      n ≫ (l ≫ b₀ ≫ pullback.fst p a) =
          ((n ≫ l) ≫ b₀) ≫ pullback.fst p a := by
        rw [Category.assoc, Category.assoc]
      _ = (n₀ ≫ b₀) ≫ pullback.fst p a :=
        congrArg (fun h => (h ≫ b₀) ≫ pullback.fst p a) hnl
      _ = wB z ≫ pullback.fst p a :=
        congrArg (fun h => h ≫ pullback.fst p a) (hmarked z)
      _ = w (f z) := pullback.lift_fst _ _ _
      _ = w s := congrArg w hf

end EtaleCohomology
