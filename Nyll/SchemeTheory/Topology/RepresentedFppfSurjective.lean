/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.CategoryTheory.Sites.Over
import Mathlib.CategoryTheory.Sites.LocallySurjective
import Mathlib.CategoryTheory.Yoneda

/-! # A represented locally surjective fppf map is surjective on scheme points -/

noncomputable section

universe u w

open CategoryTheory Opposite

namespace AlgebraicGeometry

/-- A genuine local lifting property supplies a preimage of every scheme point.
Apply it to the universal class, then use a member of its actual covering sieve. -/
theorem surjective_of_represented_fppf_locallySurjective {S : Scheme.{u}}
    {F G : (Over S)ᵒᵖ ⥤ Type w} {X Y : Over S} (a : F ⟶ G)
    (eF : F.RepresentableBy X) (eG : G.RepresentableBy Y) (m : X ⟶ Y)
    (hm : ∀ {T : Over S} (f : T ⟶ X),
      eG.homEquiv (f ≫ m) = a.app (op T) (eF.homEquiv f))
    [Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) a] : Surjective m.left := by
  let y := eG.homEquiv (𝟙 Y)
  let R := Presheaf.imageSieve a y
  have hR : Sieve.overEquiv Y R ∈ Scheme.fppfTopology Y.left :=
    (GrothendieckTopology.mem_over_iff _ _).mp
      (Presheaf.imageSieve_mem (Scheme.fppfTopology.over S) a y)
  have : Scheme.fppfPrecoverage.{u}.HasIsos :=
    ⟨fun f => Scheme.Hom.singleton_mem_fppfPrecoverage f⟩
  obtain ⟨Q, hQ, hQR⟩ :=
    (Precoverage.mem_toGrothendieck_iff_of_isStableUnderComposition
      (J := Scheme.fppfPrecoverage)).mp hR
  obtain ⟨V, rfl⟩ := Precoverage.mem_iff_exists_zeroHypercover.mp hQ
  have hV := hQR
  have : Scheme.JointlySurjective Scheme.fppfPrecoverage.{u} :=
    inferInstanceAs (Scheme.JointlySurjective
      (Scheme.precoverage ((@Flat : MorphismProperty Scheme.{u}) ⊓ @LocallyOfFinitePresentation)))
  constructor
  intro z
  obtain ⟨j, v, hv⟩ := Scheme.Cover.exists_eq V z
  let U : Over S := Over.mk (V.f j ≫ Y.hom)
  let q : U ⟶ Y := Over.homMk (V.f j) rfl
  have hq : R q := (Sieve.overEquiv_iff R (V.f j)).mp
    ((Presieve.ofArrows_le_iff.mp hV) j)
  obtain ⟨x, hx⟩ := hq
  let f : U ⟶ X := eF.homEquiv.symm x
  have hf : f ≫ m = q := by
    apply eG.homEquiv.injective
    calc
      eG.homEquiv (f ≫ m) = a.app (op U) (eF.homEquiv f) := hm f
      _ = a.app (op U) x := congrArg (a.app (op U)) (eF.homEquiv.apply_symm_apply x)
      _ = G.map q.op (eG.homEquiv (𝟙 Y)) := hx
      _ = eG.homEquiv q := by
        rw [← eG.homEquiv_comp, Category.comp_id]
  exact ⟨f.left v, (congrArg (fun k : U ⟶ Y => k.left v) hf).trans hv⟩

end AlgebraicGeometry
