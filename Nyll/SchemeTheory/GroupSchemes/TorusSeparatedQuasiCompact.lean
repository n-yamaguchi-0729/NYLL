/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.GroupSchemes.Torus
import Nyll.SchemeTheory.Morphisms.SeparatedQuasiCompactDescent
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! # Separatedness and quasi-compactness of actual tori -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.IsTorus

variable {K : Type u} [Field K] {G : CommGrp (Over (Spec (CommRingCat.of K)))}

/-- A torus is quasi-compact over its ground field. -/
instance quasiCompact [IsTorus G] : QuasiCompact G.X.hom := by
  let Ω := AlgebraicClosure K
  let f : Spec (CommRingCat.of Ω) ⟶ Spec (CommRingCat.of K) :=
    Spec.map (CommRingCat.ofHom (algebraMap K Ω))
  have : Surjective f := ⟨fun y => ⟨default, Subsingleton.elim _ y⟩⟩
  obtain ⟨r, hr⟩ := exists_geometric_split (G := G)
  obtain ⟨e⟩ := hr Ω f
  have hs : QuasiCompact (GroupSchemes.splitTorus Ω r).X.hom := by
    change QuasiCompact
      (Spec.map (CommRingCat.ofHom (algebraMap Ω (GroupSchemes.splitTorusAlgebra Ω r))))
    infer_instance
  have : QuasiCompact (pullback.snd G.X.hom f) :=
    GroupSchemes.property_of_overIso (@QuasiCompact) ((CommGrp.forget _).mapIso e.symm) hs
  exact QuasiCompact.of_pullback_snd G.X.hom f

/-- A torus is separated over its ground field. -/
instance isSeparated [IsTorus G] : IsSeparated G.X.hom := by
  let Ω := AlgebraicClosure K
  let f : Spec (CommRingCat.of Ω) ⟶ Spec (CommRingCat.of K) :=
    Spec.map (CommRingCat.ofHom (algebraMap K Ω))
  have : Surjective f := ⟨fun y => ⟨default, Subsingleton.elim _ y⟩⟩
  obtain ⟨r, hr⟩ := exists_geometric_split (G := G)
  obtain ⟨e⟩ := hr Ω f
  have hs : IsSeparated (GroupSchemes.splitTorus Ω r).X.hom := by
    change IsSeparated
      (Spec.map (CommRingCat.ofHom (algebraMap Ω (GroupSchemes.splitTorusAlgebra Ω r))))
    infer_instance
  have h : IsSeparated (pullback.snd G.X.hom f) :=
    GroupSchemes.property_of_overIso (@IsSeparated) ((CommGrp.forget _).mapIso e.symm) hs
  have : MorphismProperty.DescendsAlong (@IsSeparated : MorphismProperty Scheme.{u})
      (@Surjective ⊓ @Flat ⊓ @QuasiCompact) := IsSeparated.descendsAlong_fpqc
  exact MorphismProperty.of_isPullback_of_descendsAlong
    (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
    (IsPullback.of_hasPullback G.X.hom f).flip
    ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩ h

end AlgebraicGeometry.IsTorus
