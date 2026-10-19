/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Morphisms.GeometricallyIrreducibleOverAlgebraicallyClosed
import Nyll.SchemeTheory.Morphisms.PurelyInseparableFieldExtension
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Geometric irreducibility over a separably closed field

An arbitrary irreducible scheme over a separably closed field is geometrically
irreducible. This is Stacks Project, Lemma 33.8.3, Tag `020J`.

The purely inseparable algebraic-closure projection preserves the underlying
topological space. Geometric irreducibility over that algebraically closed
field then descends to every field extension through an actual surjective
base-change projection. No finite type assumption is needed.
-/

noncomputable section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

/-- An irreducible scheme over a separably closed field is geometrically
irreducible, without any finite type hypothesis (Stacks Project, Tag `020J`). -/
theorem GeometricallyIrreducible.of_irreducibleSpace_of_isSepClosed
    {k : Type u} [Field k] [IsSepClosed k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IrreducibleSpace X] : GeometricallyIrreducible f := by
  let A := AlgebraicClosure k
  let φA : Spec (.of A) ⟶ Spec (.of k) :=
    Spec.map (CommRingCat.ofHom (algebraMap k A))
  have : IrreducibleSpace ↥(pullback φA f) :=
    (purelyInseparableConstantFieldHomeomorph k A X f).irreducibleSpace_iff.mpr
      inferInstance
  have : IrreducibleSpace ↥(pullback f φA) :=
    (pullbackSymmetry f φA).hom.homeomorph.irreducibleSpace_iff.mpr inferInstance
  have : GeometricallyIrreducible (pullback.snd f φA) :=
    GeometricallyIrreducible.of_irreducibleSpace_of_isAlgClosed (pullback.snd f φA)
  refine ⟨(geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms
    (P := fun Y : Scheme.{u} ↦ IrreducibleSpace Y)).mpr ?_⟩
  intro K _ _
  let Ω := AlgebraicClosure K
  let j : A →ₐ[k] Ω := IsAlgClosed.lift
  let φK : Spec (.of K) ⟶ Spec (.of k) :=
    Spec.map (CommRingCat.ofHom (algebraMap k K))
  let φΩK : Spec (.of Ω) ⟶ Spec (.of K) :=
    Spec.map (CommRingCat.ofHom (algebraMap K Ω))
  let φΩA : Spec (.of Ω) ⟶ Spec (.of A) :=
    Spec.map (CommRingCat.ofHom j.toRingHom)
  have hcomp : φΩA ≫ φA = φΩK ≫ φK := by
    change Spec.map (CommRingCat.ofHom j.toRingHom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap k A)) =
      Spec.map (CommRingCat.ofHom (algebraMap K Ω)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap k K))
    rw [← Spec.map_comp, ← Spec.map_comp]
    apply congrArg Spec.map
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro x
    exact j.commutes x
  have : IrreducibleSpace ↥(pullback (pullback.snd f φA) φΩA) :=
    pullback_of_geometrically
      (GeometricallyIrreducible.geometrically_irreducibleSpace
        (f := pullback.snd f φA)) Ω φΩA
  let e : pullback (pullback.snd f φA) φΩA ≅
      pullback (pullback.snd f φK) φΩK :=
    pullbackLeftPullbackSndIso f φA φΩA ≪≫ pullback.congrHom rfl hcomp ≪≫
      (pullbackLeftPullbackSndIso f φK φΩK).symm
  have : IrreducibleSpace ↥(pullback (pullback.snd f φK) φΩK) :=
    e.hom.homeomorph.irreducibleSpace_iff.mp inferInstance
  have : Surjective φΩK := ⟨fun y ↦
    ⟨Classical.choice (inferInstance : Nonempty (Spec (.of Ω))), Subsingleton.elim _ _⟩⟩
  exact (pullback.fst (pullback.snd f φK) φΩK).surjective.irreducibleSpace
    (pullback.fst (pullback.snd f φK) φΩK).continuous

end AlgebraicGeometry
