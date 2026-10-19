/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Algebra.Algebra.Basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.Ideal.Maximal
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.LocalRing.RingHom.Basic
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.TensorProduct.Nontrivial

/-!
# Matching the special geometric field in a specialization diagram

Two field extensions of the same field embed compatibly into an algebraically
closed field: their tensor product is nontrivial, so a maximal ideal gives an
actual field quotient, whose algebraic closure supplies the common field.

Applied to the native residue-field map of a local homomorphism `A → B` and
the specified closed geometric point `A → Ω`, this construction preserves
that geometric point after a field extension. Both the residue-field square
and the square of maps from the original local ring commute.

This supplies the common special field in the proof of Stacks Project,
Lemma 58.16.4, https://stacks.math.columbia.edu/tag/0C0N. It does not use a
chosen compatibility as an additional hypothesis.
-/

noncomputable section

open scoped TensorProduct

namespace EtaleFundamentalGroups.StrictHenselian

universe u v w

/-- Any two field extensions have a common algebraically closed overfield
with their specified embeddings of the base field preserved. The field is
constructed from a maximal quotient of the actual tensor product. -/
theorem exists_algebraicallyClosedFieldSquare
    {k : Type u} {K : Type v} {L : Type w} [Field k] [Field K] [Field L]
    (α : k →+* K) (β : k →+* L) :
    ∃ (Ω : Type (max v w)) (_ : Field Ω) (_ : IsAlgClosed Ω)
      (i : K →+* Ω) (j : L →+* Ω), i.comp α = j.comp β := by
  let : Algebra k K := α.toAlgebra
  let : Algebra k L := β.toAlgebra
  let T : Type (max v w) := K ⊗[k] L
  have : Nontrivial T :=
    Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_isDomain
      k K L α.injective β.injective
  obtain ⟨m, hm⟩ := Ideal.exists_maximal T
  let F : Type (max v w) := T ⧸ m
  let : Field F := Ideal.Quotient.field m
  let Ω : Type (max v w) := AlgebraicClosure F
  let q : T →+* Ω := (algebraMap F Ω).comp (Ideal.Quotient.mk m)
  let l : K →+* T := Algebra.TensorProduct.includeLeftRingHom
  let r : L →+* T := Algebra.TensorProduct.includeRight.toRingHom
  refine ⟨Ω, inferInstance, inferInstance, q.comp l, q.comp r, ?_⟩
  rw [RingHom.comp_assoc, RingHom.comp_assoc]
  exact congrArg (fun h : k →+* T => q.comp h)
    (Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap
      (R := k) (A := K) (B := L))

/-- A local homomorphism and an independently specified closed geometric
point fit into a common algebraically closed residue-field square. The
second equality retains the original map `s`, before passing to residues. -/
theorem exists_algebraicallyClosedResidueFieldSquare
    {A : Type u} {B : Type v} {Ω : Type w}
    [CommRing A] [IsLocalRing A] [CommRing B] [IsLocalRing B] [Field Ω]
    (f : A →+* B) [IsLocalHom f] (s : A →+* Ω) [IsLocalHom s] :
    ∃ (k : Type (max v w)) (_ : Field k) (_ : IsAlgClosed k)
      (i : Ω →+* k) (j : IsLocalRing.ResidueField B →+* k),
      IsLocalHom (j.comp (IsLocalRing.residue B)) ∧
      j.comp (IsLocalRing.ResidueField.map f) =
        i.comp (IsLocalRing.ResidueField.lift s) ∧
      (j.comp (IsLocalRing.residue B)).comp f = i.comp s := by
  obtain ⟨k, hField, hClosed, j, i, hresidue⟩ :=
    exists_algebraicallyClosedFieldSquare
      (IsLocalRing.ResidueField.map f) (IsLocalRing.ResidueField.lift s)
  refine ⟨k, hField, hClosed, i, j, RingHom.isLocalHom_comp _ _, hresidue, ?_⟩
  rw [RingHom.comp_assoc, ← IsLocalRing.ResidueField.map_comp_residue f,
    ← RingHom.comp_assoc, hresidue, RingHom.comp_assoc,
    IsLocalRing.ResidueField.lift_comp_residue s]

end EtaleFundamentalGroups.StrictHenselian
