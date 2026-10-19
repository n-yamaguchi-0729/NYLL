/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Affine.FiniteSchemeAlgebra
import Nyll.SchemeTheory.Etale.FiniteStrictLocalGeometricSection
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-!
# Marked sections over arbitrary finite schemes of a strictly local base

The actual coordinate algebra of a finite scheme presents it as the spectrum
of a finite algebra over the original base ring. Transporting the prescribed
geometric points through this presentation extends their étale lifts to a
section of the original scheme. The conclusion retains equality of the
field-valued morphisms and does not require the source of the étale morphism
to be affine.
-/

noncomputable section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Etale

/-- Prescribed lifts of all geometric closed-fiber points through an étale
morphism extend to a section over any finite scheme of a strictly Henselian
local base. The section preserves the actual chosen field-valued maps. -/
theorem exists_section_prescribed_of_isFinite_over_strictlyHenselian
    (R : Type u) [CommRing R] [HenselianLocalRing R]
    [IsSepClosed (IsLocalRing.ResidueField R)]
    {Y W : Scheme.{u}} (q : Y ⟶ Spec (.of R)) [IsFinite q]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (φ : R →+* Ω) [IsLocalHom φ]
    (p : W ⟶ Y) [Etale p]
    (w : {s : Spec (.of Ω) ⟶ Y //
      s ≫ q = Spec.map (CommRingCat.ofHom φ)} → (Spec (.of Ω) ⟶ W))
    (hw : ∀ s, w s ≫ p = s.val) :
    ∃ σ : Y ⟶ W, σ ≫ p = 𝟙 _ ∧ ∀ s, s.val ≫ σ = w s := by
  let B : CommAlgCat.{u} R := SchemeTheory.Affine.FiniteScheme.coordinateAlgebra q
  let e : Y ≅ Spec (.of B) := SchemeTheory.Affine.FiniteScheme.coordinateIso q
  let qB : Spec (.of B) ⟶ Spec (.of R) :=
    Spec.map (CommRingCat.ofHom (algebraMap R B))
  have heq : e.hom ≫ qB = q :=
    SchemeTheory.Affine.FiniteScheme.coordinateIso_toBase q
  have hinv : e.inv ≫ q = qB := by
    calc
      e.inv ≫ q = e.inv ≫ (e.hom ≫ qB) :=
        congrArg (fun h => e.inv ≫ h) heq.symm
      _ = qB := by rw [Iso.inv_hom_id_assoc]
  let pB : W ⟶ Spec (.of B) := p ≫ e.hom
  let I := {s : Spec (.of Ω) ⟶ Y // s ≫ q = Spec.map (CommRingCat.ofHom φ)}
  let IB := {s : Spec (.of Ω) ⟶ Spec (.of B) //
    s ≫ qB = Spec.map (CommRingCat.ofHom φ)}
  let toY : IB → I := fun s => ⟨s.val ≫ e.inv, by
    rw [Category.assoc, hinv]
    exact s.property⟩
  let wB : IB → (Spec (.of Ω) ⟶ W) := fun s => w (toY s)
  have hwB (s : IB) : wB s ≫ pB = s.val := by
    change w (toY s) ≫ (p ≫ e.hom) = s.val
    rw [← Category.assoc, hw]
    change (s.val ≫ e.inv) ≫ e.hom = s.val
    rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  obtain ⟨σB, hσB, hmarked⟩ :=
    exists_section_prescribed_of_finite_over_strictlyHenselian R B φ pB wB hwB
  have hσ : σB ≫ p = e.inv := by
    apply (cancel_mono e.hom).mp
    rw [Category.assoc, Iso.inv_hom_id]
    exact hσB
  refine ⟨e.hom ≫ σB, ?_, ?_⟩
  · rw [Category.assoc, hσ, Iso.hom_inv_id]
  · intro s
    let sB : IB := ⟨s.val ≫ e.hom, by
      rw [Category.assoc, heq]
      exact s.property⟩
    have hpoint : toY sB = s := by
      apply Subtype.ext
      change (s.val ≫ e.hom) ≫ e.inv = s.val
      rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    rw [← Category.assoc]
    exact (hmarked sB).trans (congrArg w hpoint)

end AlgebraicGeometry.Etale
