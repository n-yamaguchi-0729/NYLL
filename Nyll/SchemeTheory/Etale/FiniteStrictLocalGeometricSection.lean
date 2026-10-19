/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Etale.HenselianLocalGeometricSection
import Nyll.SchemeTheory.RingTheory.Henselian.CompleteOrthogonalIdempotentsLocalRingQuotient
import Nyll.SchemeTheory.RingTheory.Henselian.FiniteLocalGeometricPoints
import Nyll.SchemeTheory.RingTheory.Henselian.ModuleFinite
import Mathlib.AlgebraicGeometry.Cover.Open
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap

/-!
# Sections preserving every geometric point over a strictly local base

A finite algebra over a strictly Henselian local ring is a finite product
of strictly local rings. Each factor has exactly one point over a specified
algebraically closed geometric closed point of the base. Prescribed lifts
of these points into an étale scheme therefore extend to a global section,
with equality of the specified field-valued morphisms.

This is the marked geometric step in the finite direct-image stalk formula,
Stacks Project 59.55.2(1).
-/

noncomputable section

universe u

open CategoryTheory Limits HenselianLocalRing

namespace AlgebraicGeometry.Etale

/-- Prescribed lifts of every geometric closed-fiber point through an étale
morphism extend simultaneously to an actual section over a finite algebra
of a strictly Henselian local ring. The equalities retain the chosen field
maps, not just their underlying topological points. -/
theorem exists_section_prescribed_of_finite_over_strictlyHenselian
    (R B : Type u) [CommRing R] [HenselianLocalRing R]
    [IsSepClosed (IsLocalRing.ResidueField R)]
    [CommRing B] [Algebra R B] [Module.Finite R B]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (φ : R →+* Ω) [IsLocalHom φ]
    {W : Scheme.{u}} (p : W ⟶ Spec (.of B)) [Etale p]
    (w : {s : Spec (.of Ω) ⟶ Spec (.of B) //
      s ≫ Spec.map (CommRingCat.ofHom (algebraMap R B)) = Spec.map (CommRingCat.ofHom φ)} →
      (Spec (.of Ω) ⟶ W))
    (hw : ∀ s, w s ≫ p = s.val) :
    ∃ σ : Spec (.of B) ⟶ W, σ ≫ p = 𝟙 _ ∧ ∀ s, s.val ≫ σ = w s := by
  classical
  let q : Spec (.of B) ⟶ Spec (.of R) :=
    Spec.map (CommRingCat.ofHom (algebraMap R B))
  let t : Spec (.of Ω) ⟶ Spec (.of R) := Spec.map (CommRingCat.ofHom φ)
  let I := {s : Spec (.of Ω) ⟶ Spec (.of B) // s ≫ q = t}
  obtain ⟨hfinite, e, he, _, _, hlocal⟩ :=
    exists_completeOrthogonalIdempotents_forall_isLocalRing_quotient_of_moduleFinite
      (R := R) (S := B)
  let : Fintype (MaximalSpectrum B) := hfinite
  let C (m : MaximalSpectrum B) := B ⧸ Ideal.span {1 - e m}
  have (m : MaximalSpectrum B) : IsLocalRing (C m) := hlocal m
  have hpoints (m : MaximalSpectrum B) :
      ∃ ψ : C m →+* Ω, IsLocalHom ψ ∧ ψ.comp (algebraMap R (C m)) = φ ∧
        ∀ θ : C m →+* Ω, θ.comp (algebraMap R (C m)) = φ → θ = ψ :=
    SchemeTheory.existsUnique_localPoint_of_finite_local R (C m) φ
  choose ψ hψ using hpoints
  let j (m : MaximalSpectrum B) : Spec (.of (C m)) ⟶ Spec (.of B) :=
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {1 - e m})))
  let a (m : MaximalSpectrum B) : Spec (.of Ω) ⟶ Spec (.of (C m)) :=
    Spec.map (CommRingCat.ofHom (ψ m))
  have hjq (m : MaximalSpectrum B) :
      j m ≫ q = Spec.map (CommRingCat.ofHom (algebraMap R (C m))) := by
    rw [← Spec.map_comp]
    rfl
  have haq (m : MaximalSpectrum B) : (a m ≫ j m) ≫ q = t := by
    rw [Category.assoc, hjq, ← Spec.map_comp]
    exact congrArg (fun h : R →+* Ω => Spec.map (CommRingCat.ofHom h)) (hψ m).2.1
  let s (m : MaximalSpectrum B) : I := ⟨a m ≫ j m, haq m⟩
  have hsections (m : MaximalSpectrum B) :
      ∃ σ : Spec (.of (C m)) ⟶ W, σ ≫ p = j m ∧ a m ≫ σ = w (s m) := by
    have : HenselianLocalRing (C m) :=
      HenselianLocalRing.of_moduleFinite_of_isLocalRing (R := R)
    have : IsSepClosed (IsLocalRing.ResidueField (C m)) :=
      SchemeTheory.isSepClosed_residueField_of_finite_local R (C m)
    have : IsLocalHom (ψ m) := (hψ m).1
    have ha : a m default = IsLocalRing.closedPoint (C m) := by
      change Spec.map (CommRingCat.ofHom (ψ m)) default = _
      exact (congrArg (Spec.map (CommRingCat.ofHom (ψ m)))
        (Subsingleton.elim _ (IsLocalRing.closedPoint Ω))).trans Spec_closedPoint
    let b : Spec (.of Ω) ⟶ pullback p (j m) :=
      pullback.lift (w (s m)) (a m) (hw (s m))
    obtain ⟨σ, hσ, _⟩ := existsUnique_section_of_closedFieldPoint (C m)
      (pullback.snd p (j m)) (a m) ha b (pullback.lift_snd _ _ _)
    refine ⟨σ ≫ pullback.fst p (j m), ?_, ?_⟩
    · rw [Category.assoc, pullback.condition, ← Category.assoc, hσ.1, Category.id_comp]
    · rw [← Category.assoc, hσ.2]
      exact pullback.lift_fst _ _ _
  choose σ₀ hσ₀ hmarked using hsections
  let c : B →+* (∀ m, C m) :=
    RingHom.pi fun m => Ideal.Quotient.mk (Ideal.span {1 - e m})
  let E : B ≃+* (∀ m, C m) := RingEquiv.ofBijective c he.bijective_pi
  let d : (∐ fun m => Spec (.of (C m))) ⟶ Spec (.of B) :=
    sigmaSpec (fun m => CommRingCat.of (C m)) ≫ Spec.map (CommRingCat.ofHom c)
  have : IsIso (Spec.map (CommRingCat.ofHom c)) :=
    inferInstanceAs (IsIso (Scheme.Spec.mapIso E.toCommRingCatIso.op).hom)
  have : IsIso d := inferInstance
  have hd (m : MaximalSpectrum B) :
      Sigma.ι (fun m => Spec (.of (C m))) m ≫ d = j m := by
    dsimp only [d]
    rw [← Category.assoc, ι_sigmaSpec, ← Spec.map_comp]
    rfl
  have hσp : Sigma.desc σ₀ ≫ p = d := by
    apply Sigma.hom_ext
    intro m
    rw [← Category.assoc, Sigma.ι_comp_desc, hσ₀, hd]
  let σ : Spec (.of B) ⟶ W := inv d ≫ Sigma.desc σ₀
  have hrestr (m : MaximalSpectrum B) : j m ≫ σ = σ₀ m := by
    dsimp only [σ]
    rw [← hd, Category.assoc, IsIso.hom_inv_id_assoc, Sigma.ι_comp_desc]
  refine ⟨σ, ?_, ?_⟩
  · dsimp only [σ]
    rw [Category.assoc, hσp, IsIso.inv_hom_id]
  · intro z
    let z' : Spec (.of Ω) ⟶ ∐ fun m => Spec (.of (C m)) := z.val ≫ inv d
    obtain ⟨m, x, hx⟩ := (sigmaOpenCover (fun m => Spec (.of (C m)))).exists_eq (z' default)
    change MaximalSpectrum B at m
    let ι : Spec (.of (C m)) ⟶ ∐ fun m => Spec (.of (C m)) :=
      Sigma.ι (fun m => Spec (.of (C m))) m
    have hrange : Set.range z' ⊆ Set.range ι := by
      rintro _ ⟨x', rfl⟩
      rw [Subsingleton.elim x' default]
      exact ⟨x, hx⟩
    let l : Spec (.of Ω) ⟶ Spec (.of (C m)) := IsOpenImmersion.lift ι z' hrange
    have hl : l ≫ ι = z' := IsOpenImmersion.lift_fac ι z' hrange
    have hlj : l ≫ j m = z.val := by
      calc
        l ≫ j m = l ≫ (ι ≫ d) := congrArg (fun h => l ≫ h) (hd m).symm
        _ = (l ≫ ι) ≫ d := (Category.assoc _ _ _).symm
        _ = z' ≫ d := congrArg (fun h => h ≫ d) hl
        _ = z.val := by
          dsimp only [z']
          rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
    obtain ⟨θ, hθ⟩ := Spec.map_surjective l
    have hθbase : CommRingCat.ofHom (algebraMap R (C m)) ≫ θ = CommRingCat.ofHom φ := by
      apply Spec.map_injective
      rw [Spec.map_comp, hθ, ← hjq, ← Category.assoc, hlj]
      exact z.property
    have hθeq : θ.hom = ψ m :=
      (hψ m).2.2 θ.hom (congrArg CommRingCat.Hom.hom hθbase)
    have hla : l = a m := hθ.symm.trans
      (congrArg (fun h : C m →+* Ω => Spec.map (CommRingCat.ofHom h)) hθeq)
    have hz : z = s m := Subtype.ext
      (hlj.symm.trans (congrArg (fun h => h ≫ j m) hla))
    rw [hz]
    change (a m ≫ j m) ≫ σ = w (s m)
    rw [Category.assoc, hrestr]
    exact hmarked m

end AlgebraicGeometry.Etale
