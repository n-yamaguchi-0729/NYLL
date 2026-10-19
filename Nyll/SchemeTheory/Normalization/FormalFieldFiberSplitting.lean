/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.RingTheory.Henselian.FormalTensorSplittingOfEmbeddings
import Mathlib.AlgebraicGeometry.Limits

/-! # The actual formal fibre over a finite split residue field

The complete family of residue embeddings constructs the splitting of the
actual field-spectrum pullback. Both projections are computed using the
same simple-root lifts. The coefficient field need not be algebraically
closed, so this applies to the common Laurent field of the tame boundary.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme

private theorem isIso_sigmaSpec_fin (R : Type u) [CommRing R] (n : ℕ) :
    IsIso (sigmaSpec (fun _ : Fin n => CommRingCat.of R)) := by
  let reindex : (∐ fun _ : Fin n => Spec (.of R)) ≅
      (∐ fun _ : ULift.{u} (Fin n) => Spec (.of R)) :=
    Sigma.reindex (Equiv.ulift.symm : Fin n ≃ ULift.{u} (Fin n))
      (fun _ : ULift.{u} (Fin n) => Spec (.of R))
  let coeff : (Fin n → R) ≃+* (ULift.{u} (Fin n) → R) := {
    toFun f j := f j.down
    invFun f j := f ⟨j⟩
    left_inv _ := rfl
    right_inv _ := rfl
    map_mul' _ _ := rfl
    map_add' _ _ := rfl }
  let specCoeff : Spec (.of (ULift.{u} (Fin n) → R)) ≅ Spec (.of (Fin n → R)) :=
    Scheme.Spec.mapIso coeff.toCommRingCatIso.op
  have h : sigmaSpec (fun _ : Fin n => CommRingCat.of R) =
      reindex.hom ≫ sigmaSpec (fun _ : ULift.{u} (Fin n) => CommRingCat.of R) ≫
        specCoeff.hom := by
    apply Sigma.hom_ext
    intro j
    have hι : Sigma.ι (fun _ : Fin n => Spec (.of R)) j ≫ reindex.hom =
        Sigma.ι (fun _ : ULift.{u} (Fin n) => Spec (.of R)) ⟨j⟩ :=
      Sigma.ι_reindex_hom (Equiv.ulift.symm : Fin n ≃ ULift.{u} (Fin n))
        (fun _ : ULift.{u} (Fin n) => Spec (.of R)) j
    have hσ : Sigma.ι (fun _ : ULift.{u} (Fin n) => Spec (.of R)) ⟨j⟩ ≫
        sigmaSpec (fun _ : ULift.{u} (Fin n) => CommRingCat.of R) =
      Spec.map (CommRingCat.ofHom (Pi.evalRingHom (fun _ : ULift.{u} (Fin n) => R) ⟨j⟩)) :=
      ι_sigmaSpec _ _
    calc
      Sigma.ι (fun _ : Fin n => Spec (.of R)) j ≫
          sigmaSpec (fun _ : Fin n => CommRingCat.of R) =
        Spec.map (CommRingCat.ofHom (Pi.evalRingHom (fun _ : Fin n => R) j)) :=
          ι_sigmaSpec _ _
      _ = (Sigma.ι (fun _ : ULift.{u} (Fin n) => Spec (.of R)) ⟨j⟩ ≫
          sigmaSpec (fun _ : ULift.{u} (Fin n) => CommRingCat.of R)) ≫ specCoeff.hom := by
        rw [hσ]
        change Spec.map (CommRingCat.ofHom (Pi.evalRingHom (fun _ : Fin n => R) j)) =
          Spec.map (CommRingCat.ofHom
            (Pi.evalRingHom (fun _ : ULift.{u} (Fin n) => R) ⟨j⟩)) ≫
            Spec.map (CommRingCat.ofHom coeff.toRingHom)
        rw [← Spec.map_comp]
        rfl
      _ = Sigma.ι (fun _ : Fin n => Spec (.of R)) j ≫ reindex.hom ≫
          sigmaSpec (fun _ : ULift.{u} (Fin n) => CommRingCat.of R) ≫ specCoeff.hom := by
        rw [← hι]
        simp only [Category.assoc]
  rw [h]
  infer_instance

/-- The actual base change of a finite separable field is the labelled
coproduct of its constructed formal lifts whenever all residue embeddings
are already present in the coefficient field. -/
theorem exists_formal_field_fiber_coprod_iso
    {E F L : Type u} [Field E] [Field F] [Field L]
    [Algebra E F] [Algebra E L]
    [FiniteDimensional E F] [Algebra.IsSeparable E F]
    (n : ℕ) (hn : Module.finrank E F = n)
    (ι : Fin n → F →ₐ[E] L) (hι : Function.Injective ι)
    (τ : E →+* PowerSeries L)
    (hτ : PowerSeries.constantCoeff.comp τ = algebraMap E L) :
    ∃ d : (∐ fun _ : Fin n => Spec (.of (PowerSeries L))) ≅
        pullback (Spec.map (CommRingCat.ofHom (algebraMap E F)))
          (Spec.map (CommRingCat.ofHom τ)),
      d.hom ≫ pullback.snd
          (Spec.map (CommRingCat.ofHom (algebraMap E F)))
          (Spec.map (CommRingCat.ofHom τ)) =
        Sigma.desc (fun _ : Fin n => 𝟙 (Spec (.of (PowerSeries L)))) ∧
      ∀ j : Fin n,
        Sigma.ι (fun _ : Fin n => Spec (.of (PowerSeries L))) j ≫
          d.hom ≫ pullback.fst
            (Spec.map (CommRingCat.ofHom (algebraMap E F)))
            (Spec.map (CommRingCat.ofHom τ)) =
          Spec.map (CommRingCat.ofHom (PowerSeries.formalEmbeddingLift τ hτ (ι j))) := by
  classical
  let R := PowerSeries L
  have : IsIso (sigmaSpec (fun _ : Fin n => CommRingCat.of R)) :=
    isIso_sigmaSpec_fin R n
  let algR : Algebra E R := τ.toAlgebra
  let _ : Module E R := algR.toModule
  obtain ⟨eAlg, heAlg⟩ :=
    PowerSeries.exists_formalTensorProductEquiv_of_embeddings n hn ι hι τ hτ
  let eSpec : Spec (.of (Fin n → R)) ≅ Spec (.of (R ⊗[E] F)) :=
    Scheme.Spec.mapIso eAlg.toRingEquiv.toCommRingCatIso.op
  let d : (∐ fun _ : Fin n => Spec (.of R)) ≅
      pullback (Spec.map (CommRingCat.ofHom (algebraMap E F)))
        (Spec.map (CommRingCat.ofHom τ)) :=
    asIso (sigmaSpec (fun _ : Fin n => CommRingCat.of R)) ≪≫ eSpec ≪≫
      (pullbackSpecIso E R F).symm ≪≫ pullbackSymmetry _ _
  have heBase : eSpec.hom ≫
      Spec.map (CommRingCat.ofHom (algebraMap R (R ⊗[E] F))) =
      Spec.map (CommRingCat.ofHom (algebraMap R (Fin n → R))) := by
    change Spec.map (CommRingCat.ofHom eAlg.toRingHom) ≫ Spec.map _ = _
    rw [← Spec.map_comp]
    congr 1
    exact CommRingCat.hom_ext (RingHom.ext eAlg.commutes)
  have hσ (j : Fin n) :
      Sigma.ι (fun _ : Fin n => Spec (.of R)) j ≫
        sigmaSpec (fun _ : Fin n => CommRingCat.of R) =
      Spec.map (CommRingCat.ofHom (Pi.evalRingHom (fun _ : Fin n => R) j)) :=
    ι_sigmaSpec _ _
  refine ⟨d, ?_, ?_⟩
  · simp only [d, Iso.trans_hom, Iso.symm_hom, asIso_hom, Category.assoc,
      pullbackSymmetry_hom_comp_snd, pullbackSpecIso_inv_fst']
    rw [heBase]
    apply Sigma.hom_ext
    intro j
    rw [← Category.assoc, hσ, Sigma.ι_comp_desc, ← Spec.map_comp]
    exact Spec.map_id _
  · intro j
    simp only [d, Iso.trans_hom, Iso.symm_hom, asIso_hom, Category.assoc,
      pullbackSymmetry_hom_comp_fst, pullbackSpecIso_inv_snd]
    change Sigma.ι (fun _ : Fin n => Spec (.of R)) j ≫
      sigmaSpec (fun _ : Fin n => CommRingCat.of R) ≫ eSpec.hom ≫
        Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.includeRight : F →ₐ[E] R ⊗[E] F).toRingHom) = _
    rw [← Category.assoc, hσ]
    change Spec.map (CommRingCat.ofHom (Pi.evalRingHom _ j)) ≫
      Spec.map (CommRingCat.ofHom eAlg.toRingHom) ≫
      Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.includeRight : F →ₐ[E] R ⊗[E] F).toRingHom) = _
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro b
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply]
    change eAlg ((1 : R) ⊗ₜ[E] b) j = PowerSeries.formalEmbeddingLift τ hτ (ι j) b
    rw [heAlg, one_mul]

end AlgebraicGeometry.Scheme
