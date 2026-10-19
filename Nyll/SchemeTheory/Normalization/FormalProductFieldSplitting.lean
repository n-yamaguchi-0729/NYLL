/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.RingTheory.Henselian.FormalTensorSplittingOfEmbeddings
import Mathlib.RingTheory.TensorProduct.Pi
import Mathlib.AlgebraicGeometry.Limits

/-! # Simultaneous formal splitting of the boundary field factors

Tensor product commutes with the finite product of actual completed boundary
fields. Splitting each factor by its constructed formal lifts therefore gives
the labelled splitting of their entire product over the same deformed base.
Both spectrum projections are retained, so a previously constructed Cartier
block can be transported through this isomorphism without assuming its tuple
ideal or its divisor-sum formula.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace PowerSeries

private def flattenPiAlgEquiv {R : Type*} [CommSemiring R]
    {I : Type*} (n : I → ℕ) :
    (∀ i, Fin (n i) → R) ≃ₐ[R] ((Σ i, Fin (n i)) → R) where
  toFun f j := f j.1 j.2
  invFun f i j := f ⟨i, j⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

/-- The simultaneous formal splitting of a finite product of separable
fields, labelled by their actual finite families of residue embeddings. -/
theorem exists_formalTensorProductPiEquiv_of_embeddings
    {E L : Type u} [Field E] [Field L] [Algebra E L]
    {I : Type u} [Finite I] (F : I → Type u)
    [∀ i, Field (F i)] [∀ i, Algebra E (F i)]
    [∀ i, FiniteDimensional E (F i)] [∀ i, Algebra.IsSeparable E (F i)]
    (n : I → ℕ) (hn : ∀ i, Module.finrank E (F i) = n i)
    (ι : ∀ i, Fin (n i) → F i →ₐ[E] L) (hι : ∀ i, Function.Injective (ι i))
    (τ : E →+* PowerSeries L)
    (hτ : constantCoeff.comp τ = algebraMap E L) :
    let algPS : Algebra E (PowerSeries L) := τ.toAlgebra
    let _ : Module E (PowerSeries L) := algPS.toModule
    ∃ split : (PowerSeries L ⊗[E] (∀ i, F i)) ≃ₐ[PowerSeries L]
        ((Σ i, Fin (n i)) → PowerSeries L),
      ∀ (a : PowerSeries L) (b : ∀ i, F i) (i : I) (j : Fin (n i)),
        split (a ⊗ₜ[E] b) ⟨i, j⟩ = a * formalEmbeddingLift τ hτ (ι i j) (b i) := by
  classical
  let _ : Fintype I := Fintype.ofFinite I
  intro algPS modPS
  have hlocal (i : I) :=
    exists_formalTensorProductEquiv_of_embeddings (n i) (hn i) (ι i) (hι i) τ hτ
  choose localSplit hlocalSplit using hlocal
  let split :=
    (Algebra.TensorProduct.piRight E (PowerSeries L) (PowerSeries L) F).trans
      ((AlgEquiv.piCongrRight localSplit).trans (flattenPiAlgEquiv n))
  refine ⟨split, ?_⟩
  intro a b i j
  change localSplit i (a ⊗ₜ[E] b i) j = _
  exact hlocalSplit i a (b i) j

end PowerSeries

namespace AlgebraicGeometry.Scheme

/-- The full formal base change of the product of boundary fields is the
coproduct of the actual formal lifts, with both projections computed. -/
theorem exists_formal_product_field_fiber_coprod_iso
    {E L : Type u} [Field E] [Field L] [Algebra E L]
    {I : Type u} [Finite I] (F : I → Type u)
    [∀ i, Field (F i)] [∀ i, Algebra E (F i)]
    [∀ i, FiniteDimensional E (F i)] [∀ i, Algebra.IsSeparable E (F i)]
    (n : I → ℕ) (hn : ∀ i, Module.finrank E (F i) = n i)
    (ι : ∀ i, Fin (n i) → F i →ₐ[E] L) (hι : ∀ i, Function.Injective (ι i))
    (τ : E →+* PowerSeries L)
    (hτ : PowerSeries.constantCoeff.comp τ = algebraMap E L) :
    ∃ d : (∐ fun _ : Σ i, Fin (n i) => Spec (.of (PowerSeries L))) ≅
        pullback (Spec.map (CommRingCat.ofHom (algebraMap E (∀ i, F i))))
          (Spec.map (CommRingCat.ofHom τ)),
      d.hom ≫ pullback.snd
          (Spec.map (CommRingCat.ofHom (algebraMap E (∀ i, F i))))
          (Spec.map (CommRingCat.ofHom τ)) =
        Sigma.desc (fun _ : Σ i, Fin (n i) => 𝟙 (Spec (.of (PowerSeries L)))) ∧
      ∀ (i : I) (j : Fin (n i)),
        Sigma.ι (fun _ : Σ i, Fin (n i) => Spec (.of (PowerSeries L))) ⟨i, j⟩ ≫
          d.hom ≫ pullback.fst
            (Spec.map (CommRingCat.ofHom (algebraMap E (∀ i, F i))))
            (Spec.map (CommRingCat.ofHom τ)) =
          Spec.map (CommRingCat.ofHom
            ((PowerSeries.formalEmbeddingLift τ hτ (ι i j)).comp (Pi.evalRingHom F i))) := by
  classical
  let _ : Fintype I := Fintype.ofFinite I
  let R := PowerSeries L
  let algR : Algebra E R := τ.toAlgebra
  let _ : Module E R := algR.toModule
  obtain ⟨eAlg, heAlg⟩ :=
    PowerSeries.exists_formalTensorProductPiEquiv_of_embeddings F n hn ι hι τ hτ
  let eSpec : Spec (.of ((Σ i, Fin (n i)) → R)) ≅ Spec (.of (R ⊗[E] (∀ i, F i))) :=
    Scheme.Spec.mapIso eAlg.toRingEquiv.toCommRingCatIso.op
  let d : (∐ fun _ : Σ i, Fin (n i) => Spec (.of R)) ≅
      pullback (Spec.map (CommRingCat.ofHom (algebraMap E (∀ i, F i))))
        (Spec.map (CommRingCat.ofHom τ)) :=
    asIso (sigmaSpec (fun _ : Σ i, Fin (n i) => CommRingCat.of R)) ≪≫ eSpec ≪≫
      (pullbackSpecIso E R (∀ i, F i)).symm ≪≫ pullbackSymmetry _ _
  have heBase : eSpec.hom ≫
      Spec.map (CommRingCat.ofHom (algebraMap R (R ⊗[E] (∀ i, F i)))) =
      Spec.map (CommRingCat.ofHom (algebraMap R ((Σ i, Fin (n i)) → R))) := by
    change Spec.map (CommRingCat.ofHom eAlg.toRingHom) ≫ Spec.map _ = _
    rw [← Spec.map_comp]
    congr 1
    exact CommRingCat.hom_ext (RingHom.ext eAlg.commutes)
  have hσ (j : Σ i, Fin (n i)) :
      Sigma.ι (fun _ : Σ i, Fin (n i) => Spec (.of R)) j ≫
        sigmaSpec (fun _ : Σ i, Fin (n i) => CommRingCat.of R) =
      Spec.map (CommRingCat.ofHom (Pi.evalRingHom (fun _ : Σ i, Fin (n i) => R) j)) :=
    ι_sigmaSpec _ _
  refine ⟨d, ?_, ?_⟩
  · simp only [d, Iso.trans_hom, Iso.symm_hom, asIso_hom, Category.assoc,
      pullbackSymmetry_hom_comp_snd, pullbackSpecIso_inv_fst']
    rw [heBase]
    apply Sigma.hom_ext
    intro j
    rw [← Category.assoc, hσ, Sigma.ι_comp_desc, ← Spec.map_comp]
    exact Spec.map_id _
  · intro i j
    simp only [d, Iso.trans_hom, Iso.symm_hom, asIso_hom, Category.assoc,
      pullbackSymmetry_hom_comp_fst, pullbackSpecIso_inv_snd]
    change Sigma.ι (fun _ : Σ i, Fin (n i) => Spec (.of R)) ⟨i, j⟩ ≫
      sigmaSpec (fun _ : Σ i, Fin (n i) => CommRingCat.of R) ≫ eSpec.hom ≫
        Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.includeRight :
            (∀ i, F i) →ₐ[E] R ⊗[E] (∀ i, F i)).toRingHom) = _
    rw [← Category.assoc, hσ]
    change Spec.map (CommRingCat.ofHom (Pi.evalRingHom _ ⟨i, j⟩)) ≫
      Spec.map (CommRingCat.ofHom eAlg.toRingHom) ≫
      Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.includeRight :
            (∀ i, F i) →ₐ[E] R ⊗[E] (∀ i, F i)).toRingHom) = _
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro b
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply]
    change eAlg ((1 : R) ⊗ₜ[E] b) ⟨i, j⟩ =
      PowerSeries.formalEmbeddingLift τ hτ (ι i j) (b i)
    rw [heAlg, one_mul]

end AlgebraicGeometry.Scheme
